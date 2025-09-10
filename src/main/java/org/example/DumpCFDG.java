package org.example;


import soot.*;
import soot.options.Options;
import soot.toolkits.graph.BriefUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.toolkits.scalar.LocalDefs;
import soot.toolkits.scalar.LocalUses;
import soot.toolkits.scalar.SimpleLocalDefs;
import soot.toolkits.scalar.SimpleLocalUses;
import soot.toolkits.scalar.UnitValueBoxPair;
import soot.tagkit.LineNumberTag;
import soot.tagkit.Tag;
import soot.util.dot.DotGraph;
import soot.util.dot.DotGraphEdge;
import soot.util.dot.DotGraphNode;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

/**
 * 语句级 CFG/DFG 导出器（Soot-only，按方法各自导出）
 *
 * 用法（推荐）：
 *   mvn -q -DskipTests package
 *   # Linux/macOS:
 *   JAVA_CP="target/test-classes:target/classes"
 *   java -jar target/soot-cfg-tool-1.0.0-shaded.jar \
 *     --cp "$JAVA_CP" \
 *     --class "com.example.YourTestClass" \
 *     --src-file "src/test/java/com/example/YourTestClass.java" \
 *     --method-prefix "" \
 *     --out "."
 *
 *   # Windows:
 *   set JAVA_CP=target\test-classes;target\classes
 *   java -jar target\soot-cfg-tool-1.0.0-shaded.jar ^
 *     --cp "%JAVA_CP%" ^
 *     --class "com.example.YourTestClass" ^
 *     --src-file "src\test\java\com\example\YourTestClass.java" ^
 *     --method-prefix "" ^
 *     --out "."
 *
 * 说明：
 *  - --cp：Soot 的类路径（必须能找到 .class），可包含多个目录/jar（用系统路径分隔符拼接）。
 *  - --class：要分析的类的 FQN（形如 com.example.FooTest）。
 *  - --src-file：该类对应的 .java 源文件（可用于切片文本；若缺省则节点 text 用行号占位）。
 *  - --method-prefix：只导出以此前缀开头的方法（为空则全部方法）。
 *  - --out：输出根目录（默认 .），每个方法一个子目录。
 *
 * 输出（每个方法一个目录）：
 *   out/<Class#method@line>/nodes.jsonl
 *   out/<Class#method@line>/cfg_edges.jsonl
 *   out/<Class#method@line>/dfg_edges.jsonl
 *   out/<Class#method@line>/graph.dot
 */
public class DumpCFDG {

    // ======== 语句节点模型 ========
    static final class StmtNode {
        final int stmtId;         // 1..N
        final int startLine;      // 行区间（尽力取 SourceLnPosTag，否则单行）
        final int endLine;
        final String text;        // 源码切片（若 --src-file 可读）
        StmtNode(int id, int s, int e, String t) { stmtId = id; startLine = s; endLine = e; text = t; }
    }

    public static void main(String[] args) {
        // ======== 参数 ========
        String cp = getArg(args, "--cp", buildDefaultCP(""));
        String onlyClass = getArg(args, "--class", "");
        String srcFile = getArg(args, "--src-file", "");
        String methodPrefix = getArg(args, "--method-prefix", "");
        String outRoot = getArg(args, "--out", ".");

        if (onlyClass.isEmpty()) {
            System.err.println("请提供 --class <FQN>，例如 --class com.example.YourTestClass");
            System.exit(2);
        }

        // 解析 process_dir（从 cp 中挑出存在的目录）
        List<String> processDirs = new ArrayList<>();
        for (String seg : cp.split(File.pathSeparator))  {
            if (seg == null || seg.trim().isEmpty()) continue;
            Path p = Paths.get(seg);
            if (Files.isDirectory(p)) processDirs.add(seg);
        }
        if (processDirs.isEmpty()) {
            // 至少要有一个目录供 Soot 处理，否则它不会遍历任何类
            // 用户也可以只给 --cp=...jar，但仍需 loadClassAndSupport + setApplicationClass
            // 我们容忍为空，靠后续 loadClassAndSupport 强制加载
        }

        // ======== Soot 配置 ========
        G.reset();
        Options.v().set_prepend_classpath(true);
        Options.v().set_soot_classpath(cp);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_whole_program(false);
        Options.v().set_keep_line_number(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().setPhaseOption("jb", "use-original-names:true");
        if (!processDirs.isEmpty()) {
            Options.v().set_process_dir(processDirs);
        }

        // 加载目标类
        Scene.v().loadNecessaryClasses();
        SootClass sc = Scene.v().loadClassAndSupport(onlyClass);
        sc.setApplicationClass();

        // 把源码（若提供）预加载
        final String srcText = srcFile.isEmpty() ? null : safeReadAll(srcFile);

        // ======== Transformer：每个方法导出一套产物 ========
        PackManager.v().getPack("jtp").add(new Transform("jtp.dumpcfdg", new BodyTransformer() {
            @Override
            protected void internalTransform(Body body, String phase, Map<String, String> opts) {
                SootMethod m = body.getMethod();
                if (!methodPrefix.isEmpty() && !m.getName().startsWith(methodPrefix)) return;

                UnitGraph ug = new BriefUnitGraph(body);

                // 1) 收集 Unit 的行区间 [start..end]，并合并重叠区间 → 语句段
                List<int[]> ranges = new ArrayList<>();
                for (Unit u : body.getUnits()) {
                    int[] rg = tryGetLineRange(u);
                    if (rg != null && rg[0] > 0 && rg[1] >= rg[0]) ranges.add(rg);
                }
                if (ranges.isEmpty()) {
                    System.err.println("[WARN] 方法无行号信息，跳过：" + m.getSignature());
                    return;
                }
                ranges.sort(Comparator.<int[]>comparingInt(a -> a[0]).thenComparingInt(a -> a[1]));
                List<int[]> merged = new ArrayList<>();
                for (int[] r : ranges) {
                    if (merged.isEmpty()) {
                        merged.add(r);
                    } else {
                        int[] last = merged.get(merged.size() - 1);
                        if (r[0] <= last[1] + 0) { // 重叠或相邻就合并
                            last[1] = Math.max(last[1], r[1]);
                        } else {
                            merged.add(r);
                        }
                    }
                }

                // 2) 生成语句节点（1..N）并建立行→stmtId 的快速映射
                List<StmtNode> stmtNodes = new ArrayList<>();
                int sid = 1;
                for (int[] seg : merged) {
                    String t = (srcText == null) ? ("L" + seg[0] + ".." + seg[1]) : slice(srcText, seg[0], seg[1]);
                    stmtNodes.add(new StmtNode(sid++, seg[0], seg[1], t));
                }
                int maxLine = merged.get(merged.size() - 1)[1];
                int[] line2stmt = new int[Math.max(maxLine + 5, 1024)];
                Arrays.fill(line2stmt, -1);
                for (StmtNode n : stmtNodes) {
                    for (int L = n.startLine; L <= n.endLine && L < line2stmt.length; L++) {
                        line2stmt[L] = n.stmtId;
                    }
                }

                // 3) Unit → 语句节点映射（取 Unit 起始行所在的 stmtId）
                Map<Unit, Integer> u2s = new HashMap<>();
                for (Unit u : body.getUnits()) {
                    int[] rg = tryGetLineRange(u);
                    if (rg == null) continue;
                    int L = Math.max(0, Math.min(rg[0], line2stmt.length - 1));
                    int sId = (L >= 0 && L < line2stmt.length) ? line2stmt[L] : -1;
                    if (sId > 0) u2s.put(u, sId);
                }

                if (u2s.isEmpty()) {
                    System.err.println("[WARN] Unit 无法映射到语句，跳过：" + m.getSignature());
                    return;
                }

                // 4) 方法级输出目录
                String methodKey = makeMethodKey(m);
                Path methodDir = Paths.get(outRoot).resolve(safe(methodKey));
                try { Files.createDirectories(methodDir); } catch (IOException ignored) {}

                // 5) 导出 nodes.jsonl（语句节点）
                Path nodesPath = methodDir.resolve("nodes.jsonl");
                try (BufferedWriter w = Files.newBufferedWriter(nodesPath, StandardCharsets.UTF_8)) {
                    for (StmtNode n : stmtNodes) {
                        String js = String.format(Locale.ROOT,
                                "{\"stmt_id\":%d,\"file\":\"%s\",\"start\":[%d,1],\"end\":[%d,100000],\"text\":\"%s\"}\n",
                                n.stmtId, escapeJson(srcFile), n.startLine, n.endLine, escapeJson(n.text));
                        w.write(js);
                    }
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }

                // 6) 语句级 CFG
                Path cfgPath = methodDir.resolve("cfg_edges.jsonl");
                Set<String> cfgSeen = new LinkedHashSet<>();
                try (BufferedWriter w = Files.newBufferedWriter(cfgPath, StandardCharsets.UTF_8)) {
                    for (Unit u : ug) {
                        Integer su = u2s.get(u);
                        if (su == null) continue;
                        for (Unit v : ug.getSuccsOf(u)) {
                            Integer sv = u2s.get(v);
                            if (sv == null || su.equals(sv)) continue;
                            String k = su + "->" + sv;
                            if (cfgSeen.add(k)) {
                                w.write(String.format(Locale.ROOT,
                                        "{\"src\":%d,\"dst\":%d,\"type\":\"cfg\"}\n", su, sv));
                            }
                        }
                    }
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }

                // 7) 语句级 DFG（Def→Use）
                Path dfgPath = methodDir.resolve("dfg_edges.jsonl");
                Set<String> dfgSeen = new LinkedHashSet<>();
                try (BufferedWriter w = Files.newBufferedWriter(dfgPath, StandardCharsets.UTF_8)) {
                    LocalDefs ldefs = new SimpleLocalDefs(ug);
                    LocalUses luses = new SimpleLocalUses(ug, ldefs);
                    for (Unit defU : body.getUnits()) {
                        Integer sd = u2s.get(defU);
                        if (sd == null) continue;
                        List<UnitValueBoxPair> uses = luses.getUsesOf(defU);
                        if (uses == null) continue;
                        for (UnitValueBoxPair uvp : uses) {
                            Unit useU = uvp.getUnit();
                            Integer su = u2s.get(useU);
                            if (su == null || sd.equals(su)) continue;
                            String varName = tryGetLocalName(uvp);
                            String key = sd + "->" + su + ":" + (varName == null ? "" : varName);
                            if (dfgSeen.add(key)) {
                                w.write(String.format(Locale.ROOT,
                                        "{\"src\":%d,\"dst\":%d,\"type\":\"dfg\",\"var\":\"%s\"}\n",
                                        sd, su, escapeJson(varName == null ? "" : varName)));
                            }
                        }
                    }
                } catch (IOException e) {
                    throw new RuntimeException(e);
                }

                // 8) 画语句级 graph.dot（CFG 实线 / DFG 蓝虚线）
                String graphName = methodKey.replace('$', '_');
                DotGraph dot = new DotGraph(graphName);
                dot.setGraphLabel("Solid: CFG   |   Dashed Blue: Data (Def→Use)");
                for (StmtNode n : stmtNodes) {
                    DotGraphNode dn = dot.drawNode("n" + n.stmtId);
                    dn.setLabel(String.valueOf(n.stmtId));
                    dn.setAttribute("xlabel", "\"src:L" + n.startLine + ".." + n.endLine + "\"");
                    dn.setAttribute("tooltip", "\"" + escapeDot(truncate(n.text, 200)) + "\"");
                    dn.setAttribute("shape", "circle");
                }
                for (String k : cfgSeen) {
                    String[] p = k.split("->");
                    dot.drawEdge("n" + p[0], "n" + p[1]);
                }
                for (String k : dfgSeen) {
                    int i1 = k.indexOf("->");
                    int i2 = k.indexOf(':', i1 + 2);
                    String s = k.substring(0, i1);
                    String t = k.substring(i1 + 2, i2);
                    String var = k.substring(i2 + 1);
                    DotGraphEdge e = dot.drawEdge("n" + s, "n" + t);
                    e.setStyle("dashed");
                    e.setAttribute("color", "blue");
                    if (!var.isEmpty()) e.setLabel(var);
                }
                Path dotPath = methodDir.resolve("graph.dot");
                dot.plot(dotPath.toString());

                System.out.println("Wrote: " + methodDir.toAbsolutePath());
            }
        }));

        PackManager.v().runPacks();
    }

    // ======== 工具函数 ========

    static String buildDefaultCP(String processDir) {
        String sep = File.pathSeparator;
        String base = System.getProperty("java.class.path", "");
        if (processDir == null || processDir.isEmpty()) {
            return "target/test-classes" + sep + "target/classes" + sep + base;
        }
        return processDir + sep + "target/test-classes" + sep + "target/classes" + sep + base;
    }

    static String getArg(String[] args, String key, String def) {
        for (int i = 0; i < args.length - 1; i++) {
            if (args[i].equals(key)) return args[i + 1];
        }
        return def;
    }

    // 优先尝试 SourceLnPosTag（起止行），否则回退 LineNumberTag（单行）
    static int[] tryGetLineRange(Unit u) {
        for (Tag t : u.getTags()) {
            String n = t.getName();
            if ("SourceLnPosTag".equals(n)) {
                try {
                    java.lang.reflect.Method m1 = t.getClass().getMethod("startLn");
                    java.lang.reflect.Method m2 = t.getClass().getMethod("endLn");
                    int s = (int) m1.invoke(t);
                    int e = (int) m2.invoke(t);
                    if (s > 0 && e >= s) return new int[]{s, e};
                } catch (Throwable ignore) {}
            }
        }
        Integer ln = tryGetSourceLine(u);
        if (ln != null) return new int[]{ln, ln};
        return null;
    }

    static Integer tryGetSourceLine(Unit u) {
        for (Tag t : u.getTags()) {
            if (t instanceof LineNumberTag) return ((LineNumberTag) t).getLineNumber();
        }
        return null;
    }

    static String tryGetLocalName(UnitValueBoxPair uvp) {
        Value v = uvp.getValueBox().getValue();
        if (v instanceof Local) return ((Local) v).getName();
        return null;
    }

    static String safeReadAll(String path) {
        try {
            byte[] b = Files.readAllBytes(Paths.get(path));
            return new String(b, StandardCharsets.UTF_8);
        } catch (IOException e) {
            System.err.println("[WARN] 读取源码失败：" + path + " —— 将只输出行号。");
            return null;
        }
    }

    static String slice(String src, int sLine, int eLine) {
        if (src == null) return "L" + sLine + ".." + eLine;
        String[] lines = src.replace("\r", "").split("\n", -1);
        sLine = Math.max(1, sLine);
        eLine = Math.min(eLine, lines.length);
        StringBuilder sb = new StringBuilder();
        for (int i = sLine; i <= eLine; i++) {
            sb.append(lines[i - 1]).append('\n');
        }
        return sb.toString().trim();
    }

    static String escapeJson(String s) {
        if (s == null) return "";
        return s.replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "");
    }

    static String escapeDot(String s) {
        if (s == null) return "";
        return s.replace("\\", "\\\\")
                .replace("\"", "\\\"")
                .replace("\n", "\\n")
                .replace("\r", "");
    }

    static String truncate(String s, int max) {
        if (s == null) return "";
        if (s.length() <= max) return s;
        return s.substring(0, max) + "...";
    }

    static String makeMethodKey(SootMethod m) {
        String owner = m.getDeclaringClass().getName(); // FQN，带点
        int line = -1;
        // 尝试从首个 Unit 取一个行号作为方法锚（可选）
        if (m.hasActiveBody()) {
            for (Unit u : m.getActiveBody().getUnits()) {
                Integer ln = tryGetSourceLine(u);
                if (ln != null) { line = ln; break; }
            }
        }
        StringBuilder sb = new StringBuilder();
        sb.append(owner).append("#").append(m.getName()).append("(");
        List<Type> ps = m.getParameterTypes();
        for (int i = 0; i < ps.size(); i++) {
            if (i > 0) sb.append(",");
            sb.append(ps.get(i).toString());
        }
        sb.append(")").append("@").append(line);
        return sb.toString();
    }

    static String safe(String s) {
        return s.replaceAll("[^A-Za-z0-9._@#-]", "_");
    }
}
