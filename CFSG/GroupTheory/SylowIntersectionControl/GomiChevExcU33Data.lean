module

public import CFSG.Quasithin.Recognition.CertU33Outer
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.GroupTheory.GomiExcU33

open CFSG.Quasithin

@[expose] def u33OrbWords : List String :=
  ["", "a", "b", "s", "y", "ya", "yb", "ys", "ay", "xy", "yy", "aya", "xya", "xyb", "yyb", "xys",
   "xay", "sxy", "yxy", "xyy", "xaya", "sxya", "xxya", "yxya", "yxyb", "xyyb", "sxys", "yxys",
   "sxay", "yxay", "ysxy", "ayxy", "byxy", "syxy", "xyxy", "yyxy", "sxyy", "yxyy", "sxaya",
   "yxaya", "ysxya", "yxxya", "ayxya", "byxya", "syxya", "xyxya", "yyxya", "ayxyb", "byxyb",
   "syxyb", "xyxyb", "yyxyb", "sxyyb", "yxyyb", "ysxys", "ayxys", "byxys", "syxys", "xyxys",
   "yyxys", "ayxay", "xyxay", "bysxy", "xysxy", "xayxy", "xbyxy", "xsyxy", "sxyxy", "xxyxy",
   "yxyxy", "xyyxy", "ayxyy", "xyxyy", "ayxaya", "xyxaya", "xysxya", "xyxxya", "xayxya", "xbyxya",
   "xsyxya", "sxyxya", "xxyxya", "yxyxya", "xyyxya", "xayxyb", "xbyxyb", "xsyxyb", "sxyxyb",
   "xxyxyb", "yxyxyb", "xyyxyb", "xyxyyb", "xysxys", "xayxys", "xbyxys", "xsyxys", "sxyxys",
   "xxyxys", "yxyxys", "xyyxys", "xayxay", "sxyxay", "xxyxay", "yxyxay", "xbysxy", "sxysxy",
   "xxysxy", "yxysxy", "sxayxy", "yxayxy", "sxbyxy", "xxbyxy", "yxbyxy", "yxsyxy", "ysxyxy",
   "yxxyxy", "ayxyxy", "byxyxy", "syxyxy", "yyxyxy", "sxyyxy", "xxyyxy", "yxyyxy", "xayxyy",
   "sxyxyy", "xxyxyy", "yxyxyy", "xayxaya", "sxyxaya", "xxyxaya", "yxyxaya", "yxysxya", "yxyxxya",
   "sxayxya", "yxayxya", "sxbyxya", "yxbyxya", "yxsyxya", "ysxyxya", "yxxyxya", "ayxyxya",
   "byxyxya", "syxyxya", "xyxyxya", "yyxyxya", "sxyyxya", "yxyyxya", "sxayxyb", "yxayxyb",
   "sxbyxyb", "yxbyxyb", "yxsyxyb", "ysxyxyb", "yxxyxyb", "ayxyxyb", "byxyxyb", "syxyxyb",
   "yyxyxyb", "sxyyxyb", "yxyyxyb", "yxyxyyb", "yxysxys", "sxayxys", "yxayxys", "yxbyxys",
   "yxsyxys", "ysxyxys", "yxxyxys", "ayxyxys", "byxyxys", "yyxyxys", "yxyyxys", "sxayxay",
   "yxayxay", "ysxyxay", "yxxyxay", "ayxyxay", "byxyxay", "syxyxay", "xyxyxay", "yyxyxay",
   "sxbysxy", "yxbysxy", "ysxysxy", "yxxysxy", "ayxysxy", "byxysxy", "syxysxy", "yyxysxy",
   "ayxayxy", "byxayxy", "ysxbyxy", "yxxbyxy", "ayxbyxy", "ayxsyxy", "byxsyxy", "xyxsyxy",
   "yyxsyxy", "bysxyxy", "byxxyxy", "sbyxyxy", "xsyxyxy", "byyxyxy", "syyxyxy", "xyyxyxy",
   "ysxyyxy", "byxyyxy", "sxayxyy", "yxayxyy", "ysxyxyy", "yxxyxyy", "ayxyxyy", "byxyxyy",
   "syxyxyy", "yyxyxyy", "sxayxaya", "yxayxaya", "ysxyxaya", "yxxyxaya", "ayxyxaya", "byxyxaya",
   "syxyxaya", "yyxyxaya", "byxysxya", "syxysxya", "yyxysxya", "ayxyxxya", "byxyxxya", "syxyxxya",
   "yyxyxxya", "ayxayxya", "byxayxya", "ysxbyxya", "ayxbyxya", "ayxsyxya", "byxsyxya", "xyxsyxya",
   "bysxyxya", "xxyxyxya", "yxyxyxya", "ayxyyxya", "yyxyyxya", "ayxayxyb", "byxayxyb", "ysxbyxyb",
   "ayxbyxyb", "ayxsyxyb", "yysxyxyb", "xyxxyxyb", "ayxayxys", "byxsyxys", "bysxyxys"]

@[expose] def u33CentWords : List String :=
  ["", "aa", "bb", "sx", "xa", "abs", "abx", "axs", "axx", "aabb", "aasx", "aaxa", "ayay", "bbsx",
   "bbxa", "bxas", "bxax", "sxaa", "xasx", "xyay", "yysy", "abbxs", "abbxx", "axaax"]

@[expose] def u33OutWords : List String :=
  ["", "xxya", "xyy", "sxya", "xaya", "", "ya", "aya", "a", "yb", "", "yy", "b", "", "", "",
   "xya", "xyb", "ys", "sxyy", "", "yyb", "sxaya", "y", "ay", "", "s", "", "", "", "", ""]

@[expose] def u33ConjL (w : List (ℕ × Bool)) (o : List ℕ) : List ℕ :=
  compL (compL (u33WordL w) o) (u33WordL (u33InvW w))

theorem u33Words_length : u33OrbWords.length = 252 ∧ u33CentWords.length = 24 ∧
    u33OutWords.length = 32 := by
  decide +kernel

theorem u33Words_letters : (∀ s ∈ u33OrbWords, ∀ l ∈ u33W s, l.1 < 5) ∧
    (∀ s ∈ u33CentWords, ∀ l ∈ u33W s, l.1 < 5) ∧
    (∀ s ∈ u33OutWords, ∀ l ∈ u33W s, l.1 < 5) := by
  decide +kernel

theorem u33OrbWords_nodup : (u33OrbWords.map fun s => u33ConjL (u33W s) u33PiTab).Nodup :=
  CFSG.Decide.nodup_of_bitsetNodup (CFSG.Decide.listKey 28 [0, 1, 4]) (by decide +kernel)

theorem u33OutWords_conj : ∀ i < 64, 32 ≤ i → compL (u33XL i) (u33XL i) = List.range 28 →
    u33ConjL (u33W (u33OutWords.getD (i - 32) "")) u33PiTab = u33XL i := by
  decide +kernel

theorem u33CentWords_comm : ∀ s ∈ u33CentWords,
    compL (u33WordL (u33W s)) u33PiTab = compL u33PiTab (u33WordL (u33W s)) := by
  decide +kernel

theorem u33CentWords_conj : ∀ s ∈ u33CentWords,
    compL (u33ConjL (u33W s) u33A2Tab) u33A2Tab =
      compL u33A2Tab (u33ConjL (u33W s) u33A2Tab) := by
  decide +kernel

theorem u33CentWords_nodup : (u33CentWords.map fun s => u33WordL (u33W s)).Nodup := by
  decide +kernel

theorem u33A2Tab_facts : compL u33A2Tab u33A2Tab = List.range 28 ∧
    u33A2Tab ≠ List.range 28 ∧ compL u33A2Tab u33PiTab = compL u33PiTab u33A2Tab := by
  decide +kernel

end CFSG.GroupTheory.GomiExcU33
