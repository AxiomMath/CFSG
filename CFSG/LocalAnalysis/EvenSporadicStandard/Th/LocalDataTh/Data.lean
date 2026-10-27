module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Action
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Coded

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th.Max3
open scoped Matrix

@[expose] def wordOfString (s : String) : List Gen :=
  s.toList.map fun c => if c = 'x' then Gen.x else Gen.y

@[expose] def wordMat (w : List Gen) : Mat8 := (w.map (Gen.eval B1 B2)).prod

@[expose] def B1c : List ℕ := [2, 1, 8, 4, 64, 128, 16, 32]

@[expose] def B2c : List ℕ := [2, 150, 1, 222, 4, 8, 82, 248]

@[expose] def letterCols : Gen → List ℕ
  | .x => B1c
  | .y => B2c

@[expose] def wordCols (w : List Gen) : List ℕ :=
  (w.map letterCols).foldr (mulCols 8) (idCols 8)

@[expose] def pWordStrings : List String :=
  ["", "yxyxyxyyxyyyxyxyyyyxyyxyxy", "yyxyyyxyyyxyyxyyyxyyyx", "yyyxyxyxyyxyxyyyx",
    "xyyyyxyxyxyyxyxyyyy", "xyyxyxyyyyxyyyxyyxyyxyyyx", "yxyyxyyyxyxyyyyxyxyyx",
    "xyxyyxyyxyxyyxyxyyyxyxyyyy", "xyyyxyxyxyyxyyxyxyyyyy", "yyxyyxyyyyyxyxyyyyxyyyy",
    "xyxyyxyyxyyxyyxyyyyxyyxyy", "yxyxyxyyyyxyyyyxyyxyyyxy", "yyyxyyyyxyyxyyyxyxyy",
    "yxyyxyyyyyxyxyyyyxyyxyx", "xyyxyyyxyxyyxyyyxyyyyxyyy", "yyyxyxyxyyxyyyyxyyyx",
    "yyxyyxyyyyyxyxyxyyyyxy", "yxyyyxyxyyxyyyxyyyyxyyx", "yxyxyxyyyyyxyyxyxyx",
    "xyyxyxyxyyxyyyxyxyyyyxyy", "xyxyxyyyxyyyxyyyyxy", "yxyyxyyxyyxyyxyyyxyyxyyxyx",
    "xyxyxyxyyyxyyyxyyyyxyxy", "yyxyyyxyxyyyyxyyxyyyxyxyx", "yxyxyyyyxyyyxyyxyyxyyyy",
    "yyyyyxyyxyyyxyyyy", "xyxyyxyxyxyyyyyxyyxyxyy", "xyyxyyxyxyxyyyxyyyyxyyy",
    "xyxyxyxyyyxyyyxyyyx", "xyyyyxyxyxyyxyyyyxyyyyxy", "xyxyyyyxyyyyxyyxyyyxyxyx",
    "yyyxyxyxyyxyyyyxyyyyxyxy", "yxyyxyyxyyxyyxyxyyxyyxyy", "xyxyxyyyyxyyyyxyyxyyyxyxyy",
    "yxyyxyyxyyxyyyyxyyxyx", "xyyxyxyxyyyyxyyyyxyyxyyx", "xyyxyyxyyyxyxyyyyxyxyyy",
    "xyxyyyyxyxyxyyxyyyyxyyyy", "yyyxyyyxyyxyyxyyyxyyyyxyy", "xyyxyxyxyyyyyxyyxyxyyxy",
    "xyyyxyyxyyyyyxyxyxyyyy", "yyyyyxyyyxyyyyxyyxyyyxyxyx", "xyxyyyxyyxyyyyyxyxyxyyyx",
    "xyyyxyyyxyyyx", "xyxyyyxyyyxyyyy", "yxyyxyxyyxyxyyyxyxyyyx", "yxyxyyyyxyyyyxyyxyyyxyxyyy",
    "yyyyxyyyyyxyyyyxyyxyxyy", "yyyyxyyxyxyxyyyxyyyxyyy", "yxyxyyyxyxyyyxyyyyyxyyxyyy",
    "xyyxyyxyyxyxyxyyyyxyyyyx", "yyxyyyxyyyxyyyyyx", "yxyxyxyyxyyyxyxyyyyxyx", "xyxyxy",
    "xyxyxyyyyxyxyxyyxyxyyyx", "yxyyyxyxyyxyxyxyyxyxyxyx", "xyyxyyxyxyyxyxyyyxyxyyyyxy",
    "yyxyyyxyyyyxy", "xyxyyxyyyyxyyxyyyxyyxyxyyx", "xyyyxyyyxyyyyxyxy", "yxyyxyxyxyyyxyyyyxyyx",
    "yxyxyxyyyyyxyyxyxyyxyxy", "yyxyxyyyyxyyyxyyyxyxyxyy", "yyyyxyxyyxyyxyyxyxyyyyxyyx"]

@[expose] def Pc : List (List ℕ) := pWordStrings.map fun s => wordCols (wordOfString s)

@[expose] def Pt : Finset Mat8 := (Pc.map (matOfCols 8)).toFinset

@[expose] def Kstep (K : List ℕ) : List ℕ :=
  (List.range 256).filter fun v => Pc.all fun a => decide ((applyCols 8 a v ^^^ v) ∈ K)

@[expose] def Kc : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => Kstep (Kc k)

@[expose] def uCodes : List ℕ := [1, 50, 100]

@[expose] def UCodes : List ℕ := [0, 1, 50, 51, 86, 87, 100, 101]

@[expose] def PtFacts : Prop :=
  Pt.card = 64 ∧ (∀ a ∈ Pc, a.length = 8 ∧ ∀ x ∈ a, x < 256) ∧ idCols 8 ∈ Pc ∧
  (∀ a ∈ Pc, ∀ b ∈ Pc, mulCols 8 a b ∈ Pc) ∧
  (∀ a ∈ Pc, ∃ b ∈ Pc, mulCols 8 a b = idCols 8) ∧
  (∀ v < 256, v ∈ Kc 3 ↔ v ∈ UCodes) ∧
  (∀ a ∈ Pc, a ≠ idCols 8 → ∃ v < 256, (applyCols 8 a v ^^^ v) ∉ Kc 2) ∧
  (∀ u ∈ UCodes, ∀ w ∈ UCodes, (u ^^^ w) ∈ UCodes) ∧
  (∀ u ∈ UCodes, CFSG.Certificates.ExtraspecialNF.qf c (codeVec 8 u) = 0) ∧
  (∀ u ∈ UCodes, ∀ w ∈ UCodes,
    CFSG.Certificates.ExtraspecialNF.bil c (codeVec 8 u) (codeVec 8 w) = 0) ∧
  (∀ e : Fin 3 → ZMod 2, ∑ j, e j • codeVec 8 (uCodes.getD j 0) = 0 → e = 0)

set_option synthInstance.maxSize 1000 in
instance : Decidable PtFacts := by unfold PtFacts; infer_instance

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
