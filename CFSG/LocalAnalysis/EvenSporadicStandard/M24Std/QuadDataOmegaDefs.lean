module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataTrans
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataWords

public section

namespace CFSG.EvenSporadicStandard.M24Std

open CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def qdOmega : S24 := m24Cj wordQdOmega

@[expose] def qdQB : List S24 := [26, 47, 29, 38, 23, 41].map fun k => m24E1l.getD k 1

@[expose] def qdQ (k : ℕ) : S24 := m24Elt qdQB k

@[expose] def qdFxTab : List ℕ :=
  [24, 0, 0, 0, 0, 8, 8, 8, 0, 8, 8, 8, 0, 8, 8, 8, 0, 8, 8, 8, 8, 8, 0, 8, 8, 0, 8, 8, 8,
    8, 8, 0, 0, 8, 8, 8, 8, 0, 8, 8, 8, 8, 8, 0, 8, 8, 0, 8, 0, 8, 8, 8, 8, 8, 8, 0, 8, 8,
    0, 8, 8, 0, 8, 8]

@[expose] def qdPsiTab : List ℕ :=
  [0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10, 48, 51, 49, 50, 60, 63, 61, 62, 52,
    55, 53, 54, 56, 59, 57, 58, 16, 19, 17, 18, 28, 31, 29, 30, 20, 23, 21, 22, 24, 27, 25,
    26, 32, 35, 33, 34, 44, 47, 45, 46, 36, 39, 37, 38, 40, 43, 41, 42]

@[expose] def qdPsiInvTab : List ℕ :=
  [0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5, 32, 34, 35, 33, 40, 42, 43, 41, 44,
    46, 47, 45, 36, 38, 39, 37, 48, 50, 51, 49, 56, 58, 59, 57, 60, 62, 63, 61, 52, 54, 55,
    53, 16, 18, 19, 17, 24, 26, 27, 25, 28, 30, 31, 29, 20, 22, 23, 21]

@[expose] def qdLin (y : List ℕ) (k : ℕ) : ℕ :=
  ((List.range 6).filter fun i => k.testBit i).foldl (fun acc i => acc ^^^ y.getD i 0) 0

@[expose] def qdPairs : List (ℕ × ℕ) :=
  ((List.range 64).flatMap fun a => (List.range 64).map fun b => (a, b)).filter fun p =>
    qdFxTab.getD p.1 99 == 0 && qdFxTab.getD p.2 99 == 0 && qdFxTab.getD (p.1 ^^^ p.2) 99 == 0

@[expose] def QdEnumBody (y : List ℕ) : Prop :=
  (∀ k ∈ List.range 64, qdFxTab.getD (qdLin y k) 99 = qdFxTab.getD k 99) →
    (∀ k ∈ List.range 64, qdLin y (qdPsiTab.getD k 0) = qdPsiTab.getD (qdLin y k) 0) ∨
    (∀ k ∈ List.range 64, qdLin y (qdPsiTab.getD k 0) = qdPsiInvTab.getD (qdLin y k) 0)

instance (y : List ℕ) : Decidable (QdEnumBody y) := by
  unfold QdEnumBody
  infer_instance

@[expose] def QdEnum : Prop :=
  ∀ p₁ ∈ qdPairs, ∀ p₂ ∈ qdPairs, ∀ p₃ ∈ qdPairs,
    QdEnumBody [p₁.1, p₁.2, p₂.1, p₂.2, p₃.1, p₃.2]

instance : Decidable QdEnum := by
  unfold QdEnum
  infer_instance

@[expose] def QdOmegaData : Prop :=
  QdNormChk qdOmega ∧ qdOmega * qdOmega * qdOmega = 1 ∧
    (∀ s ∈ m24E1l, qdOmega * s * qdOmega⁻¹ = s → s = 1) ∧
    (∀ k ∈ List.range 64, qdPsiTab.getD k 0 < 64 ∧ qdPsiInvTab.getD k 0 < 64 ∧
      qdOmega * qdQ k * qdOmega⁻¹ = qdQ (qdPsiTab.getD k 0) ∧
      qdOmega⁻¹ * qdQ k * qdOmega = qdQ (qdPsiInvTab.getD k 0)) ∧
    QdEnum

instance : Decidable QdOmegaData := by
  unfold QdOmegaData
  infer_instance

@[expose] def QdQData : Prop :=
  (∀ s ∈ m24E1l, ∃ k ∈ List.range 64, qdQ k = s) ∧
    (∀ k ∈ List.range 64, qdQ k ∈ m24E1l) ∧
    (∀ k ∈ List.range 64, ∀ j ∈ List.range 64, qdQ k * qdQ j = qdQ (k ^^^ j)) ∧
    (∀ k ∈ List.range 64, ∀ j ∈ List.range 64, qdQ k = qdQ j → k = j) ∧
    ∀ k ∈ List.range 64, qdFix (qdQ k) = qdFxTab.getD k 99

instance : Decidable QdQData := by
  unfold QdQData
  infer_instance

end CFSG.EvenSporadicStandard.M24Std
