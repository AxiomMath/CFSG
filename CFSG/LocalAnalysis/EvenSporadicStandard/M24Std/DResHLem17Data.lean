module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.PairData

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open CFSG.QuasithinUnique.Setup.X1

@[expose] def lem17W1 : List ℤ := [1, 2, -1, -2, -2, 1]

@[expose] def lem17W2 : List ℤ := [2, 2, 1, 1, -2, 1]

@[expose] def lem17T1 : S24 := pairN lem17W1

@[expose] def lem17T2 : S24 := pairN lem17W2

@[expose] def lem17L9 : List S24 :=
  [1, lem17T1, lem17T1 * lem17T1, lem17T2, lem17T1 * lem17T2, lem17T1 * lem17T1 * lem17T2,
    lem17T2 * lem17T2, lem17T1 * lem17T2 * lem17T2, lem17T1 * lem17T1 * lem17T2 * lem17T2]

@[expose] def Lem17Data : Prop :=
  lem17L9.length = 9 ∧ lem17L9.Nodup ∧ (1 : S24) ∈ lem17L9 ∧
    (∀ x ∈ lem17L9, ∀ y ∈ lem17L9, x * y ∈ lem17L9 ∧ x * y = y * x) ∧
    (∀ x ∈ lem17L9, x * x * x = 1) ∧
    (∀ x ∈ lem17L9, (∀ a ∈ m24E1l, x * a * x⁻¹ ∈ m24E1l) ∧
      ∀ b ∈ m24B0l, x * b * x⁻¹ ∈ m24B0l) ∧
    ∀ x ∈ lem17L9, x ≠ 1 → ∃ a ∈ m24E1l, x * a * x⁻¹ * a⁻¹ ∉ m24B0l

instance : Decidable Lem17Data := by unfold Lem17Data; infer_instance

end CFSG.EvenSporadicStandard.M24Std.DResH
