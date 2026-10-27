module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Frame
public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

@[expose] def IsQ8Decomp {A : Type} [Group A] (U V : Subgroup A) : Prop :=
  Nonempty (↥U ≃* QuaternionGroup 2) ∧ Nonempty (↥V ≃* QuaternionGroup 2) ∧
    (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧ U ⊔ V = ⊤ ∧ Nat.card ↥(U ⊓ V) = 2

@[expose] def Lemma22_1 : Prop :=
  ∀ (A : Type) [Group A] [Finite A], IsQ8StarQ8 A →
    ∃ U V : Subgroup A, IsQ8Decomp U V ∧
      ∀ U' V' : Subgroup A, IsQ8Decomp U' V' → (U' = U ∧ V' = V) ∨ (U' = V ∧ V' = U)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
