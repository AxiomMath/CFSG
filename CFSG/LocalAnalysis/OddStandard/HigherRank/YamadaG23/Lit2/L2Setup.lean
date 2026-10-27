module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

abbrev l2Mu (X : Type*) [Group X] : X →* X ⧸ CFSG.oddCore X :=
  QuotientGroup.mk' (CFSG.oddCore X)

abbrev l2Bar {X : Type*} [Group X] (H : Subgroup X) : Subgroup (X ⧸ CFSG.oddCore X) :=
  H.map (l2Mu X)

structure L2Setup {X G : Type*} [Group X] [Group G] (Z A : Subgroup X) (π : X →* G)
    (M : Subgroup G) (H : Subgroup X) : Prop where
  surj : Function.Surjective π
  ker : π.ker = litP Z
  central : ∀ z ∈ Z, ∀ x : X, z * x = x * z
  four : ∀ z ∈ Z, z ^ 4 = 1
  Z_le_A : Z ≤ A
  Z_le_H : Z ≤ H
  simple : IsSimpleGroup ↥M
  nonab : ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a
  perf : ⁅H, H⁆ = H
  map_H : H.map π = M
  cent : ∀ x ∈ H, ∀ y ∈ π.ker, x * y = y * x
  A_le : A.map π ≤ M

@[expose] def L2Form {X : Type*} [Group X] (Z A : Subgroup X) : Prop :=
  ∃ ι ∈ Z, orderOf ι = 2 ∧ (∀ a ∈ A, a ^ 2 = 1 ∨ a ^ 2 = ι) ∧
    (∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = ι) ∧ ∀ a ∈ A, a ∉ Z → ∃ b ∈ A, ⁅a, b⁆ = ι

end CFSG.OddStandard.HigherRank.YamadaG23
