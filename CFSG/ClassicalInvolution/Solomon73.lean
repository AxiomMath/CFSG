module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ClassicalInvolution.Solomon73

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def IsE64 (A : Subgroup G) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a * a = 1) ∧ Nat.card A = 64

@[expose] def AutL32 (A : Subgroup G) : Prop :=
  ∃ ρ : ↥(Subgroup.normalizer (A : Set G)) →* GL (Fin 3) (ZMod 2), Function.Surjective ρ ∧
    ρ.ker = (Subgroup.centralizer (A : Set G)).subgroupOf (Subgroup.normalizer (A : Set G))

end CFSG.ClassicalInvolution.Solomon73
