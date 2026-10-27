module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelCd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelFuse
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUnique
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueIndex

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

structure Fi22CoverAut : Prop where
  rank : ∀ σ : MulAut ↥Cd, σ * σ = 1 → (∀ l : ↥Cd, σ ≠ MulAut.conj l) →
    ∀ B : Subgroup ↥Cd, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8
  aut_cent : ∀ σ : MulAut ↥Cd, (∀ e ∈ E0, σ e = e) → ∃ x ∈ E0, σ = MulAut.conj x

theorem fi22CoverRest_of_aut
    (A : Fi22CoverAut) :
    Fi22CoverRest :=
  ⟨E0_card, E0_sq, E0_fuse, E0_gen, E0_odd_index, E0_unique, A.rank, A.aut_cent⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81
