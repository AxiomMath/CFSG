module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.E0
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Model

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem E0_center_le :
    center ↥Cd ≤ E0 := by
  intro z hz
  rw [center_C] at hz
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz
  rw [← hk]
  refine zpow_mem ?_ k
  rw [E0, mem_subgroupOf]
  refine ⟨eVec 0, ?_⟩
  rw [fjHom_eVec, fjPt_zero]
  rfl

structure Fi22CoverRest : Prop where
  card_E : Nat.card E0 = 2 ^ 11
  E_sq : ∀ e ∈ E0, e ^ 2 = 1
  fuse : ∀ s : ↥Cd, orderOf s = 2 → ∃ l : ↥Cd, l⁻¹ * s * l ∈ E0
  gen : normalizer (E0 : Set ↥Cd) ≤
    E0 ⊔ closure {y | y ∈ normalizer (E0 : Set ↥Cd) ∧ Odd (orderOf y)}
  odd_index : Odd (normalizer (E0 : Set ↥Cd)).index
  unique : ∀ B : Subgroup ↥Cd, B ≤ normalizer (E0 : Set ↥Cd) → (∀ b ∈ B, b ^ 2 = 1) →
    Nat.card B = 2 ^ 11 → B = E0
  rank : ∀ σ : MulAut ↥Cd, σ * σ = 1 → (∀ l : ↥Cd, σ ≠ MulAut.conj l) →
    ∀ B : Subgroup ↥Cd, (∀ b ∈ B, b ^ 2 = 1) → (∀ b ∈ B, σ b = b) → Nat.card B ≤ 2 ^ 8
  aut_cent : ∀ σ : MulAut ↥Cd, (∀ e ∈ E0, σ e = e) → ∃ x ∈ E0, σ = MulAut.conj x

theorem localModel_Cd
    (R : Fi22CoverRest) :
    LocalModel ↥Cd E0 :=
  ⟨R.card_E, R.E_sq, E0_center_le, R.fuse, R.gen, R.odd_index, R.unique, Cd_sq, R.rank,
    R.aut_cent⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81
