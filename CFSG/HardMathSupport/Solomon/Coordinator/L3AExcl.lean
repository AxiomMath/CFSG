module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AAutDerived
public import CFSG.HardMathSupport.Solomon.Coordinator.L3ABridge
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag

structure GoodPinned {M : Type*} [Group M] (P : PinnedAut M) : Prop where
  sep : P.Separated
  norm : P.inndiag.Normal
  up : P.inndiag ≤ commutator (MulAut M)
  down : commutator (MulAut M) ≤ P.inndiag

theorem goodPinned_psl (F : Type) [Field F] [Finite F] : GoodPinned (stdPinnedPSL 3 F) where
  sep := stdPinnedPSL_separated le_rfl
  norm := (stdPinnedPSL_stable le_rfl).normal
  up := by
    intro x hx
    rw [stdPinnedPSL_inndiag, linearAutGroup_eq_range] at hx
    obtain ⟨A, rfl⟩ := hx
    exact conjAut_mem_commutator F A
  down := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact OuterDerived.commutator_mem_linearAutGroup le_rfl a b

theorem goodPinned_psu {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)
    (hq : 2 < p ^ f) : GoodPinned (stdPinnedPSU3 hF) where
  sep := stdPinnedPSU3_separated hF
  norm := (stdPinnedPSU3_stable hq).normal
  up := by
    rintro x ⟨A, rfl⟩
    exact psuConj_mem_commutator hF hq A
  down := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact commutator_mem_psuConj_range hF hq a b

theorem eq_one_of_inndiag_of_field {Q M₁ M₂ : Type*} [Group Q] [Group M₁] [Group M₂]
    {P₁ : PinnedAut M₁} {P₂ : PinnedAut M₂} (g₁ : GoodPinned P₁) (g₂ : GoodPinned P₂)
    (e₁ : Q ≃* M₁) (e₂ : Q ≃* M₂) {τ : MulAut Q} (h₁ : MulAut.congr e₁ τ ∈ P₁.inndiag)
    {φ : MulAut M₂} (hφ : φ ∈ P₂.field) (γ : MulAut M₂)
    (h₂ : MulAut.congr e₂ τ = γ * φ * γ⁻¹) : τ = 1 := by
  have h3 : MulAut.congr e₁ τ ∈ commutator (MulAut M₁) := g₁.up h₁
  set u : MulAut M₁ ≃* MulAut M₂ := MulAut.congr (e₁.symm.trans e₂) with hu
  have h4 : u (MulAut.congr e₁ τ) = MulAut.congr e₂ τ := by
    ext m
    simp [hu, MulAut.congr_apply]
  have h5 : MulAut.congr e₂ τ ∈ commutator (MulAut M₂) := by
    rw [← h4]
    have : u (MulAut.congr e₁ τ) ∈ (commutator (MulAut M₁)).map u.toMonoidHom := ⟨_, h3, rfl⟩
    rw [commutator_def, Subgroup.map_commutator] at this
    exact Subgroup.commutator_mono le_top le_top this
  have h6 := g₂.down h5
  rw [h₂] at h6
  have h7 := eq_one_of_isField_mem_inndiag P₂ g₂.sep g₂.norm hφ γ h6
  rw [← h₂] at h7
  exact (MulAut.congr e₂).injective (by rw [map_one]; exact h7)

end CFSG.HardMathSupport.Solomon.Coordinator
