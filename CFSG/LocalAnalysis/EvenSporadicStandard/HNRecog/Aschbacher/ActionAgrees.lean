module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.PerfectCommutator
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.CohomologyVanishing
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.ActionGeometry
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.CenterCentral

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup

variable {C C' : Type} [Group C] [Group C'] [Finite C] [Finite C'] {Q : Subgroup C}
  {Q' : Subgroup C'} [Q.Normal] [Q'.Normal]

theorem AschbacherHyp.exists_conj_of_isOuterInvolution (hC : AschbacherHyp C Q)
    (hC' : AschbacherHyp C' Q') (α : ↥(commutator C) ≃* ↥(commutator C')) {t : C}
    (ht : IsOuterInvolution Q t) :
    ∃ τ : C', τ ∉ commutator C' ∧ ∀ l : ↥(commutator C),
      ((α (MulAut.conjNormal t l) : ↥(commutator C')) : C') = τ * (α l : C') * τ⁻¹ := by
  obtain ⟨τ, hτL, hτ⟩ := hC.exists_conj_mod_centerOf hC' α ht
  let β : ↥(commutator C') ≃* ↥(commutator C') := α.symm.trans ((MulAut.conjNormal t).trans α)
  let γ : ↥(commutator C') ≃* ↥(commutator C') := β.trans (MulAut.conjNormal τ⁻¹)
  haveI := hC'.plus.finite
  have hE' := hC'.plus.isExtraspecialPGroup
  letI : Module (ZMod 2) (Additive (Abelianization Q')) :=
    CFSG.GroupTheory.extraspecialQuotientModule hE'
  have hγ : ∀ x : ↥(commutator C'), (x : C') ∈ Q' →
      ((γ x : ↥(commutator C')) : C') * (x : C')⁻¹ ∈ centerOf Q' := by
    intro x hx
    have h1 : ((β x : ↥(commutator C')) : C') * (τ * (x : C') * τ⁻¹)⁻¹ ∈ centerOf Q' := hτ x hx
    have hz := Subgroup.mem_center_iff.mp (hC'.centerOf_le_center h1) τ
    have hγx : ((γ x : ↥(commutator C')) : C') = τ⁻¹ * ((β x : ↥(commutator C')) : C') * τ⁻¹⁻¹ :=
      MulAut.conjNormal_apply τ⁻¹ (β x)
    have h2 : ((γ x : ↥(commutator C')) : C') * (x : C')⁻¹ =
        (((β x : ↥(commutator C')) : C') * (τ * (x : C') * τ⁻¹)⁻¹) := by
      generalize ((β x : ↥(commutator C')) : C') = y at hz hγx h1 ⊢
      rw [hγx]
      have hz' : τ⁻¹ * (y * (τ * (x : C') * τ⁻¹)⁻¹) * τ = y * (τ * (x : C') * τ⁻¹)⁻¹ := by
        calc τ⁻¹ * (y * (τ * (x : C') * τ⁻¹)⁻¹) * τ
            = τ⁻¹ * ((y * (τ * (x : C') * τ⁻¹)⁻¹) * τ) := by group
          _ = τ⁻¹ * (τ * (y * (τ * (x : C') * τ⁻¹)⁻¹)) := by rw [hz]
          _ = y * (τ * (x : C') * τ⁻¹)⁻¹ := by group
      rw [← hz']
      group
    rw [h2]
    exact h1
  obtain ⟨q, hq, hqγ⟩ := exists_conj_of_forall_mem_centerOf (L := commutator C') hE'
    hC'.centralizer_le hC'.le_commutator hC'.commutator_commutator_eq_top
    hC'.centerOf_le_center hC'.crossedHomVanishing_commutator γ hγ
  refine ⟨τ * q, ?_, fun l => ?_⟩
  · intro h
    exact hτL (by simpa using mul_mem h (inv_mem (hC'.le_commutator hq)))
  · have h1 := hqγ (α l)
    have hγl : ((γ (α l) : ↥(commutator C')) : C') =
        τ⁻¹ * ((α (MulAut.conjNormal t l) : ↥(commutator C')) : C') * τ⁻¹⁻¹ := by
      have : γ (α l) = MulAut.conjNormal τ⁻¹ (α (MulAut.conjNormal t l)) := by
        simp [γ, β]
      rw [this]
      exact MulAut.conjNormal_apply τ⁻¹ _
    have h3 : τ⁻¹ * ((α (MulAut.conjNormal t l) : ↥(commutator C')) : C') * τ⁻¹⁻¹ =
        q * ((α l : ↥(commutator C')) : C') * q⁻¹ := hγl.symm.trans h1
    generalize ((α (MulAut.conjNormal t l) : ↥(commutator C')) : C') = A at h3 ⊢
    generalize ((α l : ↥(commutator C')) : C') = B at h3 ⊢
    calc A = τ * (τ⁻¹ * A * τ⁻¹⁻¹) * τ⁻¹ := by group
      _ = τ * (q * B * q⁻¹) * τ⁻¹ := by rw [h3]
      _ = τ * q * B * (τ * q)⁻¹ := by group

end CFSG.EvenSporadicStandard.HNRecog
