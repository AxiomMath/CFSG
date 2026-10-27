module

public import CFSG.ClassicalInvolution.Q3.Q3OTBase
public import CFSG.ClassicalInvolution.Q3.Q3NMOrth

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin

section Dict

variable {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)} {X : Type} [Group X]

theorem oddCoreIn_fixed_of_lift [Group.IsPerfect (spinGroup Q)]
    (hrange : (spinAction Q).range = elementaryGroup Q) {θ : spinGroup Q →* X}
    (hθs : Function.Surjective θ) (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (τ : MulAut X)
    (αK : MulAut (spinGroup Q)) (hτ : ∀ s, θ (αK s) = τ (θ s)) {g : (ι → F) ≃ₗ[F] (ι → F)}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ s, spinAction Q (αK s) = g * spinAction Q s * g⁻¹)
    (hN : oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
      (conjE Q g hgO))) = ⊥) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient X τ)) = ⊥ := by
  classical
  have hmem : ∀ s : spinGroup Q, spinAction Q s ∈ elementaryGroup Q := fun s => by
    rw [← hrange]
    exact ⟨s, rfl⟩
  set πE : spinGroup Q →* ↥(elementaryGroup Q) :=
    (spinAction Q).codRestrict (elementaryGroup Q) hmem with hπE
  have hπs : Function.Surjective πE := by
    intro e
    have h1 : (e : (ι → F) ≃ₗ[F] (ι → F)) ∈ (spinAction Q).range := by
      rw [hrange]
      exact e.2
    obtain ⟨s, hs⟩ := h1
    exact ⟨s, Subtype.ext hs⟩
  have hπk : πE.ker ≤ Subgroup.center (spinGroup Q) := by
    intro s hs
    exact ker_spinAction_le_center Q (by
      rw [MonoidHom.mem_ker] at hs ⊢
      exact congrArg Subtype.val hs)
  let ε : X ⧸ Subgroup.center X ≃* ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q) :=
    (centralQuotientIso θ hθs hθk).symm.trans (centralQuotientIso πE hπs hπk)
  have hε : ∀ s : spinGroup Q, ε (QuotientGroup.mk (θ s)) = QuotientGroup.mk (πE s) := by
    intro s
    have h1 : (centralQuotientIso θ hθs hθk).symm (QuotientGroup.mk (θ s)) =
        (QuotientGroup.mk s : spinGroup Q ⧸ Subgroup.center (spinGroup Q)) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (centralQuotientIso πE hπs hπk)
      ((centralQuotientIso θ hθs hθk).symm (QuotientGroup.mk (θ s))) = _
    rw [h1]
    rfl
  have hcongr : MulAut.congr ε.symm (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hgO)) =
      autToCentralQuotient X τ := by
    refine MulEquiv.ext fun xb => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective xb
    obtain ⟨s, rfl⟩ := hθs y
    have h1 : (MulAut.congr ε.symm (autToCentralQuotient ↥(elementaryGroup Q) (conjE Q g hgO)))
        (QuotientGroup.mk (θ s)) = ε.symm ((autToCentralQuotient ↥(elementaryGroup Q)
          (conjE Q g hgO)) (ε (QuotientGroup.mk (θ s)))) := rfl
    rw [h1, hε, autToCentralQuotient_mk]
    have hπα : conjE Q g hgO (πE s) = πE (αK s) :=
      Subtype.ext (by
        show g * spinAction Q s * g⁻¹ = spinAction Q (αK s)
        rw [hg])
    rw [hπα, ← hε, MulEquiv.symm_apply_apply, autToCentralQuotient_mk, hτ]
  rw [← hcongr]
  exact oddCoreIn_fixed_congr_eq_bot' ε.symm _ hN

end Dict

end CFSG.ClassicalInvolution.Q3.Q3OT
