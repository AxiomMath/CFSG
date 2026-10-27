module

public import CFSG.GH74.GLS.NT44.ActualCoverModel
public import CFSG.Mathlib.GroupTheory.PerfectCentralAut
import CFSG.GH74.GLS.NT44.ActualCover

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG.ComponentClassification.PSL3Four

theorem autProjection :
      ∃ Φ : MulAut CFSG.GH74.GLS.NT44.FullTwoCover ≃* MulAut CFSG.ComponentClassification.PSL3Four.S,
      (∀ (α : MulAut CFSG.GH74.GLS.NT44.FullTwoCover) (u : CFSG.GH74.GLS.NT44.FullTwoCover),
        CFSG.GH74.GLS.NT44.fullTwoCoverToS (α u) = Φ α (CFSG.GH74.GLS.NT44.fullTwoCoverToS u)) ∧
      (∀ (β : MulAut CFSG.ComponentClassification.PSL3Four.S) (u : CFSG.GH74.GLS.NT44.FullTwoCover),
        CFSG.GH74.GLS.NT44.fullTwoCoverToS (Φ.symm β u) = β (CFSG.GH74.GLS.NT44.fullTwoCoverToS u)) ∧
      (∀ (β : MulAut CFSG.ComponentClassification.PSL3Four.S) (α : MulAut CFSG.GH74.GLS.NT44.FullTwoCover),
        (∀ u : CFSG.GH74.GLS.NT44.FullTwoCover, CFSG.GH74.GLS.NT44.fullTwoCoverToS (α u) = β (CFSG.GH74.GLS.NT44.fullTwoCoverToS u)) →
          α = Φ.symm β) ∧
      (∀ u : CFSG.GH74.GLS.NT44.FullTwoCover,
        Φ (MulAut.conj u) = MulAut.conj (CFSG.GH74.GLS.NT44.fullTwoCoverToS u)) ∧
      (∀ α : MulAut CFSG.GH74.GLS.NT44.FullTwoCover,
        Φ α ∈ (MulAut.conj : CFSG.ComponentClassification.PSL3Four.S →* MulAut CFSG.ComponentClassification.PSL3Four.S).range ↔
          α ∈ (MulAut.conj : CFSG.GH74.GLS.NT44.FullTwoCover →* MulAut CFSG.GH74.GLS.NT44.FullTwoCover).range) ∧
      (∀ Φ' : MulAut CFSG.GH74.GLS.NT44.FullTwoCover ≃* MulAut CFSG.ComponentClassification.PSL3Four.S,
        (∀ (α : MulAut CFSG.GH74.GLS.NT44.FullTwoCover) (u : CFSG.GH74.GLS.NT44.FullTwoCover),
          CFSG.GH74.GLS.NT44.fullTwoCoverToS (α u) = Φ' α (CFSG.GH74.GLS.NT44.fullTwoCoverToS u)) → Φ' = Φ) := by
  obtain ⟨_, _, _, _, _, hπ_surj, _, hπ_ker_center, hπ_ker_card, hF_perfect,
      hF_finite, _, _⟩ :=
    @CFSG.GH74.GLS.NT44.modelStructure
  have hlift : ∀ β : MulAut S,
      ∃ α : MulAut FullTwoCover, ∀ u : FullTwoCover,
        fullTwoCoverToS (α u) = β (fullTwoCoverToS u) := by
    intro β
    let qβ : FullTwoCover →* S := β.symm.toMonoidHom.comp fullTwoCoverToS
    have hqβ_surj : Function.Surjective qβ := by
      intro s
      obtain ⟨x, hx⟩ := hπ_surj (β s)
      refine ⟨x, ?_⟩
      change β.symm (fullTwoCoverToS x) = s
      rw [hx]
      simp
    have hqβ_ker : qβ.ker = fullTwoCoverToS.ker := by
      ext x
      change β.symm (fullTwoCoverToS x) = 1 ↔ fullTwoCoverToS x = 1
      constructor
      · intro h
        have h' := congrArg (fun y : S => β y) h
        simpa using h'
      · intro h
        simp [h]
    have hqβ_ker_le : qβ.ker ≤ Subgroup.center FullTwoCover := by
      rw [hqβ_ker]
      exact hπ_ker_center.le
    have hqβ_ker_card : Nat.card ↥qβ.ker = 16 := by
      rw [hqβ_ker]
      exact hπ_ker_card
    obtain ⟨_, e, _, _, _, hqe, _, _, _, _⟩ :=
      @CFSG.GH74.GLS.NT44.actualCoverEquiv 
        FullTwoCover inferInstance hF_finite hF_perfect qβ hqβ_surj hqβ_ker_le hqβ_ker_card
    refine ⟨e, ?_⟩
    intro u
    have h1 : β.symm (fullTwoCoverToS (e u)) = fullTwoCoverToS u := by
      simpa [qβ] using DFunLike.congr_fun hqe u
    calc
      fullTwoCoverToS (e u) = β (β.symm (fullTwoCoverToS (e u))) := by simp
      _ = β (fullTwoCoverToS u) := by rw [h1]
  obtain ⟨Φ, hΦ, hsymm, huniq, hconj, hinner, huniq'⟩ :=
    CFSG.exists_autEquiv_of_lifts hF_perfect fullTwoCoverToS hπ_surj hπ_ker_center hlift
  exact ⟨Φ, hΦ, hsymm, huniq, hconj, hinner, huniq'⟩

end CFSG.GH74.GLS.NT44
