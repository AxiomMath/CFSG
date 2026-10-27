module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

variable {G : Type*} [Group G]

theorem inf_right_sup_eq_of_isInternalSemidirectProduct {X S E A : Subgroup G}
    (hX : FreeCore.IsInternalSemidirectProduct X S E) (hAE : A ≤ E) : (S ⊔ A) ⊓ E = A := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hAE)
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
  have hAS : A ≤ normalizer (S : Set G) := hAE.trans hX.right_le_normalizer
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left S A hAS] at hx1
  obtain ⟨s, hs, a, ha, rfl⟩ := Set.mem_mul.1 hx1
  have hsE : s ∈ E := by
    rw [(mul_inv_cancel_right s a).symm]
    exact mul_mem hx2 (inv_mem (hAE ha))
  have hs1 : s = 1 := Subgroup.mem_bot.1 (hX.inf_eq_bot ▸ Subgroup.mem_inf.2 ⟨hs, hsE⟩)
  simpa [hs1] using ha

theorem right_le_normalizer_of_normal_sup {X S E A : Subgroup G}
    (hX : FreeCore.IsInternalSemidirectProduct X S E) (hAE : A ≤ E)
    (hnorm : X ≤ normalizer ((S ⊔ A : Subgroup G) : Set G)) :
    E ≤ normalizer ((A : Subgroup G) : Set G) := by
  have key := inf_right_sup_eq_of_isInternalSemidirectProduct hX hAE
  intro e he
  have h1 : e ∈ normalizer ((S ⊔ A : Subgroup G) : Set G) := hnorm (hX.right_le he)
  have h2 : e ∈ normalizer ((E : Subgroup G) : Set G) := Subgroup.le_normalizer he
  have h3 := Subgroup.inf_normalizer_le_normalizer_inf (H := S ⊔ A) (K := E)
    (Subgroup.mem_inf.2 ⟨h1, h2⟩)
  rwa [key] at h3

theorem FTS_outside_sigma_plane_complement_normality
    (h₁ : Statements.FTS_outside_sigma_plane_structure.{u}) :
    Statements.FTS_outside_sigma_plane_complement_normality.{u} := by
  intro G _ _ hG M A E p hM hp hpσ hAM hA _hEM hsemi hAE
  exact right_le_normalizer_of_normal_sup hsemi hAE (h₁ G hG M A p hM hp hpσ hAM hA).2.2

end

end CFSG.FeitThompson.Proofs
