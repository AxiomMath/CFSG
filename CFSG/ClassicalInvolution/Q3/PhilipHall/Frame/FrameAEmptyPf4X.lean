module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf4C3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf3HexMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge (FrameCore)

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.Q3T6D

variable {G : Type} [Group G] [Finite G] [FrameCore G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

namespace Std20Frame

theorem sec20X_eq (d : Std20Frame K K' J S R R' W V z t) :
    sec20X (CoreAssembly.conjClass K) z K K' =
      (⨆ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c V) ⊔ (K ⊔ K') := by
  have hx : Hex20 (CoreAssembly.conjClass K) K J W := hexAllF G K K' J S R R' W V z t d
  have hV2 : IsPGroup 2 V := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ d.hV
  have tw : Twin20 (CoreAssembly.conjClass K) K K' z (S : Subgroup G) V :=
    ⟨d.hyp.conjInvariant, d.viol.hzK, d.twins, d.ne, d.hSz, d.hV, d.hVS, hV2⟩
  have hKconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inl rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  have hK'conj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c K' ≤ K ⊔ K' := fun c hc => by
    rcases conjSub_mem_pair d.hyp.conjInvariant d.viol.hzK d.twins (Or.inr rfl) hc with h | h
    · rw [h]; exact le_sup_left
    · rw [h]; exact le_sup_right
  apply le_antisymm
  · have hVc : ∀ c ∈ Subgroup.centralizer ({z} : Set G),
        conjSub c V ≤ (⨆ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c V) ⊔ (K ⊔ K') :=
      fun c hc => le_trans (le_iSup₂ (f := fun c (_ : c ∈ Subgroup.centralizer ({z} : Set G)) =>
        conjSub c V) c hc) le_sup_left
    have hMN : K ⊔ K' ≤ (⨆ c ∈ Subgroup.centralizer ({z} : Set G), conjSub c V) ⊔ (K ⊔ K') :=
      le_sup_right
    unfold sec20X
    refine sup_le (sup_le ?_ (le_trans le_sup_left hMN)) (le_trans le_sup_right hMN)
    refine iSup₂_le fun U hU => ?_
    obtain ⟨hUU, hUC⟩ := hU
    have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet d.late_hΩ hUU
    obtain ⟨c, hc, hcU⟩ := d.exists_conj_le_S hU2 hUC
    have hU1 : conjSub c U ∈ USet (CoreAssembly.conjClass K) :=
      USet.conj d.hyp.conjInvariant hUU c
    have hc' : c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (Subgroup.centralizer _).inv_mem hc
    have hback : U = conjSub c⁻¹ (conjSub c U) := (conjSub_inv_conjSub c U).symm
    rcases d.U_cases hU1 hcU with h | h | h
    · have h1 : conjSub c U ≤ V ⊔ K :=
        h.trans ((d.W_le_V_sup_K hx).trans (sup_le_sup_left inf_le_right V))
      have h2 := conjSub_mono (n := c⁻¹) h1
      rw [conjSub_inv_conjSub, conjSub_sup'] at h2
      exact h2.trans (sup_le (hVc c⁻¹ hc') ((hKconj c⁻¹ hc').trans hMN))
    · have h2 := conjSub_mono (n := c⁻¹) h
      rw [conjSub_inv_conjSub] at h2
      exact h2.trans ((hKconj c⁻¹ hc').trans hMN)
    · have h2 := conjSub_mono (n := c⁻¹) h
      rw [conjSub_inv_conjSub] at h2
      exact h2.trans ((hK'conj c⁻¹ hc').trans hMN)
  · refine sup_le (iSup₂_le fun c hc => ?_) le_sec20X_pair
    exact (conjSub_mono tw.hVX).trans (conjSub_sec20X_le d.hyp.conjInvariant d.viol.hzK d.twins hc)

end Std20Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
