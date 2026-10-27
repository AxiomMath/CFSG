module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRTr
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.S3Gen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCQAss
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSteps

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type} [Group G] [Finite G]

theorem fzc_sy1_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hr : Nat.card (twoCore t) = 2) (hV : FzSylow (l41V S t x₁ x₂))
    (ht : t ∉ fzP t x₁ x₂ rho) : False := by
  haveI := h.simple
  have hctx := h.ctx
  have hlam2 : lam * lam = 1 := by
    have h1 := pow_orderOf_eq_one lam
    rw [hctx.wreath.ord_lam] at h1
    simpa [pow_two] using h1
  have hPR : fzP t x₁ x₂ rho ≤ fzR t x₁ x₂ := by
    rw [hq.R_eq_PK]
    exact le_sup_left
  have hKR : twoCore t ≤ fzR t x₁ x₂ := by
    rw [hq.R_eq_PK]
    exact le_sup_right
  have hRV : fzR t x₁ x₂ ≤ l41V S t x₁ x₂ := hq.R_le_V
  have hlamV : lam ∈ l41V S t x₁ x₂ := by
    rw [hq.V_eq]
    exact mem_sup_right (mem_zpowers lam)
  have hlamP : lam ∉ fzP t x₁ x₂ rho := fun hl => hq.lam_not_mem_R (hPR hl)
  have hl2P : lam * lam ∈ fzP t x₁ x₂ rho := by
    rw [hlam2]
    exact one_mem _
  have hW : Nat.card (ctxW t x₁ x₂) = 32 := by rw [hq.card_W, hr]
  have hP : Nat.card (fzP t x₁ x₂ rho) = 64 := by
    have h1 := hq.card_P_of_not_mem ht
    rw [hr, hq.card_R, hW] at h1
    omega
  have hM : Nat.card ↥(fzP t x₁ x₂ rho ⊔ zpowers lam) = 128 := by
    rw [card_sup_zpowers_sq hl2P hq.lam_norm_P hlamP, hP]
  have hVc : Nat.card (l41V S t x₁ x₂) = 256 := by rw [hq.card_V, hW]
  have hMV : fzP t x₁ x₂ rho ⊔ zpowers lam ≤ l41V S t x₁ x₂ :=
    sup_le (hPR.trans hRV) (zpowers_le.mpr hlamV)
  have hrel : (fzP t x₁ x₂ rho ⊔ zpowers lam).relIndex (l41V S t x₁ x₂) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := fzP t x₁ x₂ rho ⊔ zpowers lam)
      (K := l41V S t x₁ x₂)
    rw [inf_eq_left.mpr hMV, hM, hVc] at h1
    omega
  have htV : t ∈ l41V S t x₁ x₂ := hRV (hKR hctx.hyp.mem_twoCore)
  have htt : t * t = 1 := S4A.t_mul_self hctx.hyp
  obtain ⟨x, hx⟩ :=
    fzr_transfer (fzr_nonabelian_of_wreath hctx.wreath) hV hMV hrel htV htt
  have hP2 : IsPGroup 2 (fzP t x₁ x₂ rho) := hV.1.to_le (hPR.trans hRV)
  refine fzc_core42_of h hq.not_conj_z hP2 hq.rho_norm_P hq.lam_norm_P
    (hq.P_fpf_of_not_mem ht) x⁻¹ ?_
  simpa using hx

theorem fzc_sy1 :
    FzCSy1 :=
  fun _ _ _ _ _ _ _ _ _ _ h hr hV ht => fzc_sy1_of h (fzc_qfacts_of_steps (fzc_steps h)) hr hV ht

end CFSG.OddStandard.SmallF3.FritzII
