module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BInst
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCSy3BRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33 CFSG.GH74.GLS.Stage1.Thm6.Sec13

variable {G : Type} [Group G] [Finite G]

theorem fzc_sy3_b_of {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hq : FzCQFacts t S x₁ x₂ lam rho)
    (hr : Nat.card (twoCore t) = 4) (hV : FzSylow (l41V S t x₁ x₂))
    (ht : t ∈ fzP t x₁ x₂ rho) : False := by
  obtain ⟨q, hK, hq4, hqt⟩ := hq.K_four hr
  obtain ⟨a, ha, hat⟩ := fzc_sy3_exists_a h.ctx hq hK hqt ht
  have hs := fzc_sy3_str h.ctx hq hK hq4 hqt ht ha hat
  have hU3 : S4A.RankLE (fzP t x₁ x₂ rho ⊔ zpowers (q * lam)) 3 := fzc_sy3_rank hs
  have hPR : fzP t x₁ x₂ rho ≤ fzR t x₁ x₂ := by
    rw [hq.R_eq_PK]
    exact le_sup_left
  have hqR : q ∈ fzR t x₁ x₂ := by
    rw [hq.R_eq_PK, hK]
    exact mem_sup_right (mem_zpowers q)
  have hlamV : lam ∈ l41V S t x₁ x₂ := by
    rw [hq.V_eq]
    exact mem_sup_right (mem_zpowers lam)
  have hUV : fzP t x₁ x₂ rho ⊔ zpowers (q * lam) ≤ l41V S t x₁ x₂ :=
    sup_le (hPR.trans hq.R_le_V) (zpowers_le.2 (mul_mem (hq.R_le_V hqR) hlamV))
  have hcP : q * lam * (q * lam) ∈ fzP t x₁ x₂ rho := by
    rw [← pow_two, hs.c_sq]
    exact ht
  have hnP : ∀ x ∈ fzP t x₁ x₂ rho, q * lam * x * (q * lam)⁻¹ ∈ fzP t x₁ x₂ rho := by
    intro x hx
    have e : q * lam * x * (q * lam)⁻¹ = q * (lam * x * lam⁻¹) * q⁻¹ := by group
    rw [e]
    exact hq.P_normal_R q hqR _ (hq.lam_norm_P x hx)
  have hcardU : Nat.card ↥(fzP t x₁ x₂ rho ⊔ zpowers (q * lam)) = 256 := by
    rw [card_sup_zpowers_sq hcP hnP hs.c_notin, fzc_sy3_card_P h.ctx hq hK hq4 hqt ht,
      fzc_sy3_card_Wp h.ctx]
  have hcardV : Nat.card (l41V S t x₁ x₂) = 512 := by
    rw [hq.card_V, hq.card_W, hr]
  have hrel : (fzP t x₁ x₂ rho ⊔ zpowers (q * lam)).relIndex (l41V S t x₁ x₂) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := fzP t x₁ x₂ rho ⊔ zpowers (q * lam))
      (K := l41V S t x₁ x₂)
    rw [inf_eq_left.mpr hUV, hcardU, hcardV] at h1
    omega
  have hV4 : S4A.RankLE (l41V S t x₁ x₂) 4 := S4A.RankLE.of_relIndex_two hUV hrel hU3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine h.ass (S4A.sectionalTwoRankLE_of_sylow_rank (hV.1.toSylow hV.2) ?_)
  intro X hX
  exact hV4 X (by simpa using hX)

end CFSG.OddStandard.SmallF3.FritzII
