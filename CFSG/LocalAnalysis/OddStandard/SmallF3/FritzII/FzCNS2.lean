module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCNSCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzCK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzRTr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AQ15F
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACorA

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

variable {G : Type} [Group G] [Finite G]

section Helpers


theorem fzc_ns_fpf_Q1 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (p : L41GPh10 t L S x₁ x₂ lam rho) (ht : t ∉ l41Q1 t x₁ x₂ rho) :
    ∀ d ∈ l41Q1 t x₁ x₂ rho, rho * d * rho⁻¹ = d → d = 1 := by
  intro d hdQ₁ hfix
  have hdQ : d ∈ l41Q t x₁ x₂ rho := S4A.q15_Q1_le_Q p.toL41GPh8 hdQ₁
  have hdcent : d ∈ centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * rho = (rho * d * rho⁻¹) * rho := by rw [hfix]
      _ = rho * d := by group
  have hdt : d ∈ zpowers t := by
    rw [← S4A.q14_cent_Q_rho p]
    exact Subgroup.mem_inf.mpr ⟨hdQ, hdcent⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hdt
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · rw [zpow_mul, zpow_two, S4A.t_mul_self p.hyp, one_zpow]
  · exfalso
    apply ht
    have hodd : t ^ (2 * m + 1 : ℤ) = t := by
      rw [zpow_add_one, zpow_mul, zpow_two, S4A.t_mul_self p.hyp, one_zpow, one_mul]
    rw [hodd] at hdQ₁
    exact hdQ₁

theorem fzc_ns_relIndex_M1 {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (p : L41GPh10 t L S x₁ x₂ lam rho)
    (hQ : l41Q t x₁ x₂ rho = l41Q1 t x₁ x₂ rho ⊔ zpowers t)
    (hcard : Nat.card (l41Q1 t x₁ x₂ rho) = 2 ^ 8)
    (htM : t ∉ l41Q1 t x₁ x₂ rho ⊔ zpowers lam) :
    l41Q1 t x₁ x₂ rho ⊔ zpowers lam ≤ l41V1 t x₁ x₂ rho lam ∧
      (l41Q1 t x₁ x₂ rho ⊔ zpowers lam).relIndex (l41V1 t x₁ x₂ rho lam) = 2 := by
  have htV : t ∈ l41V1 t x₁ x₂ rho lam :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hlamV : lam ∈ l41V1 t x₁ x₂ rho lam :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have hMV : l41Q1 t x₁ x₂ rho ⊔ zpowers lam ≤ l41V1 t x₁ x₂ rho lam :=
    sup_le le_sup_left (Subgroup.zpowers_le.mpr hlamV)
  have hV1c := S4A.q15_card_V1 p hQ
  have hinf : l41Q1 t x₁ x₂ rho ⊓ zpowers lam = ⊥ := by
    have h1 : l41Q1 t x₁ x₂ rho ⊓ zpowers lam ≤
        l41Q t x₁ x₂ rho ⊓ closure ({rho, lam} : Set G) :=
      inf_le_inf (S4A.q15_Q1_le_Q p.toL41GPh8)
        (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    exact le_bot_iff.mp (h1.trans (S4A.q14_inf_K_Q p).le)
  have hge : 2 ^ 9 ≤ Nat.card ↥(l41Q1 t x₁ x₂ rho ⊔ zpowers lam) := by
    have hmul := S4A.m11_card_mul_le_sup hinf
    rw [hcard, Nat.card_zpowers, p.toCtx0.wreath.ord_lam] at hmul
    norm_num at hmul ⊢
    exact hmul
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((S4A.q15_V1_pGroup p hQ).to_le hMV)
  have hdvd : 2 ^ k ∣ 2 ^ 10 := by
    rw [← hk, ← hV1c]
    exact Subgroup.card_dvd_of_le hMV
  have hk10 : k ≤ 10 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have hk9 : 9 ≤ k := by
    rw [hk] at hge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hge
  have hk' : k ≠ 10 := by
    rintro rfl
    apply htM
    have heq : l41Q1 t x₁ x₂ rho ⊔ zpowers lam = l41V1 t x₁ x₂ rho lam :=
      Subgroup.eq_of_le_of_card_ge hMV (le_of_eq (by rw [hk, hV1c]))
    rw [heq]
    exact htV
  refine ⟨hMV, ?_⟩
  have hrel := Subgroup.relIndex_mul_card (H := l41Q1 t x₁ x₂ rho ⊔ zpowers lam)
    (K := l41V1 t x₁ x₂ rho lam)
  rw [inf_eq_left.mpr hMV, hk, hV1c, show k = 9 by omega] at hrel
  norm_num at hrel
  omega

end Helpers

theorem fzc_ns2_of
    {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}
    (h : FzCCtx G t L S x₁ x₂ lam rho) (hA : CorAStatement)
    (hV : 2 ∣ (l41V S t x₁ x₂).index) (hV1 : ¬ 2 ∣ (l41V1 t x₁ x₂ rho lam).index) : False := by
  haveI : IsSimpleGroup G := h.simple
  have p14 := fzc_ns_ph14 h hA hV
  have p10 : L41GPh10 t L S x₁ x₂ lam rho := p14.toL41GPh10
  obtain ⟨ht, hQ, hcard, -⟩ := S4A.q15_hs27 p10
  have hV1p : IsPGroup 2 (l41V1 t x₁ x₂ rho lam) := S4A.q15_V1_pGroup p10 hQ
  have hX : IsPGroup 2 (l41Q1 t x₁ x₂ rho) := hV1p.to_le le_sup_left
  have hrX : ∀ x ∈ l41Q1 t x₁ x₂ rho, rho * x * rho⁻¹ ∈ l41Q1 t x₁ x₂ rho := fun x hx =>
    (S4A.q15_normal_Q1 p10).2 rho (S4A.q14_rho_mem_M p14.toL41GPh8) x hx
  have hlX : ∀ x ∈ l41Q1 t x₁ x₂ rho, lam * x * lam⁻¹ ∈ l41Q1 t x₁ x₂ rho := fun x hx =>
    (S4A.q15_normal_Q1 p10).2 lam (S4A.q14_lam_mem_M p14.toL41GPh8) x hx
  have hK : ∀ g : G, g * t * g⁻¹ ∉ l41Q1 t x₁ x₂ rho ⊔ zpowers lam :=
    fzc_core42_of h p14.fusion.not_conj_z hX hrX hlX (fzc_ns_fpf_Q1 p10 ht)
  have htM : t ∉ l41Q1 t x₁ x₂ rho ⊔ zpowers lam := by
    simpa using hK 1
  obtain ⟨hMV, hidx⟩ := fzc_ns_relIndex_M1 p10 hQ hcard htM
  have htV : t ∈ l41V1 t x₁ x₂ rho lam :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  obtain ⟨x, hx⟩ := fzr_transfer (fzr_nonabelian_of_wreath h.ctx.wreath) ⟨hV1p, hV1⟩ hMV hidx
    htV (S4A.t_mul_self h.ctx.hyp)
  exact hK x⁻¹ (by rwa [inv_inv])

section Closing


theorem fzc_ns2 : FzCNS2 := by
  intro G _ _ t L S x₁ x₂ lam rho h hV hV1
  exact fzc_ns2_of h corAStatement_of_certificates hV hV1

end Closing

end CFSG.OddStandard.SmallF3.FritzII
