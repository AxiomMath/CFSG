module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoStart
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoComp

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem sq_mem_szA₁_of_mem_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {r : G}
    (hr : r ∈ u3R₁ L T t) : r ^ 2 ∈ szA₁ (szT₁ L T) :=
  (h.u3RSetup_of_card_sylow hS2).sq_mem_szA₁ hr

theorem comm_mem_szA₁_of_mem_u3R₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {r r' : G}
    (hr : r ∈ u3R₁ L T t) (hr' : r' ∈ u3R₁ L T t) : r * r' * r⁻¹ * r'⁻¹ ∈ szA₁ (szT₁ L T) :=
  (h.u3RSetup_of_card_sylow hS2).comm_mem_szA₁ hr hr'

theorem exists_u3R2_canonical_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ R₂ : Subgroup G, U3R2 G L (szT₁ L T) R₂ t f ∧
      szT₁ L T ⊔ R₂ ⊔ zpowers t = u3R₁ L T t ∧ szA L T t ⊓ R₂ = szA₁ (szT₁ L T) ∧
      u3R₁ L T t ⊓ centralizer (szT₁ L T : Set G) = R₂ ⊔ zpowers t ∧
      (∀ B : Subgroup G, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
        B ≤ u3R₁ L T t ⊓ centralizer (szT₁ L T : Set G) → Nat.card B = (2 ^ f) ^ 2 → B = R₂) ∧
      normalizer (szA L T t : Set G) ≤
        normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (szA L T t : Set G) ≤ normalizer (R₂ : Set G) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (T ⊔ R₂) (normalizer (szA L T t : Set G)) := by
  have hS := h.u3RSetup_of_card_sylow hS2
  obtain ⟨d, k, -, hd⟩ := h.exists_u3RTorus_of_card_sylow hS2
  obtain ⟨R₂, hc⟩ := hS.exists_comp hd
  have hNR₁ : normalizer (szA L T t : Set G) ≤ normalizer (u3R₁ L T t : Set G) := by
    intro n hn
    refine mem_normalizer_iff.mpr fun r => ⟨fun hr => h.conj_mem_u3R₁_of_card_sylow hS2 hn hr,
      fun hr => ?_⟩
    have := h.conj_mem_u3R₁_of_card_sylow hS2 (inv_mem hn) hr
    rwa [show n⁻¹ * (n * r * n⁻¹) * n⁻¹⁻¹ = r by group] at this
  have hNT₁ := h.normalizer_szA_le_of_card_sylow hS2
  have hsup := hc.sup_eq
  have hdt := hd.comm_t
  have htinv : t⁻¹ = t := hS.t_inv
  have hU3R2 : U3R2 G L (szT₁ L T) R₂ t f := by
    refine ⟨hc.comm hS hd, hc.card hS, hc.le, hc.inf_T₁, fun x hx r hr => hc.commute_T₁ hS hd hx hr,
      fun r hr => hc.conj_mem_R₁ hS hS.t_mem_R₁ hr, fun b hb => ?_, hc.rho_ker hS, hS.t_sq,
      fun x hx => mem_centralizer_iff.mp hS.t_comm x hx, hS.sq_A₁,
      fun r hr => hS.sq_mem_szA₁ (hc.le_R₁ hr), fun r hr => ?_, d, hdt, ?_, hd.mem_normalizer_T₁,
      hd.trans⟩
    · obtain ⟨r, hr, hrb⟩ := hc.rho_surj hS hb
      refine ⟨r, hr, ?_⟩
      rw [← hrb, htinv]
    · have := hS.rho_mem r (hc.le_R₁ hr)
      rwa [htinv] at this
    · exact mem_normalizer_iff.mpr fun x => ⟨fun hx => hc.conj_mem d (mem_zpowers d) x hx,
        fun hx => by
          have := hc.conj_mem d⁻¹ (inv_mem (mem_zpowers d)) _ hx
          rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at this⟩
  have hTR : T ⊔ R₂ = T ⊔ u3R₁ L T t := by
    obtain ⟨htT, -⟩ := h.start_of_card_sylow hS2
    apply le_antisymm
    · exact sup_le_sup_left hc.le_R₁ _
    · refine sup_le le_sup_left ?_
      rw [← hsup]
      exact sup_le (sup_le ((szT₁_le_left L T).trans le_sup_left) le_sup_right)
        (zpowers_le.mpr (mem_sup_left htT))
  have hAR₂ : szA L T t ⊓ R₂ = szA₁ (szT₁ L T) := by
    apply le_antisymm
    · rw [← hc.inf]
      exact inf_le_inf_right _ (sup_le_sup_right (szA₁_le _) _)
    · exact le_inf (szA₁_le_szA L T t) hc.le
  refine ⟨R₂, hU3R2, hsup, hAR₂, hc.inf_centralizer_T₁ hS hd, fun B hBc hB hBcard =>
    hc.eq_of_comm hS hd hBc hB hBcard, ?_, fun n hn => hc.mem_normalizer hS hd (hNR₁ hn) (hNT₁ hn),
    ?_⟩
  · rw [hsup]
    exact hNR₁
  · rw [hTR]
    exact h.isSylowOf_sup_u3R₁_of_card_sylow hS2

theorem exists_u3R2_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ R₂ : Subgroup G, U3R2 G L (szT₁ L T) R₂ t f ∧
      normalizer (szA L T t : Set G) ≤
        normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (szA L T t : Set G) ≤ normalizer (R₂ : Set G) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 (T ⊔ R₂) (normalizer (szA L T t : Set G)) := by
  obtain ⟨R₂, hR₂, -, -, -, -, hN, hN', hS⟩ := h.exists_u3R2_canonical_of_card_sylow hS2
  exact ⟨R₂, hR₂, hN, hN', hS⟩

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
