module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGlobalSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

namespace U3C1OuterLevelData

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T R₂ D : Subgroup G} {d : G} {V U U₁ : Subgroup G}

theorem norm_exists_conj (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1)
    (hL : U3C1OuterLevelData G L f t T D V U U₁ 1) (hμV : ¬ U₁ ≤ centralizer (V : Set G))
    {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1) (hwS : w ∉ szT₁ L T ⊔ zpowers t)
    (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {P : Subgroup G} (hP2 : IsPGroup 2 P) (hSP : U ⊔ T ≤ P)
    {g : G} (hgN : g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)) (hgP : g ∈ P)
    (hgS : g ∉ U ⊔ T) : ∃ c ∈ szT₁ L T, c * (g * t * g⁻¹) * c⁻¹ = w := by
  classical
  obtain ⟨K, _, _, _, v, μ, hK, hc, hμ⟩ := hS.exists_coords
  have h := hS.start
  have hS2 := hS.card_sylow
  obtain ⟨htT, -, -, -, -, -, -⟩ := h.start_of_card_sylow hS2
  have htt : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hT₁U₁ : szT₁ L T ≤ U₁ := le_sup_left.trans hL.sup_le_U₁
  have hgT : ∀ s ∈ T, g * s * g⁻¹ ∈ U ⊔ T := fun s hs =>
    (mem_normalizer_iff.mp hgN s).mp (mem_sup_right hs)
  have hx2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, htt, mul_one,
      mul_inv_cancel]
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (h.le hwT)
  have htwT : t * w ∈ T := mul_mem htT hwT
  have htw2 : (t * w) ^ 2 = 1 := by
    rw [Commute.mul_pow hwt.symm 2, h.sq_eq_one, hw2, one_mul]
  have htwS : t * w ∉ szT₁ L T ⊔ zpowers t := fun hm => hwS (by
    rw [show w = t⁻¹ * (t * w) by group]
    exact mul_mem (inv_mem (mem_sup_right (mem_zpowers t))) hm)
  have htwV : ∀ r ∈ V, t * w * r * (t * w)⁻¹ = r⁻¹ := fun r hr => by
    rw [show t * w * r * (t * w)⁻¹ = t * (w * r * w⁻¹) * t⁻¹ by group, hwV r hr]
    exact hS.conf.inv r hr
  rcases hL.muOne_classify hS (hgT t htT) hx2 with h1 | h1 | ⟨w', hw'T, hw'2, hw'S, h1⟩
  · exact (hL.muOne_false_of_conj_mem_U₁ hS hc hμV hK hμ hgT h1).elim
  · exact (hgS (hL.muOne_mem_sup_of_conj hS hc hμV hK hμ hP2 hSP hgP h1)).elim
  · rcases hL.muOne_dichotomy hS hc hμV hK hμ hw'T hw'2 hw'S with hcen | hinv
    ·
      have hM : w' * w⁻¹ ∈ szT₁ L T ⊔ zpowers t :=
        h.mul_inv_mem_of_sq_mem_of_card_sylow hS2 hw'T hwT (by rw [hw'2]; exact one_mem _)
          (by rw [hw2]; exact one_mem _) hw'S hwS
      obtain ⟨a, ha, z, hz, haz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hM
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hz with hz1 | hz1
      · rw [hz1, mul_one] at haz
        refine hL.muOneCent_exists_conj_eq hS hc hμV hK hμ hwT hw2 hwS hwV hgT ?_
        rw [show g * t * g⁻¹ * w⁻¹ = (g * t * g⁻¹ * w'⁻¹) * (w' * w⁻¹) by group, ← haz]
        exact mul_mem h1 (hT₁U₁ ha)
      · refine (hL.muOne_false_of_conj_mem_inv hS hc hμV hK hμ htwT htw2 htwS htwV hgT ?_).elim
        have e : g * t * g⁻¹ * (t * w)⁻¹ = (g * t * g⁻¹ * w'⁻¹) * (w' * w⁻¹ * t⁻¹) := by group
        rw [e, ← haz, hz1, show a * t * t⁻¹ = a by group]
        exact mul_mem h1 (hT₁U₁ ha)
    · exact (hL.muOne_false_of_conj_mem_inv hS hc hμV hK hμ hw'T hw'2 hw'S hinv hgT h1).elim

theorem norm_not_mem_of_conj_eq
    (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
    {w : G} (hwT : w ∈ T) (hwS : w ∉ szT₁ L T ⊔ zpowers t) {g : G} (hg : g * t * g⁻¹ = w) :
    g ∉ U ⊔ T := by
  intro hgS
  have htT := (hS.start.start_of_card_sylow hS.card_sylow).1
  have h1 := hL.muOne_comm_mem_U₁ hS g hgS t (mem_sup_right htT)
  rw [hg] at h1
  have h2 : w * t⁻¹ ∈ szT₁ L T := hL.muOne_mem_T₁_of_mem_T hS h1 (mul_mem hwT (inv_mem htT))
  apply hwS
  rw [show w = w * t⁻¹ * t by group]
  exact mul_mem (mem_sup_left h2) (mem_sup_right (mem_zpowers t))

theorem norm_mem_T_of_commute (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hTP : T ≤ P) {z : G} (hzP : z ∈ P) (hz : z * t = t * z) : z ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsyl : IsSylowOf 2 T (centralizer ({t} : Set G)) := by
    obtain ⟨P₀, hP₀⟩ := hS.start.sylow
    exact ⟨P₀, by rw [hP₀, subgroupOf_map_subtype, inf_eq_left.mpr hS.start.le]⟩
  have hH : T ⊔ zpowers z ≤ centralizer ({t} : Set G) :=
    sup_le hS.start.le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hz))
  have hHP : T ⊔ zpowers z ≤ P := sup_le hTP (zpowers_le.mpr hzP)
  have heq := hTsyl.eq_of_le le_sup_left hH (hP2.to_le hHP)
  rw [← heq]
  exact mem_sup_right (mem_zpowers _)

theorem norm_exists_swap
    (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
    (hμV : ¬ U₁ ≤ centralizer (V : Set G)) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hSP : U ⊔ T ≤ P) {g : G}
    (hgN : g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)) (hgP : g ∈ P) (hg : g * t * g⁻¹ = w) :
    ∃ c ∈ szT₁ L T, g * c⁻¹ * t * (g * c⁻¹)⁻¹ = w ∧ g * c⁻¹ * w * (g * c⁻¹)⁻¹ = t := by
  have hgS := hL.norm_not_mem_of_conj_eq hS hwT hwS hg
  have hgS' : g⁻¹ ∉ U ⊔ T := fun h' => hgS (by simpa using inv_mem h')
  obtain ⟨c, hcT, hc⟩ :=
    hL.norm_exists_conj hS hμV hwT hw2 hwS hwV hP2 hSP (inv_mem hgN) (inv_mem hgP) hgS'
  have hct : c * t = t * c := mem_centralizer_iff.mp hS.start.mem_centralizer_szT₁ c hcT
  refine ⟨c, hcT, ?_, ?_⟩
  · calc g * c⁻¹ * t * (g * c⁻¹)⁻¹ = g * (c⁻¹ * (t * c)) * g⁻¹ := by group
      _ = g * (c⁻¹ * (c * t)) * g⁻¹ := by rw [hct]
      _ = w := by rw [← hg]; group
  · rw [← hc]
    group

theorem norm_swap_facts
    (hS : U3C1OuterStepHyp G L f t T R₂ D d V 1) (hL : U3C1OuterLevelData G L f t T D V U U₁ 1)
    (hμV : ¬ U₁ ≤ centralizer (V : Set G)) {w : G} (hwT : w ∈ T) (hw2 : w ^ 2 = 1)
    (hwS : w ∉ szT₁ L T ⊔ zpowers t) (hwV : ∀ r ∈ V, w * r * w⁻¹ = r) {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hSP : U ⊔ T ≤ P) {s : G}
    (hsN : s ∈ normalizer ((U ⊔ T : Subgroup G) : Set G)) (hsP : s ∈ P)
    (hst : s * t * s⁻¹ = w) (hsw : s * w * s⁻¹ = t) :
    s ∉ U ⊔ T ∧ s ^ 2 ∈ T ∧ s * (t * w) * s⁻¹ = t * w ∧
      ∀ g ∈ normalizer ((U ⊔ T : Subgroup G) : Set G), g ∈ P → g ∈ U ⊔ T ∨ g * s⁻¹ ∈ U ⊔ T := by
  have hTP : T ≤ P := le_sup_right.trans hSP
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.mp (hS.start.le hwT)
  refine ⟨hL.norm_not_mem_of_conj_eq hS hwT hwS hst, ?_, ?_, ?_⟩
  · refine norm_mem_T_of_commute hS hP2 hTP (pow_mem hsP 2) ?_
    have e : s ^ 2 * t * (s ^ 2)⁻¹ = t := by
      rw [show s ^ 2 * t * (s ^ 2)⁻¹ = s * (s * t * s⁻¹) * s⁻¹ by rw [sq]; group, hst, hsw]
    calc s ^ 2 * t = s ^ 2 * t * (s ^ 2)⁻¹ * s ^ 2 := by group
      _ = t * s ^ 2 := by rw [e]
  · rw [show s * (t * w) * s⁻¹ = (s * t * s⁻¹) * (s * w * s⁻¹) by group, hst, hsw, hwt]
  · intro g hgN hgP
    by_cases hgS : g ∈ U ⊔ T
    · exact Or.inl hgS
    right
    obtain ⟨c, hcT, hc⟩ := hL.norm_exists_conj hS hμV hwT hw2 hwS hwV hP2 hSP hgN hgP hgS
    have hcS : c ∈ U ⊔ T := mem_sup_left (hL.U₁_le ((le_sup_left.trans hL.sup_le_U₁) hcT))
    set z := s⁻¹ * c * g with hz
    have hzt : z * t = t * z := by
      have e : z * t * z⁻¹ = t := by
        rw [hz, show s⁻¹ * c * g * t * (s⁻¹ * c * g)⁻¹ = s⁻¹ * (c * (g * t * g⁻¹) * c⁻¹) * s by
          group, hc, ← hst]
        group
      calc z * t = z * t * z⁻¹ * z := by group
        _ = t * z := by rw [e]
    have hzT : z ∈ T := norm_mem_T_of_commute hS hP2 hTP
      (mul_mem (mul_mem (inv_mem hsP) (hSP hcS)) hgP) hzt
    have e : g * s⁻¹ = c⁻¹ * (s * z * s⁻¹) := by rw [hz]; group
    rw [e]
    exact mul_mem (inv_mem hcS) ((mem_normalizer_iff.mp hsN z).mp (mem_sup_right hzT))

end U3C1OuterLevelData

@[expose] def U3C1OuterMuOneSwapInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f : ℕ) (t : G) (T R₂ D : Subgroup G) (d : G)
    (V U U₁ : Subgroup G), U3C1OuterStepHyp G L f t T R₂ D d V 1 →
    U3C1OuterLevelData G L f t T D V U U₁ 1 → ¬ U₁ ≤ centralizer (V : Set G) →
    (¬ ∃ S : Sylow 2 G, (S : Subgroup G) = U ⊔ T) →
    ∀ w ∈ T, w ^ 2 = 1 → w ∉ szT₁ L T ⊔ zpowers t → (∀ r ∈ V, w * r * w⁻¹ = r) →
      (∀ s : G, s ^ 2 ≠ w) → ∀ s ∈ normalizer ((U ⊔ T : Subgroup G) : Set G),
        (∃ P : Subgroup G, IsPGroup 2 P ∧ U ⊔ T ≤ P ∧ s ∈ P) → s * t * s⁻¹ = w →
          s * w * s⁻¹ ≠ t

theorem u3C1OuterMuOneNormInput_of_swap
    (hW : U3C1OuterMuOneSwapInput) : U3C1OuterMuOneNormInput := by
  intro G _ _ L f t T R₂ D d V U U₁ hS hL hμV hnS w hwT hw2 hwS hwV hsq g hgN hP hg
  obtain ⟨P, hP2, hSP, hgP⟩ := hP
  obtain ⟨c, hcT, h1, h2⟩ := hL.norm_exists_swap hS hμV hwT hw2 hwS hwV hP2 hSP hgN hgP hg
  have hcS : c ∈ U ⊔ T := mem_sup_left (hL.U₁_le ((le_sup_left.trans hL.sup_le_U₁) hcT))
  exact hW G L f t T R₂ D d V U U₁ hS hL hμV hnS w hwT hw2 hwS hwV hsq (g * c⁻¹)
    (mul_mem hgN (Subgroup.le_normalizer (inv_mem hcS))) ⟨P, hP2, hSP, mul_mem hgP (hSP (inv_mem hcS))⟩
    h1 h2

end CFSG.SeitzReduction.RankOne
