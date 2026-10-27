module

public import CFSG.GH74.Uniqueness.SU.KI6BComp

public section

namespace CFSG.GH74.Uniqueness.SU.K.R6

open Subgroup CFSG CFSG.Blueprint CFSG.ProperTwoGeneratedCore CFSG.GH74.Uniqueness.SU.K.R3
open scoped Pointwise commutatorElement
open CFSG.LocalCores

variable {H : Type} [Group H] [Finite H] {T : Sylow 2 H} {H₀ : Subgroup H}

theorem sq_eq_t_of_orderOf_four (F : KI6BFacts) (h : Cfg H T H₀) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K) (hr : Open.pRank 2 K ≤ 1)
    {y : H} (hyK : y ∈ K) (hy4 : orderOf y = 4) : y * y = t := by
  apply (component_data F h htc ht2 hK hr).2.1 _ (K.mul_mem hyK hyK)
  have : orderOf (y * y) = 2 := by
    rw [← pow_two, orderOf_pow' _ (by norm_num : (2:ℕ) ≠ 0), hy4]
    norm_num
  exact this

theorem two_le_pRank_of_order_four (F : KI6BFacts) (h : Cfg H T H₀) {t : H}
    (htc : t ∈ center H) (ht2 : orderOf t = 2) {K : Subgroup H} (hK : IsComponent K)
    (hr : Open.pRank 2 K ≤ 1) {y x : H} (hyK : y ∈ K) (hy4 : orderOf y = 4)
    (hcomm : y * x = x * y) (hx : x ∉ zpowers t) (hx2 : ∃ n : ℕ, x ^ (2 ^ n) = 1)
    (hint : ∀ g : H, g ∈ zpowers y → g ∈ zpowers x → g ∈ zpowers t) :
    2 ≤ Open.pRank 2 (zpowers y ⊔ zpowers x) :=
  two_le_pRank_sup_zpowers (mul_self_eq_one_of_orderOf_two ht2) hy4
    (sq_eq_t_of_orderOf_four F h htc ht2 hK hr hyK hy4) hcomm hx hx2 hint

omit [Finite H] in
theorem commute_of_commutator_eq_bot {A B : Subgroup H} (h : ⁅A, B⁆ = ⊥) :
    ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := by
  intro a ha b hb
  have h1 : ⁅a, b⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [h] at h1
  have h2 : a * b * a⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp h1
  calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [h2, one_mul]

theorem components_commute {K K' : Subgroup H} (hK : IsComponent K) (hK' : IsComponent K')
    (hne : K ≠ K') : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := by
  rcases distinct_components_commute hK hK' with h1 | h1
  · exact absurd h1 hne
  · exact commute_of_commutator_eq_bot h1

theorem exists_component (h : Cfg H T H₀) : ∃ K : Subgroup H, IsComponent K := by
  by_contra hcon
  push Not at hcon
  exact h.layer_ne_bot (layer_eq_bot_of_forall hcon)

omit [Finite H] in
theorem exists_two_pow_eq_one_of_orderOf_four {y : H} (h4 : orderOf y = 4) :
    ∃ n : ℕ, y ^ (2 ^ n) = 1 :=
  ⟨2, by have := pow_orderOf_eq_one y; rwa [h4] at this⟩

omit [Finite H] in
theorem not_mem_zpowers_of_orderOf_four {y t : H} (ht2 : orderOf t = 2) (hy4 : orderOf y = 4) :
    y ∉ zpowers t := by
  intro hmem
  have ht2' : t * t = 1 := mul_self_eq_one_of_orderOf_two ht2
  rcases LemmaYAux.eq_one_or_eq_of_mem_zpowers ht2' hmem with h1 | h1
  · rw [h1, orderOf_one] at hy4; omega
  · have : orderOf y ∣ 2 := by
      rw [h1]; exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht2')
    rw [hy4] at this; omega

theorem two_le_pRank_generalizedFitting (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) : 2 ≤ Open.pRank 2 (generalizedFitting H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  have hF1 : Open.pRank 2 (generalizedFitting H) ≤ 1 := by omega
  obtain ⟨K, hK⟩ := exists_component h
  have hdata := component_data F h htc ht2 hK (hr K hK)
  obtain ⟨y, hyK, hy4⟩ := hdata.2.2.2
  have hlayerF : layer H ≤ generalizedFitting H := le_sup_right
  have hfitF : fittingSubgroup H ≤ generalizedFitting H := le_sup_left
  have hfit : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 h.odd
  have huniq : ∀ K' : Subgroup H, IsComponent K' → K' = K := by
    intro K' hK'
    by_contra hne
    obtain ⟨y', hy'K', hy'4⟩ := (component_data F h htc ht2 hK' (hr K' hK')).2.2.2
    have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
      components_commute hK hK' (fun h' => hne h'.symm)
    have hrank := two_le_pRank_of_order_four F h htc ht2 hK (hr K hK) hyK hy4
      (hcomm y hyK y' hy'K') (not_mem_zpowers_of_orderOf_four ht2 hy'4)
      (exists_two_pow_eq_one_of_orderOf_four hy'4)
      (fun g hg1 hg2 => hdata.2.2.1 g (Subgroup.zpowers_le.mpr hyK hg1)
        (fun k hk => (hcomm k hk g (Subgroup.zpowers_le.mpr hy'K' hg2)).symm))
    have hle : zpowers y ⊔ zpowers y' ≤ generalizedFitting H :=
      sup_le (Subgroup.zpowers_le.mpr (hlayerF (component_le_layer hK hyK)))
        (Subgroup.zpowers_le.mpr (hlayerF (component_le_layer hK' hy'K')))
    have := (hrank.trans (SU1.pRank_mono (by norm_num) hle)).trans hF1
    omega
  have hlayer : layer H = K :=
    le_antisymm (sSup_le fun L hL => (huniq L hL).le) (component_le_layer hK)
  have hQK : pCore 2 H ≤ K := by
    intro w hw
    by_contra hwK
    have hcomm : y * w = w * y := (h.pCore_comm_layer hw (component_le_layer hK hyK)).symm
    have htK : t ∈ K := hdata.1
    have hrank := two_le_pRank_of_order_four F h htc ht2 hK (hr K hK) hyK hy4 hcomm
      (fun hmem => hwK (Subgroup.zpowers_le.mpr htK hmem))
      (by
        obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨w, hw⟩
        exact ⟨n, congrArg Subtype.val hn⟩)
      (fun g hg1 hg2 => h.pCore_inf_component_le F htc ht2 hK (hr K hK)
        ((Subgroup.zpowers_le.mpr hw) hg2) (Subgroup.zpowers_le.mpr hyK hg1))
    have hle : zpowers y ⊔ zpowers w ≤ generalizedFitting H :=
      sup_le (Subgroup.zpowers_le.mpr (hlayerF (component_le_layer hK hyK)))
        (Subgroup.zpowers_le.mpr (hfitF (hfit ▸ hw)))
    have := (hrank.trans (SU1.pRank_mono (by norm_num) hle)).trans hF1
    omega
  have hFK : generalizedFitting H = K := by
    apply le_antisymm
    · exact sup_le (hfit ▸ hQK) hlayer.le
    · exact hlayer ▸ hlayerF
  have hKnorm : K.Normal := by
    have := layer_characteristic (G := H)
    rw [← hlayer]
    infer_instance
  have hC : centralizer (K : Set H) ≤ K := by
    have := centralizer_generalizedFitting_le H
    rwa [hFK] at this
  have hrk : CFSG.pRank 2 ↥K ≤ 1 := (pRank_coe_eq K).trans_le (hr K hK)
  obtain ⟨U, hU4, hU2, hUK⟩ := exists_four_group_inf_eq_bot K h.rank (hr K hK)
  exact F.noOuter H K hKnorm hK.1 hrk (h.isPGroup_center_component hK) hC U hU4 hU2 hUK

omit [Finite H] in
theorem generalizedFitting_normal : (generalizedFitting H).Normal := by
  have := generalized_fitting_characteristic (G := H)
  infer_instance

theorem Cfg.generalizedFitting_sup_eq_top (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) : generalizedFitting H ⊔ H₀ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn : (generalizedFitting H).Normal := generalizedFitting_normal
  let P : Sylow 2 ↥(generalizedFitting H) :=
    CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal T (generalizedFitting H)
  have hPle : ((P : Subgroup ↥(generalizedFitting H)).map (generalizedFitting H).subtype) ≤
      (T : Subgroup H) := by
    rw [CFSG.BenderSuzuki.External.hallSylowSubgroupOfNormal_coe]
    exact Subgroup.map_comap_le _ _
  have hrank : 2 ≤ Open.pRank 2
      ((P : Subgroup ↥(generalizedFitting H)).map (generalizedFitting H).subtype) := by
    rw [sylow_image_two_rank_eq]
    exact two_le_pRank_generalizedFitting F h hr htc ht2
  have hN := two_generated_core_subgroup_normalizer_le T H₀ h.sylow_le h.gamma _
    (hPle.trans h.sylow_le) hrank
  have htop := Sylow.normalizer_sup_eq_top P
  rw [eq_top_iff, ← htop, sup_comm (generalizedFitting H)]
  exact sup_le_sup_right hN _

theorem Cfg.generalizedFitting_le_normalizer (h : Cfg H T H₀) {K : Subgroup H}
    (hK : IsComponent K) : generalizedFitting H ≤ normalizer (K : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfit : fittingSubgroup H = pCore 2 H := Fitting_eq_pcore H 2 h.odd
  refine sup_le ?_ (layer_le_normalizer hK)
  rw [hfit]
  intro q hq
  apply Subgroup.centralizer_le_normalizer (K : Set H)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (h.pCore_comm_layer hq (component_le_layer hK hx)).symm

omit [Finite H] in
theorem Cfg.pCore_le_T (T : Sylow 2 H) : pCore 2 H ≤ (T : Subgroup H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.Glauberman.pCore_le_sylow T

omit [Finite H] in
theorem Cfg.exists_mul_eq (hFH : generalizedFitting H ⊔ H₀ = ⊤) (g : H) :
    ∃ h₀ ∈ H₀, ∃ f ∈ generalizedFitting H, g = h₀ * f := by
  have hFn : (generalizedFitting H).Normal := generalizedFitting_normal
  have hg : g ∈ H₀ ⊔ generalizedFitting H := by rw [sup_comm, hFH]; trivial
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg
  obtain ⟨h₀, hh₀, f, hf, hgf⟩ := Set.mem_mul.mp hg
  exact ⟨h₀, hh₀, f, hf, hgf.symm⟩

theorem Cfg.exists_component_not_le (F : KI6BFacts) (h : Cfg H T H₀)
    (hr : ∀ L : Subgroup H, IsComponent L → Open.pRank 2 L ≤ 1) {t : H} (htc : t ∈ center H)
    (ht2 : orderOf t = 2) : ∃ K : Subgroup H, IsComponent K ∧ ¬ K ≤ H₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hlayer : layer H ≤ H₀ := sSup_le fun L hL => hcon L hL
  have hfit : fittingSubgroup H ≤ H₀ := by
    rw [Fitting_eq_pcore H 2 h.odd]
    exact (Cfg.pCore_le_T T).trans h.sylow_le
  apply h.ne
  rw [eq_top_iff, ← h.generalizedFitting_sup_eq_top F hr htc ht2]
  exact sup_le (sup_le hfit hlayer) le_rfl

theorem Cfg.conj_not_le (h : Cfg H T H₀) (hFH : generalizedFitting H ⊔ H₀ = ⊤)
    {K : Subgroup H} (hK : IsComponent K) (hKH : ¬ K ≤ H₀) (g : H) :
    ¬ ∀ x ∈ K, g * x * g⁻¹ ∈ H₀ := by
  intro hall
  apply hKH
  obtain ⟨h₀, hh₀, f, hf, rfl⟩ := Cfg.exists_mul_eq hFH g
  have hfn : f ∈ normalizer (K : Set H) := h.generalizedFitting_le_normalizer hK hf
  intro x hx
  have hx' : f⁻¹ * x * f ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (K : Set H)).inv_mem hfn)) x
    simpa using this.mp hx
  have h1 := hall _ hx'
  have h2 : h₀ * f * (f⁻¹ * x * f) * (h₀ * f)⁻¹ = h₀ * x * h₀⁻¹ := by group
  rw [h2] at h1
  have h3 : h₀⁻¹ * (h₀ * x * h₀⁻¹) * h₀ ∈ H₀ := H₀.mul_mem (H₀.mul_mem (H₀.inv_mem hh₀) h1) hh₀
  have h4 : h₀⁻¹ * (h₀ * x * h₀⁻¹) * h₀ = x := by group
  rwa [h4] at h3

end CFSG.GH74.Uniqueness.SU.K.R6
