module

public import CFSG.Goldschmidt75.Sig31

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G] {S₁ S₂ : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_mul_self (hc : S₁ ≤ centralizer (S₂ : Set G)) (hd : S₁ ⊓ S₂ = ⊥) {t : G}
    (ht : t ∈ S₁ ⊔ S₂) (ht2 : t * t = 1) :
    ∃ t₁ ∈ S₁, ∃ t₂ ∈ S₂, t = t₁ * t₂ ∧ t₁ * t₁ = 1 ∧ t₂ * t₂ = 1 := by
  have hn : S₁ ≤ normalizer (S₂ : Set G) := hc.trans (centralizer_le_normalizer _)
  have h : t ∈ ((S₁ ⊔ S₂ : Subgroup G) : Set G) := ht
  rw [coe_mul_of_left_le_normalizer_right _ _ hn] at h
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := h
  have hcomm : t₁ * t₂ = t₂ * t₁ := (mem_centralizer_iff.mp (hc ht₁) t₂ ht₂).symm
  have h1 : t₁ * t₁ = (t₂ * t₂)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc t₁ * t₁ * (t₂ * t₂) = t₁ * (t₁ * t₂) * t₂ := by group
      _ = t₁ * (t₂ * t₁) * t₂ := by rw [hcomm]
      _ = t₁ * t₂ * (t₁ * t₂) := by group
      _ = 1 := ht2
  have hmem : t₁ * t₁ ∈ S₁ ⊓ S₂ :=
    Subgroup.mem_inf.mpr ⟨mul_mem ht₁ ht₁, by rw [h1]; exact inv_mem (mul_mem ht₂ ht₂)⟩
  rw [hd, mem_bot] at hmem
  refine ⟨t₁, ht₁, t₂, ht₂, rfl, hmem, ?_⟩
  rw [hmem] at h1
  exact inv_eq_one.mp h1.symm

omit [Finite G] in
theorem ne_one_of_orderOf_eq_two {t : G} (ht : orderOf t = 2) : t ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at ht
  exact absurd ht (by norm_num)

theorem exists_W (hS₁ : IsPGroup 2 S₁) (hS₂ : IsPGroup 2 S₂)
    (hc : S₁ ≤ centralizer (S₂ : Set G)) (hd : S₁ ⊓ S₂ = ⊥) (hsep : CoreSep S₁ S₂)
    (hm₁ : ∃ V ≤ S₁, IsKleinFour V) (hm₂ : ∃ V ≤ S₂, IsKleinFour V) :
    ∃ W : Subgroup G, Odd (Nat.card W) ∧
      (∀ B₁ B₂ : Subgroup G, B₁ ≤ S₁ → B₂ ≤ S₂ → B₁ ≠ ⊥ → B₂ ≠ ⊥ →
        W ∈ NSet (B₁ ⊔ B₂) ∧ ∀ X ∈ NSet (B₁ ⊔ B₂), X ≤ W) ∧
      (∀ t₁ ∈ S₁, orderOf t₁ = 2 → ∀ t₂ ∈ S₂, orderOf t₂ = 2 →
        ⁅oddCent t₁, zpowers t₂⁆ ≤ W ∧ ⁅oddCent t₂, zpowers t₁⁆ ≤ W) := by
  obtain ⟨V₁, hV₁S, hV₁⟩ := hm₁
  obtain ⟨V₂, hV₂S, hV₂⟩ := hm₂
  have hne : ∀ {S V : Subgroup G}, V ≤ S → IsKleinFour V → S ≠ ⊥ := by
    intro S V hVS hV h
    obtain ⟨v, hv, hv1, -⟩ := exists_mem_ne_of_isKleinFour hV 1
    exact hv1 (by have := hVS hv; rw [h] at this; exact mem_bot.mp this)
  obtain ⟨z₁, hz₁S, hz₁2, hz₁c⟩ := exists_central_involution_of_isPGroup hS₁ (hne hV₁S hV₁)
  obtain ⟨z₂, hz₂S, hz₂2, hz₂c⟩ := exists_central_involution_of_isPGroup hS₂ (hne hV₂S hV₂)
  obtain ⟨P₁, hP₁S, hP₁, hz₁V⟩ := exists_isKleinFour_mem hS₁ ⟨V₁, hV₁S, hV₁⟩ hz₁S hz₁2
  obtain ⟨P₂, hP₂S, hP₂, hz₂V⟩ := exists_isKleinFour_mem hS₂ ⟨V₂, hV₂S, hV₂⟩ hz₂S hz₂2
  have hp₀ : FourPair S₁ S₂ P₁ P₂ := FourPair.of_le hc hd hP₁S hP₂S hP₁ hP₂
  have hlink₁ : ∀ U₁ U₂, FourPair S₁ S₂ U₁ U₂ → wE U₁ U₂ = wE P₁ U₂ := by
    intro U₁ U₂ hp
    obtain ⟨u, huU, hu1, huz⟩ := exists_mem_ne_of_isKleinFour hp.four_left z₁
    have hK : IsKleinFour (zpowers u ⊔ zpowers z₁ : Subgroup G) :=
      isKleinFour_sup (orderOf_eq_two_of_isKleinFour hp.four_left huU hu1) hz₁2 huz
        (hz₁c u (hp.le_left huU))
    have hle : zpowers u ⊔ zpowers z₁ ≤ S₁ :=
      sup_le (zpowers_le.mpr (hp.le_left huU)) (zpowers_le.mpr hz₁S)
    have hp' : FourPair S₁ S₂ (zpowers u ⊔ zpowers z₁) U₂ :=
      FourPair.of_le hc hd hle hp.le_right hK hp.four_right
    have hp'' : FourPair S₁ S₂ P₁ U₂ := FourPair.of_le hc hd hP₁S hp.le_right hP₁ hp.four_right
    rw [wE_eq_of_mem_left hp hp' hsep huU (mem_sup_left (mem_zpowers u)) hu1,
      wE_eq_of_mem_left hp' hp'' hsep (mem_sup_right (mem_zpowers z₁)) hz₁V
        (ne_one_of_orderOf_eq_two hz₁2)]
  have hlink₂ : ∀ U₂, FourPair S₁ S₂ P₁ U₂ → wE P₁ U₂ = wE P₁ P₂ := by
    intro U₂ hp
    obtain ⟨u, huU, hu1, huz⟩ := exists_mem_ne_of_isKleinFour hp.four_right z₂
    have hK : IsKleinFour (zpowers u ⊔ zpowers z₂ : Subgroup G) :=
      isKleinFour_sup (orderOf_eq_two_of_isKleinFour hp.four_right huU hu1) hz₂2 huz
        (hz₂c u (hp.le_right huU))
    have hle : zpowers u ⊔ zpowers z₂ ≤ S₂ :=
      sup_le (zpowers_le.mpr (hp.le_right huU)) (zpowers_le.mpr hz₂S)
    have hp' : FourPair S₁ S₂ P₁ (zpowers u ⊔ zpowers z₂) :=
      FourPair.of_le hc hd hP₁S hle hP₁ hK
    rw [wE_eq_of_mem_right hp hp' hsep huU (mem_sup_left (mem_zpowers u)) hu1,
      wE_eq_of_mem_right hp' hp₀ hsep (mem_sup_right (mem_zpowers z₂)) hz₂V
        (ne_one_of_orderOf_eq_two hz₂2)]
  set W := wE P₁ P₂ with hWdef
  have hW : ∀ U₁ U₂, FourPair S₁ S₂ U₁ U₂ → wE U₁ U₂ = W := fun U₁ U₂ hp =>
    (hlink₁ U₁ U₂ hp).trans
      (hlink₂ U₂ (FourPair.of_le hc hd hP₁S hp.le_right hP₁ hp.four_right))
  have hpair : ∀ c₁ ∈ S₁, orderOf c₁ = 2 → ∀ c₂ ∈ S₂, orderOf c₂ = 2 →
      ∃ U₁ U₂, FourPair S₁ S₂ U₁ U₂ ∧ c₁ ∈ U₁ ∧ c₂ ∈ U₂ := by
    intro c₁ hc₁ hc₁2 c₂ hc₂ hc₂2
    obtain ⟨U₁, hU₁S, hU₁, hcU₁⟩ := exists_isKleinFour_mem hS₁ ⟨V₁, hV₁S, hV₁⟩ hc₁ hc₁2
    obtain ⟨U₂, hU₂S, hU₂, hcU₂⟩ := exists_isKleinFour_mem hS₂ ⟨V₂, hV₂S, hV₂⟩ hc₂ hc₂2
    exact ⟨U₁, U₂, FourPair.of_le hc hd hU₁S hU₂S hU₁ hU₂, hcU₁, hcU₂⟩
  have hmax : ∀ c₁ ∈ S₁, orderOf c₁ = 2 → ∀ c₂ ∈ S₂, orderOf c₂ = 2 →
      W ∈ NSet (zpowers c₁ ⊔ zpowers c₂) ∧ ∀ X ∈ NSet (zpowers c₁ ⊔ zpowers c₂), X ≤ W := by
    intro c₁ hc₁ hc₁2 c₂ hc₂ hc₂2
    obtain ⟨U₁, U₂, hp, hcU₁, hcU₂⟩ := hpair c₁ hc₁ hc₁2 c₂ hc₂ hc₂2
    rw [← hW U₁ U₂ hp]
    exact ⟨wE_mem_NSet hp hsep (sup_le_sup (zpowers_le.mpr hcU₁) (zpowers_le.mpr hcU₂)),
      fun X hX => le_wE_of_mem_NSet hp hsep hcU₁ (ne_one_of_orderOf_eq_two hc₁2) hcU₂
        (ne_one_of_orderOf_eq_two hc₂2) hX⟩
  have hfour : ∀ {S V : Subgroup G} {b : G}, IsPGroup 2 S → V ≤ S → IsKleinFour V → b ∈ S →
      b * b = 1 → ∃ U ≤ S, IsKleinFour U ∧ b ∈ U := by
    intro S V b hS hVS hV hb hb2
    by_cases h : b = 1
    · exact ⟨V, hVS, hV, h ▸ one_mem _⟩
    · exact exists_isKleinFour_mem hS ⟨V, hVS, hV⟩ hb
        (orderOf_eq_prime (by rw [pow_two]; exact hb2) h)
  have hcond : ∀ t ∈ S₁ ⊔ S₂, orderOf t = 2 → W ⊓ centralizer ({t} : Set G) ≤ oddCent t := by
    intro t ht ht2
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl, h₁, h₂⟩ := exists_mul_of_mul_self hc hd ht htt
    obtain ⟨U₁, hU₁S, hU₁, htU₁⟩ := hfour hS₁ hV₁S hV₁ ht₁ h₁
    obtain ⟨U₂, hU₂S, hU₂, htU₂⟩ := hfour hS₂ hV₂S hV₂ ht₂ h₂
    have hp := FourPair.of_le hc hd hU₁S hU₂S hU₁ hU₂
    rw [← hW U₁ U₂ hp]
    exact (wE_mem_NSet hp hsep (zpowers_le.mpr (mul_mem (mem_sup_left htU₁)
      (mem_sup_right htU₂)))).2.2 _ (mem_zpowers _) ht2
  have hN₁ : S₁ ⊔ S₂ ≤ normalizer (S₁ : Set G) :=
    sup_le le_normalizer ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _))
  have hN₂ : S₁ ⊔ S₂ ≤ normalizer (S₂ : Set G) :=
    sup_le (hc.trans (centralizer_le_normalizer _)) le_normalizer
  have hconjmem : ∀ {S : Subgroup G} {g b : G}, S₁ ⊔ S₂ ≤ normalizer (S : Set G) →
      g ∈ S₁ ⊔ S₂ → b ∈ S → g⁻¹ * b * g ∈ S := by
    intro S g b hN hg hb
    have h := (mem_normalizer_iff.mp (inv_mem (hN hg)) b).mp hb
    rwa [inv_inv] at h
  have hord : ∀ g b : G, orderOf b = 2 → orderOf (g⁻¹ * b * g) = 2 := by
    intro g b hb
    have h := orderOf_conj_eq g⁻¹ b
    rwa [inv_inv, hb] at h
  refine ⟨W, (wE_spec hp₀ hsep).1, fun B₁ B₂ hB₁ hB₂ hB₁1 hB₂1 => ?_,
    fun t₁ ht₁ ht₁2 t₂ ht₂ ht₂2 => ?_⟩
  · obtain ⟨b₁, hb₁, hb₁2, -⟩ := exists_central_involution_of_isPGroup (hS₁.to_le hB₁) hB₁1
    obtain ⟨b₂, hb₂, hb₂2, -⟩ := exists_central_involution_of_isPGroup (hS₂.to_le hB₂) hB₂1
    have hle : zpowers b₁ ⊔ zpowers b₂ ≤ B₁ ⊔ B₂ :=
      sup_le_sup (zpowers_le.mpr hb₁) (zpowers_le.mpr hb₂)
    have hmb := hmax b₁ (hB₁ hb₁) hb₁2 b₂ (hB₂ hb₂) hb₂2
    refine ⟨⟨fun g hg => ?_, (wE_spec hp₀ hsep).1,
      fun t ht ht2 => hcond t (sup_le_sup hB₁ hB₂ ht) ht2⟩, fun X hX => hmb.2 X (NSet_anti hle hX)⟩
    have hgS : g ∈ S₁ ⊔ S₂ := sup_le_sup hB₁ hB₂ hg
    have hconj := NSet_conjSub g hmb.1
    rw [conjSub_sup, conjSub_zpowers, conjSub_zpowers] at hconj
    have hle' : conjSub g W ≤ W := (hmax _ (hconjmem hN₁ hgS (hB₁ hb₁)) (hord g b₁ hb₁2) _
      (hconjmem hN₂ hgS (hB₂ hb₂)) (hord g b₂ hb₂2)).2 _ hconj
    have hcard : Nat.card W ≤ Nat.card (conjSub g W) := by
      unfold conjSub
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact mem_normalizer_of_conjSub_eq (Subgroup.eq_of_le_of_card_ge hle' hcard)
  · obtain ⟨U₁, U₂, hp, htU₁, htU₂⟩ := hpair t₁ ht₁ ht₁2 t₂ ht₂ ht₂2
    obtain ⟨-, hθ⟩ := wE_spec hp hsep
    rw [← hW U₁ U₂ hp]
    refine ⟨(commutator_oddCent_le_theta hp htU₁ htU₂).trans
      ((hθ t₁ (mem_sup_left htU₁) (ne_one_of_orderOf_eq_two ht₁2)).le.trans inf_le_left), ?_⟩
    have h := commutator_oddCent_le_theta hp.symm htU₂ htU₁
    rw [theta_comm] at h
    exact h.trans ((hθ t₂ (mem_sup_right htU₂) (ne_one_of_orderOf_eq_two ht₂2)).le.trans
      inf_le_left)

end CFSG.Goldschmidt75
