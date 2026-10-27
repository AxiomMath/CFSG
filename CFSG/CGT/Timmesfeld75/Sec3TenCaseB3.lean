module

public import CFSG.CGT.Timmesfeld75.Sec3TenBasic
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB1

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem mul_mem_of_not_mem_of_card [Finite G] {A B : Subgroup G} (hAB : A ≤ B)
    (hcard : Nat.card B = Nat.card A * 2) {p q : G} (hp : p ∈ B) (hq : q ∈ B) (hpA : p ∉ A)
    (hqA : q ∉ A) : p * q ∈ A := by
  have hidx : (A.subgroupOf B).index = 2 := by
    have h1 := Subgroup.card_mul_index (A.subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans hcard)
  have hp' : (⟨p, hp⟩ : B) ∉ A.subgroupOf B := hpA
  have hq' : (⟨q, hq⟩ : B) ∉ A.subgroupOf B := hqA
  exact (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨p, hp⟩) (b := ⟨q, hq⟩)).2
    (iff_of_false hp' hq')

theorem Sec3.three_le_card_normIn [Finite G] (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (hD : Sec3Dih T T₁ n) : 3 ≤ Nat.card (normIn T T₁) := by
  obtain ⟨hN, ⟨e⟩⟩ := hD
  by_contra hlt
  obtain ⟨l₀, hl₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS.cfg.ne
  have hl₀M : (l₀ : G) ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ l₀.2
  have hl₀1 : (l₀ : G) ≠ 1 := fun h => hl₀ (Subtype.ext h)
  set V : Set G := {w | w ∈ cfgM T T₁ ∧ w ≠ 1} with hV
  have hVinv : ∀ x ∈ T ⊔ T₁, ∀ w ∈ V, x * w * x⁻¹ ∈ V := by
    rintro x hx w ⟨hw, hw1⟩
    refine ⟨hS.cfg.conj_mem_cfgM hx hw, fun h => hw1 ?_⟩
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  have hcard := hS.card_le_of_invariant_dihedral hn e (V := V) (fun w hw => hw) hVinv
    (w₀ := l₀) ⟨hl₀M, hl₀1⟩
  have hsub : V ⊆ (cfgM T T₁ : Set G) \ {1} := fun w hw => ⟨hw.1, hw.2⟩
  have hc1 : V.ncard ≤ ((cfgM T T₁ : Set G) \ {1}).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hc2 : ((cfgM T T₁ : Set G) \ {1}).ncard + 1 = Nat.card (cfgM T T₁) := by
    rw [Set.ncard_sdiff_singleton_add_one (a := 1) (cfgM T T₁).one_mem (Set.toFinite _)]
    exact Nat.card_coe_set_eq _ ▸ rfl
  have hsq := hS.card_cfgM_eq_sq
  have hL2 : Nat.card (normIn T T₁) ≤ 2 := by omega
  have : Nat.card (cfgM T T₁) ≤ 4 := by
    rw [hsq]
    exact Nat.pow_le_pow_left hL2 2
  omega

theorem Sec3.exists_a [Finite G] (hS : Sec3 T T₁) {n : ℕ} (hn : Odd n) (hn3 : 3 < n)
    (hD : Sec3Dih T T₁ n) {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G))
    (hgB : ∃ x ∈ conjSubgroup g (normIn T₁ T), ∃ l ∈ normIn T T₁, x * l ≠ l * x) :
    ∃ a u : G, a ∈ conjSubgroup g (normIn T₁ T) ∧ a ≠ 1 ∧ u ∈ normIn T T₁ ∧
      (∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u) ∧ ∃ l ∈ normIn T T₁, a * l ≠ l * a := by
  have hS2 := hS.conj_of_mem_normalizer hg
  have hD' := hD
  obtain ⟨hN, ⟨e⟩⟩ := hD
  have hcard : Nat.card T = Nat.card (normIn T T₁) * 2 := hS.card_eq_two_mul_dihedral hn e
  have hL3 := hS.three_le_card_normIn hn hn3 hD'
  have hLg : normIn T (conjSubgroup g T₁) = conjSubgroup g (normIn T T₁) :=
    normIn_conj_left_of_mem_normalizer hg T₁
  have hL₂ : normIn (conjSubgroup g T₁) T = conjSubgroup g (normIn T₁ T) :=
    normIn_conj_right_of_mem_normalizer hg T₁
  have hcardg : Nat.card T = Nat.card (normIn T (conjSubgroup g T₁)) * 2 := by
    rw [hLg, card_conjSubgroup]
    exact hcard
  have hcardg3 : 3 ≤ Nat.card (normIn T (conjSubgroup g T₁)) := by
    rw [hLg, card_conjSubgroup]
    exact hL3
  obtain ⟨x₀, hx₀, l₀, hl₀, hx₀l₀⟩ := hgB
  have hne : normIn T (conjSubgroup g T₁) ≠ normIn T T₁ := by
    intro h
    apply hx₀l₀
    have hl' : l₀ ∈ normIn T (conjSubgroup g T₁) := by rw [h]; exact hl₀
    have hx' : x₀ ∈ normIn (conjSubgroup g T₁) T := by rw [hL₂]; exact hx₀
    exact (hS2.cfg.comm_L_L₁ hl' hx').symm
  have hLgT : normIn T (conjSubgroup g T₁) ≤ T := normIn_le _ _
  have hwc := hS.cfg.wc
  obtain ⟨p, q, hpL, hqL, hp1, hq1, hpq⟩ : ∃ p q : G, p ∈ normIn T (conjSubgroup g T₁) ∧
      q ∈ normIn T (conjSubgroup g T₁) ∧ p ≠ 1 ∧ q ≠ 1 ∧ p ≠ q := by
    have h2 : 2 < ((normIn T (conjSubgroup g T₁) : Subgroup G) : Set G).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact hcardg3
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h2
    by_cases ha1 : a = 1
    · exact ⟨b, c, hb, hc, fun h => hab (ha1.trans h.symm), fun h => hac (ha1.trans h.symm), hbc⟩
    by_cases hb1 : b = 1
    · exact ⟨a, c, ha, hc, ha1, fun h => hbc (hb1.trans h.symm), hac⟩
    by_cases hc1 : c = 1
    · exact ⟨a, b, ha, hb, ha1, hb1, hab⟩
    · exact ⟨a, b, ha, hb, ha1, hb1, hab⟩
  obtain ⟨u, huLg, huL, hu1⟩ : ∃ u : G, u ∈ normIn T (conjSubgroup g T₁) ∧ u ∈ normIn T T₁ ∧
      u ≠ 1 := by
    by_cases hpL' : p ∈ normIn T T₁
    · exact ⟨p, hpL, hpL', hp1⟩
    by_cases hqL' : q ∈ normIn T T₁
    · exact ⟨q, hqL, hqL', hq1⟩
    refine ⟨p * q, (normIn T (conjSubgroup g T₁)).mul_mem hpL hqL,
      mul_mem_of_not_mem_of_card (normIn_le T T₁) hcard (hLgT hpL) (hLgT hqL) hpL' hqL', ?_⟩
    intro h
    apply hpq
    have hqi : q⁻¹ = q := elemAbelian_inv hwc.1 (hLgT hqL)
    have := eq_inv_of_mul_eq_one_left h
    rw [this, hqi]
  have hTnle : ¬ T ≤ normIn T (conjSubgroup g T₁) := by
    intro hle
    have heq : normIn T (conjSubgroup g T₁) = T := le_antisymm hLgT hle
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [heq] at hcardg
    omega
  obtain ⟨t₀, ht₀T, ht₀Lg⟩ := IsConcreteLE.not_le_iff_exists.1 hTnle
  have ht₀M : t₀ ∉ cfgM T (conjSubgroup g T₁) := fun hM => ht₀Lg (by
    rw [← hS2.cfg.inf_cfgM]; exact ⟨ht₀T, hM⟩)
  obtain ⟨a, haL₂, hat₀⟩ := hS2.exists_mem_normIn₁_conj_eq ht₀T ht₀M huLg
  have haL₂' : a ∈ conjSubgroup g (normIn T₁ T) := by rw [← hL₂]; exact haL₂
  have hti : t₀⁻¹ = t₀ := elemAbelian_inv hwc.1 ht₀T
  have hui : u⁻¹ = u := elemAbelian_inv hwc.1 (hLgT huLg)
  have hcomm_t₀u : t₀ * u = u * t₀ := elemAbelian_mul_comm hwc.1 ht₀T (hLgT huLg)
  have hcomm_a : ∀ l ∈ normIn T (conjSubgroup g T₁), l * a = a * l := fun l hl =>
    hS2.cfg.comm_L_L₁ hl haL₂
  have hcom₀ : ⁅t₀, a⁆ = u := by
    have h1 : a * t₀⁻¹ * a⁻¹ = (t₀ * u)⁻¹ := by
      rw [← hat₀]
      group
    have hcomm' : t₀ * u⁻¹ = u⁻¹ * t₀ :=
      elemAbelian_mul_comm hwc.1 ht₀T (T.inv_mem (hLgT huLg))
    calc ⁅t₀, a⁆ = t₀ * (a * t₀⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      _ = t₀ * (t₀ * u)⁻¹ := by rw [h1]
      _ = t₀ * (u⁻¹ * t₀⁻¹) := by rw [mul_inv_rev]
      _ = (t₀ * u⁻¹) * t₀⁻¹ := by group
      _ = (u⁻¹ * t₀) * t₀⁻¹ := by rw [hcomm']
      _ = u⁻¹ := by group
      _ = u := hui
  have ha1 : a ≠ 1 := by
    intro h
    rw [h] at hat₀
    apply hu1
    have : t₀ * u = t₀ := by
      calc t₀ * u = 1 * t₀ * 1⁻¹ := hat₀.symm
        _ = t₀ := by group
    exact mul_eq_left.1 this
  have hvals : ∀ t ∈ T, ⁅t, a⁆ = 1 ∨ ⁅t, a⁆ = u := by
    intro t ht
    by_cases htLg : t ∈ normIn T (conjSubgroup g T₁)
    · left
      simp only [commutatorElement_def]
      rw [hcomm_a t htLg]
      group
    · right
      have hl' : t * t₀ ∈ normIn T (conjSubgroup g T₁) :=
        mul_mem_of_not_mem_of_card (normIn_le T (conjSubgroup g T₁)) hcardg ht ht₀T htLg ht₀Lg
      have hc := hcomm_a _ hl'
      have hltT : t * t₀ ∈ T := hLgT hl'
      have hcc : (t * t₀)⁻¹ * a⁻¹ = a⁻¹ * (t * t₀)⁻¹ :=
        (Commute.inv_inv (show Commute (t * t₀) a from hc)).eq
      have htl : t = (t * t₀) * t₀ := by
        have : t₀ * t₀ = 1 := elemAbelian_mul_self hwc.1 ht₀T
        rw [mul_assoc, this, mul_one]
      have hcu : (t * t₀) * u = u * (t * t₀) := elemAbelian_mul_comm hwc.1 hltT (hLgT huLg)
      calc ⁅t, a⁆ = t * a * t⁻¹ * a⁻¹ := rfl
        _ = (t * t₀) * t₀ * a * ((t * t₀) * t₀)⁻¹ * a⁻¹ := by rw [← htl]
        _ = (t * t₀) * t₀ * a * t₀⁻¹ * ((t * t₀)⁻¹ * a⁻¹) := by group
        _ = (t * t₀) * t₀ * a * t₀⁻¹ * (a⁻¹ * (t * t₀)⁻¹) := by rw [hcc]
        _ = (t * t₀) * ⁅t₀, a⁆ * (t * t₀)⁻¹ := by simp only [commutatorElement_def]; group
        _ = (t * t₀) * u * (t * t₀)⁻¹ := by rw [hcom₀]
        _ = u := by rw [hcu]; group
  have hLnle : ¬ normIn T T₁ ≤ normIn T (conjSubgroup g T₁) := by
    intro hle
    have hcard' : Nat.card (normIn T (conjSubgroup g T₁)) ≤ Nat.card (normIn T T₁) := by
      omega
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard').symm
  obtain ⟨l, hlL, hlLg⟩ := IsConcreteLE.not_le_iff_exists.1 hLnle
  refine ⟨a, u, haL₂', ha1, huL, hvals, l, hlL, fun hal => hlLg ?_⟩
  exact (hS.isLElt_conj hg haL₂' ha1).cent l (normIn_le T T₁ hlL) hal

end CFSG.CGT.Timmesfeld75
