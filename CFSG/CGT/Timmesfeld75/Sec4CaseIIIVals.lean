module

public import CFSG.CGT.Timmesfeld75.Sec3TenCaseB3

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem card_le_four_mul_card_inf {A B T : Subgroup G} (hA : A ≤ T) (hB : B ≤ T)
    (hcA : Nat.card T = Nat.card A * 2) (hcB : Nat.card T = Nat.card B * 2) :
    Nat.card T ≤ Nat.card ↥(A ⊓ B) * 4 := by
  have hAi : A.relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := A) (K := T)
    rw [inf_eq_left.2 hA] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, hcA]
    ring
  have hBi : B.relIndex T = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := T)
    rw [inf_eq_left.2 hB] at h1
    have hpos : 0 < Nat.card B := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [h1, hcB]
    ring
  have hF := Subgroup.relIndex_inf_le (H := A) (K := B) (L := T)
  have h2 := Subgroup.relIndex_mul_card (H := A ⊓ B) (K := T)
  rw [inf_eq_left.2 (inf_le_left.trans hA)] at h2
  rw [hAi, hBi] at hF
  calc Nat.card T = (A ⊓ B).relIndex T * Nat.card ↥(A ⊓ B) := h2.symm
    _ ≤ (2 * 2) * Nat.card ↥(A ⊓ B) := Nat.mul_le_mul_right _ hF
    _ = Nat.card ↥(A ⊓ B) * 4 := by ring

theorem Sec3.values_of_mem_conj (hS : Sec3 T T₁)
    (hcard : Nat.card T = Nat.card (normIn T T₁) * 2) {g : G}
    (hg : g ∈ Subgroup.normalizer (T : Set G)) {t₀ : G} (ht₀ : t₀ ∈ T)
    (ht₀U : t₀ ∉ normIn T (conjSubgroup g T₁)) {z : G}
    (hz : z ∈ conjSubgroup g (normIn T₁ T)) :
    ∀ s ∈ T, ⁅s, z⁆ = 1 ∨ ⁅s, z⁆ = ⁅t₀, z⁆ := by
  have hS2 := hS.conj_of_mem_normalizer hg
  have hL₂ : normIn (conjSubgroup g T₁) T = conjSubgroup g (normIn T₁ T) :=
    normIn_conj_right_of_mem_normalizer hg T₁
  have hLg : normIn T (conjSubgroup g T₁) = conjSubgroup g (normIn T T₁) :=
    normIn_conj_left_of_mem_normalizer hg T₁
  have hcardU : Nat.card T = Nat.card (normIn T (conjSubgroup g T₁)) * 2 := by
    rw [hLg, card_conjSubgroup]
    exact hcard
  have hzL : z ∈ normIn (conjSubgroup g T₁) T := by
    rw [hL₂]
    exact hz
  have hwc := hS.cfg.wc
  have hUT : normIn T (conjSubgroup g T₁) ≤ T := normIn_le _ _
  intro s hs
  by_cases hsU : s ∈ normIn T (conjSubgroup g T₁)
  · left
    have hc := hS2.cfg.comm_L_L₁ hsU hzL
    simp only [commutatorElement_def]
    rw [hc]
    group
  · right
    have hw : s * t₀ ∈ normIn T (conjSubgroup g T₁) :=
      mul_mem_of_not_mem_of_card hUT hcardU hs ht₀ hsU ht₀U
    have hwT : s * t₀ ∈ T := hUT hw
    have hc : (s * t₀) * z = z * (s * t₀) := hS2.cfg.comm_L_L₁ hw hzL
    have hcc : (s * t₀)⁻¹ * z⁻¹ = z⁻¹ * (s * t₀)⁻¹ :=
      (Commute.inv_inv (show Commute (s * t₀) z from hc)).eq
    have hu : ⁅t₀, z⁆ ∈ normIn T (conjSubgroup g T₁) := hS2.cfg.comm_mem_normIn ht₀ hzL
    have hcu : (s * t₀) * ⁅t₀, z⁆ = ⁅t₀, z⁆ * (s * t₀) :=
      elemAbelian_mul_comm hwc.1 hwT (hUT hu)
    have hst : s = (s * t₀) * t₀ := by
      have : t₀ * t₀ = 1 := elemAbelian_mul_self hwc.1 ht₀
      rw [mul_assoc, this, mul_one]
    calc ⁅s, z⁆ = s * z * s⁻¹ * z⁻¹ := rfl
      _ = (s * t₀) * t₀ * z * ((s * t₀) * t₀)⁻¹ * z⁻¹ := by rw [← hst]
      _ = (s * t₀) * t₀ * z * t₀⁻¹ * ((s * t₀)⁻¹ * z⁻¹) := by group
      _ = (s * t₀) * t₀ * z * t₀⁻¹ * (z⁻¹ * (s * t₀)⁻¹) := by rw [hcc]
      _ = (s * t₀) * ⁅t₀, z⁆ * (s * t₀)⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅t₀, z⁆ := by rw [hcu]; group

omit [Finite G] in
theorem commutator_eq_of_conj_eq {T : Subgroup G} (hT : IsElemAbelian 2 T) {t₀ u z : G}
    (ht₀ : t₀ ∈ T) (hu : u ∈ T) (h : z * t₀ * z⁻¹ = t₀ * u) : ⁅t₀, z⁆ = u := by
  have ht₀i : t₀⁻¹ = t₀ := elemAbelian_inv hT ht₀
  have hui : u⁻¹ = u := elemAbelian_inv hT hu
  have hc : t₀ * u = u * t₀ := elemAbelian_mul_comm hT ht₀ hu
  have htt : t₀ * t₀ = 1 := elemAbelian_mul_self hT ht₀
  have h1 : z * t₀⁻¹ * z⁻¹ = (t₀ * u)⁻¹ := by rw [← h]; group
  calc ⁅t₀, z⁆ = t₀ * (z * t₀⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = t₀ * (t₀ * u)⁻¹ := by rw [h1]
    _ = t₀ * (u⁻¹ * t₀⁻¹) := by rw [mul_inv_rev]
    _ = t₀ * (u * t₀) := by rw [hui, ht₀i]
    _ = (t₀ * t₀) * u := by
        rw [← hc]
        group
    _ = u := by rw [htt, one_mul]

theorem Sec3.exists_two_mem_conj (hS : Sec3 T T₁)
    (hcard : Nat.card T = Nat.card (normIn T T₁) * 2) (hL8 : 8 ≤ Nat.card (normIn T T₁))
    {g : G} (hg : g ∈ Subgroup.normalizer (T : Set G)) :
    ∃ t₀ ∈ T, t₀ ∉ normIn T (conjSubgroup g T₁) ∧ ∃ x y : G,
      x ∈ conjSubgroup g (normIn T₁ T) ∧ y ∈ conjSubgroup g (normIn T₁ T) ∧ x ≠ 1 ∧ y ≠ 1 ∧
      x ≠ y ∧ ⁅t₀, x⁆ ∈ normIn T T₁ ∧ ⁅t₀, y⁆ ∈ normIn T T₁ := by
  have hS2 := hS.conj_of_mem_normalizer hg
  have hLg : normIn T (conjSubgroup g T₁) = conjSubgroup g (normIn T T₁) :=
    normIn_conj_left_of_mem_normalizer hg T₁
  have hcardU : Nat.card T = Nat.card (normIn T (conjSubgroup g T₁)) * 2 := by
    rw [hLg, card_conjSubgroup]
    exact hcard
  have hwc := hS.cfg.wc
  have hUT : normIn T (conjSubgroup g T₁) ≤ T := normIn_le _ _
  have hLT : normIn T T₁ ≤ T := normIn_le _ _
  have hTnle : ¬ T ≤ normIn T (conjSubgroup g T₁) := by
    intro hle
    have heq : normIn T (conjSubgroup g T₁) = T := le_antisymm hUT hle
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [heq] at hcardU
    omega
  obtain ⟨t₀, ht₀T, ht₀U⟩ := IsConcreteLE.not_le_iff_exists.1 hTnle
  have ht₀M : t₀ ∉ cfgM T (conjSubgroup g T₁) := fun hM => ht₀U (by
    rw [← hS2.cfg.inf_cfgM]
    exact ⟨ht₀T, hM⟩)
  have hF4 : 4 ≤ Nat.card ↥(normIn T T₁ ⊓ normIn T (conjSubgroup g T₁)) := by
    have h1 := card_le_four_mul_card_inf hLT hUT hcard hcardU
    omega
  have h2 : 2 < ((normIn T T₁ ⊓ normIn T (conjSubgroup g T₁) : Subgroup G) : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact lt_of_lt_of_le (by norm_num) hF4
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 h2
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁1, hu₂1, hu₁₂⟩ : ∃ u₁ u₂ : G,
      u₁ ∈ normIn T T₁ ⊓ normIn T (conjSubgroup g T₁) ∧
      u₂ ∈ normIn T T₁ ⊓ normIn T (conjSubgroup g T₁) ∧ u₁ ≠ 1 ∧ u₂ ≠ 1 ∧ u₁ ≠ u₂ := by
    by_cases hp1 : p = 1
    · exact ⟨q, r, hq, hr, fun h => hpq (hp1.trans h.symm), fun h => hpr (hp1.trans h.symm), hqr⟩
    by_cases hq1 : q = 1
    · exact ⟨p, r, hp, hr, hp1, fun h => hqr (hq1.trans h.symm), hpr⟩
    · exact ⟨p, q, hp, hq, hp1, hq1, hpq⟩
  have key : ∀ u ∈ normIn T T₁ ⊓ normIn T (conjSubgroup g T₁), ∃ z ∈ conjSubgroup g (normIn T₁ T),
      ⁅t₀, z⁆ = u := by
    intro u hu
    obtain ⟨l, hl, hlu⟩ := hS2.exists_mem_normIn₁_conj_eq ht₀T ht₀M hu.2
    refine ⟨l, ?_, commutator_eq_of_conj_eq hwc.1 ht₀T (hUT hu.2) hlu⟩
    rw [← normIn_conj_right_of_mem_normalizer hg T₁]
    exact hl
  obtain ⟨x, hx, hxu⟩ := key u₁ hu₁
  obtain ⟨y, hy, hyu⟩ := key u₂ hu₂
  refine ⟨t₀, ht₀T, ht₀U, x, y, hx, hy, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    apply hu₁1
    rw [← hxu]
    simp [commutatorElement_def]
  · rintro rfl
    apply hu₂1
    rw [← hyu]
    simp [commutatorElement_def]
  · rintro rfl
    exact hu₁₂ (hxu.symm.trans hyu)
  · rw [hxu]
    exact hu₁.1
  · rw [hyu]
    exact hu₂.1

end CFSG.CGT.Timmesfeld75
