module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIZStar
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIRel

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_not_mem_of_card_lt {A B : Subgroup G} (h : Nat.card A < Nat.card B) :
    ∃ x ∈ B, x ∉ A := by
  by_contra hcon
  have hBA : B ≤ A := fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩
  have := Subgroup.card_le_of_le hBA
  omega

end Basic

section Rel

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

omit [Finite G] in
theorem inf_sec4N_right_eq : T₂ ⊓ sec4N T T₁ T₂ = normIn T₂ T := by
  apply le_antisymm
  · intro x hx
    exact mem_normIn.2 ⟨hx.1, sec4N_le_normalizer_left hx.2⟩
  · intro x hx
    exact ⟨normIn_le _ _ hx, normIn_le_sec4N_right hx⟩

theorem Sec4Hyp.exists_rel_four (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) (h4 : Nat.card T = 4) :
    ∃ ℓ ℓ₁ t t₁ t₂ : G, ℓ ∈ normIn T T₁ ∧ ℓ ≠ 1 ∧ ℓ₁ ∈ normIn T₁ T ∧ ℓ₁ ≠ 1 ∧
      t ∈ T ∧ t ∉ normIn T T₁ ∧ t₁ ∈ T₁ ∧ t₁ ∉ normIn T₁ T ∧ t₂ ∈ T₂ ∧ t₂ ∉ normIn T₂ T ∧
      t * ℓ * t⁻¹ = ℓ ∧ t * ℓ₁ * t⁻¹ = ℓ * ℓ₁ ∧ t * a * t⁻¹ = ℓ * a ∧
      t₁ * ℓ * t₁⁻¹ = ℓ₁ * ℓ ∧ t₁ * ℓ₁ * t₁⁻¹ = ℓ₁ ∧ t₁ * a * t₁⁻¹ = ℓ₁ * a ∧
      t₂ * ℓ * t₂⁻¹ = a * ℓ ∧ t₂ * ℓ₁ * t₂⁻¹ = a * ℓ₁ ∧ t₂ * a * t₂⁻¹ = a := by
  have hB := h.mem_normalizer_normIn
  have hcL : Nat.card (normIn T T₁) = 2 := by omega
  have hcL₁ : Nat.card (normIn T₁ T) = 2 := by rw [h.card_normIn₁, hcL]
  have hcL₂ : Nat.card (normIn T₂ T) = 2 := by rw [h.card_normIn₂_eq hB, hcL]
  have e1 : normIn T T₂ = normIn T T₁ := h.normIn_eq hB
  have e2 : normIn T₁ T₂ = normIn T₁ T := h.normIn_right_eq hB
  have e3 : normIn T₂ T = normIn T₂ T₁ := h.normIn₂_eq hB
  have hc₁ := h.sec3.cfg
  have hc₂ := h.cfg₂
  have hc₁₂ := h.cfg₁₂ hB
  have hcT₁ : Nat.card T₁ = 4 := by
    obtain ⟨x, hx⟩ := h.pair.conj
    rw [hx, card_conjSubgroup, h4]
  have hcT₂ : Nat.card T₂ = 4 := by
    obtain ⟨x, hx⟩ := h.conj
    rw [hx, card_conjSubgroup, h4]
  obtain ⟨⟨ℓ, hℓ⟩, hℓ1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc₁.ne
  have hℓ1 : ℓ ≠ 1 := fun h' => hℓ1' (Subtype.ext h')
  obtain ⟨⟨ℓ₁, hℓ₁⟩, hℓ₁1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hc₁.ne₁
  have hℓ₁1 : ℓ₁ ≠ 1 := fun h' => hℓ₁1' (Subtype.ext h')
  obtain ⟨t, ht, htL⟩ := exists_mem_not_mem_of_card_lt (A := normIn T T₁) (B := T) (by omega)
  obtain ⟨t₁, ht₁, ht₁L⟩ := exists_mem_not_mem_of_card_lt (A := normIn T₁ T) (B := T₁) (by omega)
  obtain ⟨t₂, ht₂, ht₂L⟩ := exists_mem_not_mem_of_card_lt (A := normIn T₂ T) (B := T₂) (by omega)
  have haL₂ : a ∈ normIn T₂ T := h.mem_normIn₂
  have haL₂' : a ∈ normIn T₂ T₁ := by rw [← e3]; exact haL₂
  have hℓ' : ℓ ∈ normIn T T₂ := by rw [e1]; exact hℓ
  have hℓ₁' : ℓ₁ ∈ normIn T₁ T₂ := by rw [e2]; exact hℓ₁
  have htL' : t ∉ normIn T T₂ := by rw [e1]; exact htL
  have ht₁L' : t₁ ∉ normIn T₁ T₂ := by rw [e2]; exact ht₁L
  have ht₂L' : t₂ ∉ normIn T₂ T₁ := by rw [← e3]; exact ht₂L
  have hℓT : ℓ ∈ T := normIn_le T T₁ hℓ
  have hℓ₁T₁ : ℓ₁ ∈ T₁ := normIn_le T₁ T hℓ₁
  have haT₂ : a ∈ T₂ := h.haT₂
  refine ⟨ℓ, ℓ₁, t, t₁, t₂, hℓ, hℓ1, hℓ₁, hℓ₁1, ht, htL, ht₁, ht₁L, ht₂, ht₂L, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · have := elemAbelian_mul_comm h.pair.wc.1 ht hℓT
    rw [this]
    group
  · exact hc₁.conj_mul_eq_of_card_two hcL ht htL hℓ₁ hℓ₁1 hℓ hℓ1
  · exact hc₂.conj_mul_eq_of_card_two (by rw [e1]; exact hcL) ht htL' haL₂ h.ne_one hℓ' hℓ1
  · exact hc₁.symm.conj_mul_eq_of_card_two hcL₁ ht₁ ht₁L hℓ hℓ1 hℓ₁ hℓ₁1
  · have := elemAbelian_mul_comm h.isWC₁.1 ht₁ hℓ₁T₁
    rw [this]
    group
  · exact hc₁₂.conj_mul_eq_of_card_two (by rw [e2]; exact hcL₁) ht₁ ht₁L' haL₂' h.ne_one hℓ₁'
      hℓ₁1
  · exact hc₂.symm.conj_mul_eq_of_card_two hcL₂ ht₂ ht₂L hℓ' hℓ1 haL₂ h.ne_one
  · exact hc₁₂.symm.conj_mul_eq_of_card_two (by rw [← e3]; exact hcL₂) ht₂ ht₂L' hℓ₁' hℓ₁1
      haL₂' h.ne_one
  · have := elemAbelian_mul_comm h.isWC₂.1 ht₂ haT₂
    rw [this]
    group

theorem Sec4Hyp.false_of_card_four (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) (h4 : Nat.card T = 4) : False := by
  obtain ⟨ℓ, ℓ₁, t, t₁, t₂, hℓ, hℓ1, hℓ₁, hℓ₁1, ht, htL, ht₁, ht₁L, ht₂, ht₂L, r1, r2, r3, r4,
    r5, r6, r7, r8, r9⟩ := h.exists_rel_four hq h4
  obtain ⟨P, -, hsq, hP⟩ := h.exists_odd_subgroup hq
  have hB := h.mem_normalizer_normIn
  have hNab := h.isElemAbelian_sec4N
  have hℓN : ℓ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_left hℓ
  have hℓ₁N : ℓ₁ ∈ sec4N T T₁ T₂ := normIn_le_sec4N_mid hℓ₁
  have haN : a ∈ sec4N T T₁ T₂ := normIn_le_sec4N_right h.mem_normIn₂
  have htN : t ∉ sec4N T T₁ T₂ := fun hN => htL (by rw [← h.inf_sec4N_eq]; exact ⟨ht, hN⟩)
  have ht₁N : t₁ ∉ sec4N T T₁ T₂ := fun hN => ht₁L (by
    rw [← inf_sec4N_mid_eq (T := T) (T₂ := T₂)]
    exact ⟨ht₁, hN⟩)
  have ht₂N : t₂ ∉ sec4N T T₁ T₂ := fun hN => ht₂L (by
    rw [← inf_sec4N_right_eq (T := T) (T₁ := T₁)]
    exact ⟨ht₂, hN⟩)
  have htt : t * t = 1 := elemAbelian_mul_self h.pair.wc.1 ht
  have ht₁t₁ : t₁ * t₁ = 1 := elemAbelian_mul_self h.isWC₁.1 ht₁
  have ht₂t₂ : t₂ * t₂ = 1 := elemAbelian_mul_self h.isWC₂.1 ht₂
  have hS₂ : Sec3 T T₂ := sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ h.conj
    h.ne_left h.normIn_ne_bot
  have hM₂ : cfgM T T₂ ≤ sec4N T T₁ T₂ := by
    rw [cfgM, h.normIn_eq hB]
    exact sup_le normIn_le_sec4N_left normIn_le_sec4N_right
  have hodd₁ : Odd (orderOf (t * t₁)) :=
    odd_orderOf_mul_of_sec3 h.sec3 cfgM_le_sec4N h.pair.ne ht htN ht₁ ht₁N
  have hodd₂ : Odd (orderOf (t * t₂)) :=
    odd_orderOf_mul_of_sec3 hS₂ hM₂ h.ne_left ht htN ht₂ ht₂N
  have hP₁ : t * t₁ ∈ P := mul_mem_of_sq_mem_of_odd_orderOf hsq (left_le_sec4Y ht)
    (mid_le_sec4Y ht₁) htt ht₁t₁ hodd₁
  have hP₂ : t * t₂ ∈ P := mul_mem_of_sq_mem_of_odd_orderOf hsq (left_le_sec4Y ht)
    (right_le_sec4Y ht₂) htt ht₂t₂ hodd₂
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have ht₁i : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁t₁
  have ht₂i : t₂⁻¹ = t₂ := inv_eq_of_mul_eq_one_right ht₂t₂
  have hz : t₂ * t * t₁ * t ∈ P := by
    have e1 : t₂ * t = (t * t₂)⁻¹ := by rw [mul_inv_rev, hti, ht₂i]
    have e2 : t₁ * t = (t * t₁)⁻¹ := by rw [mul_inv_rev, hti, ht₁i]
    have e3 : t₂ * t * t₁ * t = (t₂ * t) * (t₁ * t) := by group
    rw [e3, e1, e2]
    exact P.mul_mem (P.inv_mem hP₂) (P.inv_mem hP₁)
  obtain ⟨m, hm, hzm⟩ := hP _ hz
  have hzm' : (t₂ * t * t₁ * t) ^ m * ℓ = ℓ * (t₂ * t * t₁ * t) ^ m :=
    elemAbelian_mul_comm hNab hzm hℓN
  have hrel := eq_of_relations (elemAbelian_mul_self hNab hℓN) (elemAbelian_mul_self hNab hℓ₁N)
    (elemAbelian_mul_self hNab haN) (elemAbelian_mul_comm hNab hℓN hℓ₁N) r1 r2 r3 r4 r5 r6 r7 r8
    r9 hm hzm'
  have ha' : a = ℓ * ℓ₁ := by
    have h1 : a = ℓ * ℓ₁⁻¹ := eq_mul_inv_of_mul_eq hrel
    rwa [inv_eq_of_mul_eq_one_right (elemAbelian_mul_self hNab hℓ₁N)] at h1
  apply h.haL
  rw [ha']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (normIn_le T T₁ hℓ)) (Subgroup.mem_sup_right hℓ₁)

end Rel

end CFSG.CGT.Timmesfeld75
