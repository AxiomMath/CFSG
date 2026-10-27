module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIKappa
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFpf
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIITrans
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIVals

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.false_of_kappa (h : Sec4Hyp T T₁ a T₂)
    (hq : Nat.card T = 2 * Nat.card (normIn T T₁)) {κ : G}
    (hκT : κ ∈ Subgroup.normalizer (T : Set G)) (hκT₁ : κ ∈ Subgroup.normalizer (T₁ : Set G))
    (hκT₂ : κ ∈ Subgroup.normalizer (T₂ : Set G)) {ℓ : G} (hℓ : ℓ ∈ normIn T T₁)
    (hℓκ : κ * ℓ ≠ ℓ * κ)
    (hconst : ∀ l ∈ normIn T T₁, ∀ l' ∈ normIn T T₁, κ * l ≠ l * κ → κ * l' ≠ l' * κ →
      ⁅κ, l⁆ = ⁅κ, l'⁆) : False := by
  have hB := h.mem_normalizer_normIn
  have e1 : normIn T T₂ = normIn T T₁ := h.normIn_eq hB
  have e2 : normIn T₁ T₂ = normIn T₁ T := h.normIn_right_eq hB
  have e3 : normIn T₂ T = normIn T₂ T₁ := h.normIn₂_eq hB
  have hc₁ := h.sec3.cfg
  have hc₂ := h.cfg₂
  have hc₁₂ := h.cfg₁₂ hB
  have hS₂ : Sec3 T T₂ := sec3_of_conj_conj h.glob ⟨1, (conjSubgroup_one T).symm⟩ h.conj
    h.ne_left h.normIn_ne_bot
  have hpos : 0 < Nat.card (normIn T T₁) := Nat.card_pos
  have hpos₁ : 0 < Nat.card (normIn T₁ T) := Nat.card_pos
  have hpos₂ : 0 < Nat.card (normIn T₂ T) := Nat.card_pos
  have hcT : Nat.card T = Nat.card (normIn T T₁) * 2 := by rw [hq, mul_comm]
  have hcT₁ : Nat.card T₁ = Nat.card (normIn T₁ T) * 2 := by
    have h1 : Nat.card T₁ = Nat.card T := by
      obtain ⟨x, hx⟩ := h.pair.conj
      rw [hx, card_conjSubgroup]
    rw [h1, h.card_normIn₁, hcT]
  have hcT₂ : Nat.card T₂ = Nat.card (normIn T₂ T) * 2 := by
    have h1 : Nat.card T₂ = Nat.card T := by
      obtain ⟨x, hx⟩ := h.conj
      rw [hx, card_conjSubgroup]
    rw [h1, h.card_normIn₂_eq hB, hcT]
  have hU₁ := comm_mem_normIn_of_index_two hκT hκT₁ hcT
  have hV₁ := conj_mem_normIn_of_mem hκT hκT₁
  have hU₁' := comm_mem_normIn_of_index_two hκT₁ hκT hcT₁
  have hV₁' := conj_mem_normIn_of_mem hκT₁ hκT
  have hU₂ : ∀ y ∈ T, κ * y * κ⁻¹ * y⁻¹ ∈ normIn T T₂ :=
    comm_mem_normIn_of_index_two hκT hκT₂ (by rw [e1]; exact hcT)
  have hV₂ := conj_mem_normIn_of_mem hκT hκT₂
  have hU₁₂ : ∀ y ∈ T₁, κ * y * κ⁻¹ * y⁻¹ ∈ normIn T₁ T₂ :=
    comm_mem_normIn_of_index_two hκT₁ hκT₂ (by rw [e2]; exact hcT₁)
  have hV₁₂ := conj_mem_normIn_of_mem hκT₁ hκT₂
  obtain ⟨t, ht, htL⟩ := exists_mem_not_mem_of_card_lt (A := normIn T T₁) (B := T) (by omega)
  obtain ⟨t₁, ht₁, ht₁L⟩ := exists_mem_not_mem_of_card_lt (A := normIn T₁ T) (B := T₁)
    (by omega)
  obtain ⟨t₂, ht₂, ht₂L⟩ := exists_mem_not_mem_of_card_lt (A := normIn T₂ T) (B := T₂)
    (by omega)
  have htL₂ : t ∉ normIn T T₂ := by rw [e1]; exact htL
  have ht₁L₂ : t₁ ∉ normIn T₁ T₂ := by rw [e2]; exact ht₁L
  have htM₂ : t ∉ cfgM T T₂ := fun hM => htL₂ (by rw [← hc₂.inf_cfgM]; exact ⟨ht, hM⟩)
  have hℓ₂ : ℓ ∈ normIn T T₂ := by rw [e1]; exact hℓ
  obtain ⟨a', ha', ha't⟩ := hS₂.exists_mem_normIn₁_conj_eq ht htM₂ hℓ₂
  have ha'c : ⁅t, a'⁆ = ℓ := commutator_eq_of_conj_eq h.pair.wc.1 ht (normIn_le T T₁ hℓ) ha't
  have ha'κ : κ * a' ≠ a' * κ := fun hc => hℓκ (by
    have := (hc₂.comm_mem_centralizer_iff hU₂ hV₂ ht htL₂ ha').1 hc
    rwa [ha'c] at this)
  have hconst₁ := hc₁.const_transfer hU₁ hV₁ ht htL hconst
  have hNab := h.isElemAbelian_sec4N
  have ha'₁ : a' ∈ normIn T₂ T₁ := by rw [← e3]; exact ha'
  have hℓ₁m : ⁅t₁, ℓ⁆ ∈ normIn T₁ T := hc₁.symm.comm_mem_normIn ht₁ hℓ
  have hℓ₁κ : κ * ⁅t₁, ℓ⁆ ≠ ⁅t₁, ℓ⁆ * κ := fun hc => hℓκ
    ((hc₁.symm.comm_mem_centralizer_iff hU₁' hV₁' ht₁ ht₁L hℓ).2 hc)
  have ha₁m : ⁅t₁, a'⁆ ∈ normIn T₁ T := by
    rw [← e2]
    exact hc₁₂.comm_mem_normIn ht₁ ha'₁
  have ha₁κ : κ * ⁅t₁, a'⁆ ≠ ⁅t₁, a'⁆ * κ := fun hc => ha'κ
    ((hc₁₂.comm_mem_centralizer_iff hU₁₂ hV₁₂ ht₁ ht₁L₂ ha'₁).2 hc)
  have huκL : ⁅κ, ℓ⁆ ∈ normIn T T₁ :=
    (normIn T T₁).mul_mem (hV₁' ℓ hℓ) ((normIn T T₁).inv_mem hℓ)
  have hu₁L : ⁅κ, ⁅t₁, ℓ⁆⁆ ∈ normIn T₁ T :=
    (normIn T₁ T).mul_mem (hV₁ _ hℓ₁m) ((normIn T₁ T).inv_mem hℓ₁m)
  have hu₂L : ⁅κ, a'⁆ ∈ normIn T₂ T :=
    (normIn T₂ T).mul_mem (hV₂ a' ha') ((normIn T₂ T).inv_mem ha')
  have R1 : t * ⁅κ, ℓ⁆ * t⁻¹ = ⁅κ, ℓ⁆ :=
    mul_inv_eq_iff_eq_mul.2 (elemAbelian_mul_comm h.pair.wc.1 ht (normIn_le T T₁ huκL))
  have R3 : t * ⁅κ, a'⁆ * t⁻¹ = ⁅κ, ℓ⁆ * ⁅κ, a'⁆ := by
    have := hc₂.conj_commutator_eq hU₂ ht ha' (hV₂ a' ha')
    rwa [ha'c] at this
  have R4 : t₁ * ⁅κ, ℓ⁆ * t₁⁻¹ = ⁅κ, ⁅t₁, ℓ⁆⁆ * ⁅κ, ℓ⁆ :=
    hc₁.symm.conj_commutator_eq hU₁' ht₁ hℓ (hV₁' ℓ hℓ)
  have R6 : t₁ * ⁅κ, a'⁆ * t₁⁻¹ = ⁅κ, ⁅t₁, ℓ⁆⁆ * ⁅κ, a'⁆ := by
    have := hc₁₂.conj_commutator_eq hU₁₂ ht₁ ha'₁ (hV₁₂ a' ha'₁)
    rwa [hconst₁ _ ha₁m _ hℓ₁m ha₁κ hℓ₁κ] at this
  have R9 : t₂ * ⁅κ, a'⁆ * t₂⁻¹ = ⁅κ, a'⁆ :=
    mul_inv_eq_iff_eq_mul.2 (elemAbelian_mul_comm h.isWC₂.1 ht₂ (normIn_le T₂ T hu₂L))
  have hz := z_fixes_a (elemAbelian_mul_self hNab (normIn_le_sec4N_left huκL))
    (elemAbelian_mul_self hNab (normIn_le_sec4N_mid hu₁L))
    (elemAbelian_mul_comm hNab (normIn_le_sec4N_left huκL) (normIn_le_sec4N_mid hu₁L)) R1 R3 R4
    R6 R9
  have h1 := h.fixed_eq_one ht ht₁ ht₁L ht₂ ht₂L hu₂L hz
  exact ha'κ (commutatorElement_eq_one_iff_mul_comm.1 h1)

end CFSG.CGT.Timmesfeld75
