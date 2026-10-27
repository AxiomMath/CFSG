module

public import CFSG.ClassicalGroups.F2Fixed
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.ClassicalGroups.F2Fixed

open CFSG.LocalAnalysis.ComponentInitial Matrix
open scoped MatrixGroups

section Subgroups

variable (E : Type*) [Field E]

@[expose] def sl2UpperSub : Subgroup SL(2, E) where
  carrier := Set.range (sl2Upper E)
  one_mem' := ⟨0, sl2Upper_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, sl2Upper_add a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, sl2Upper_neg a⟩

@[expose] def sl2LowerSub : Subgroup SL(2, E) where
  carrier := Set.range (sl2Lower E)
  one_mem' := ⟨0, sl2Lower_zero⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, sl2Lower_add a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, sl2Lower_neg a⟩

variable {E}

theorem sl2Upper_mem_sub (s : E) : sl2Upper E s ∈ sl2UpperSub E := ⟨s, rfl⟩

theorem sl2Lower_mem_sub (t : E) : sl2Lower E t ∈ sl2LowerSub E := ⟨t, rfl⟩

theorem sl2Upper_mul_self [CharP E 2] (s : E) : sl2Upper E s * sl2Upper E s = 1 := by
  rw [← sl2Upper_add, CharTwo.add_self_eq_zero, sl2Upper_zero]

theorem sl2Lower_mul_self [CharP E 2] (t : E) : sl2Lower E t * sl2Lower E t = 1 := by
  rw [← sl2Lower_add, CharTwo.add_self_eq_zero, sl2Lower_zero]

theorem sl2Weyl_mul_lower (t : Eˣ) (d : E) :
    sl2Weyl E t * sl2Lower E d = sl2Upper E (-(t : E) ^ 2 * d) * sl2Weyl E t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  field_simp

theorem sl2Weyl_eq_lower_upper_lower (t : Eˣ) :
    sl2Weyl E t = sl2Lower E (-((t⁻¹ : Eˣ) : E)) * sl2Upper E t *
      sl2Lower E (-((t⁻¹ : Eˣ) : E)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp
  all_goals ring

theorem closure_upper_insert_lower [CharP E 2] {c : E} (hc : c ≠ 0) :
    Subgroup.closure ((sl2UpperSub E : Set SL(2, E)) ∪ {sl2Lower E c}) = ⊤ := by
  set H := Subgroup.closure ((sl2UpperSub E : Set SL(2, E)) ∪ {sl2Lower E c}) with hH
  have hU : ∀ s, sl2Upper E s ∈ H := fun s =>
    Subgroup.subset_closure (Or.inl (sl2Upper_mem_sub s))
  have hLc : sl2Lower E c ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hW : sl2Weyl E (Units.mk0 c⁻¹ (inv_ne_zero hc)) ∈ H := by
    rw [sl2Weyl_eq]
    have h1 : ((Units.mk0 c⁻¹ (inv_ne_zero hc) : Eˣ) : E) = c⁻¹ := rfl
    have h2 : (((Units.mk0 c⁻¹ (inv_ne_zero hc))⁻¹ : Eˣ) : E) = c := by
      rw [Units.val_inv_eq_inv_val, h1, inv_inv]
    rw [h2, CharTwo.neg_eq]
    exact mul_mem (mul_mem (hU _) hLc) (hU _)
  have hL : ∀ d, sl2Lower E d ∈ H := by
    intro d
    have h2 : (((Units.mk0 c⁻¹ (inv_ne_zero hc))⁻¹ : Eˣ) : E) = c := by
      rw [Units.val_inv_eq_inv_val]; exact inv_inv c
    have key := sl2Weyl_mul_upper (Units.mk0 c⁻¹ (inv_ne_zero hc)) (d / c ^ 2)
    rw [h2] at key
    have e : sl2Lower E d = sl2Weyl E (Units.mk0 c⁻¹ (inv_ne_zero hc)) * sl2Upper E (d / c ^ 2) *
        (sl2Weyl E (Units.mk0 c⁻¹ (inv_ne_zero hc)))⁻¹ := by
      rw [key, mul_assoc, mul_inv_cancel, mul_one]
      congr 2
      rw [CharTwo.neg_eq]
      field_simp
    rw [e]
    exact mul_mem (mul_mem hW (hU _)) (inv_mem hW)
  refine eq_top_iff.mpr ?_
  rw [← sl2_closure_upper_lower (K := E), Subgroup.closure_le]
  rintro _ (⟨s, rfl⟩ | ⟨t, rfl⟩)
  · exact hU s
  · exact hL t

theorem closure_lower_insert_upper [CharP E 2] {c : E} (hc : c ≠ 0) :
    Subgroup.closure ((sl2LowerSub E : Set SL(2, E)) ∪ {sl2Upper E c}) = ⊤ := by
  set H := Subgroup.closure ((sl2LowerSub E : Set SL(2, E)) ∪ {sl2Upper E c}) with hH
  have hL : ∀ s, sl2Lower E s ∈ H := fun s =>
    Subgroup.subset_closure (Or.inl (sl2Lower_mem_sub s))
  have hUc : sl2Upper E c ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hW : sl2Weyl E (Units.mk0 c hc) ∈ H := by
    rw [sl2Weyl_eq_lower_upper_lower]
    exact mul_mem (mul_mem (hL _) hUc) (hL _)
  have hU : ∀ d, sl2Upper E d ∈ H := by
    intro d
    have key := sl2Weyl_mul_lower (Units.mk0 c hc) (d / c ^ 2)
    have e : sl2Upper E d = sl2Weyl E (Units.mk0 c hc) * sl2Lower E (d / c ^ 2) *
        (sl2Weyl E (Units.mk0 c hc))⁻¹ := by
      rw [key, mul_assoc, mul_inv_cancel, mul_one]
      congr 2
      rw [CharTwo.neg_eq]
      show d = (c : E) ^ 2 * (d / c ^ 2)
      field_simp
    rw [e]
    exact mul_mem (mul_mem hW (hL _)) (inv_mem hW)
  refine eq_top_iff.mpr ?_
  rw [← sl2_closure_upper_lower (K := E), Subgroup.closure_le]
  rintro _ (⟨s, rfl⟩ | ⟨t, rfl⟩)
  · exact hU s
  · exact hL t

end Subgroups

section Factorization

variable {E : Type*} [Field E]

theorem entry_conj_lower (w : SL(2, E)) (r : E) :
    ((sl2Lower E r)⁻¹ * w * sl2Lower E r : SL(2, E)) 0 0 =
      (w : Matrix (Fin 2) (Fin 2) E) 0 0 + (w : Matrix (Fin 2) (Fin 2) E) 0 1 * r := by
  rw [← sl2Lower_neg]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem entry_conj_upper (w : SL(2, E)) (r : E) :
    ((sl2Upper E r)⁻¹ * w * sl2Upper E r : SL(2, E)) 0 0 =
      (w : Matrix (Fin 2) (Fin 2) E) 0 0 - r * (w : Matrix (Fin 2) (Fin 2) E) 1 0 := by
  rw [← sl2Upper_neg]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

theorem entry01_conj_upper (w : SL(2, E)) (r : E) :
    ((sl2Upper E r)⁻¹ * w * sl2Upper E r : SL(2, E)) 0 1 =
      r * ((w : Matrix (Fin 2) (Fin 2) E) 0 0 - r * (w : Matrix (Fin 2) (Fin 2) E) 1 0) +
        (w : Matrix (Fin 2) (Fin 2) E) 0 1 - r * (w : Matrix (Fin 2) (Fin 2) E) 1 1 := by
  rw [← sl2Upper_neg]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  ring

theorem eq_lower_mul_upper_of_entry_one (M : SL(2, E))
    (h : (M : Matrix (Fin 2) (Fin 2) E) 0 0 = 1) :
    M = sl2Lower E ((M : Matrix (Fin 2) (Fin 2) E) 1 0) *
      sl2Upper E ((M : Matrix (Fin 2) (Fin 2) E) 0 1) := by
  have hdet := M.2
  rw [det_fin_two, h] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h]
  linear_combination hdet

theorem exists_conj_entry_one [CharP E 2] {w : SL(2, E)} (hw : w ≠ 1) :
    ∃ g : SL(2, E), (g⁻¹ * w * g : SL(2, E)) 0 0 = 1 := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨a, b, c, d, hm⟩ : ∃ a b c d : E, (w : Matrix (Fin 2) (Fin 2) E) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet := w.2
  rw [hm, det_fin_two_of] at hdet
  have ha : (w : Matrix (Fin 2) (Fin 2) E) 0 0 = a := by rw [hm]; rfl
  have hb : (w : Matrix (Fin 2) (Fin 2) E) 0 1 = b := by rw [hm]; rfl
  have hc : (w : Matrix (Fin 2) (Fin 2) E) 1 0 = c := by rw [hm]; rfl
  have hd : (w : Matrix (Fin 2) (Fin 2) E) 1 1 = d := by rw [hm]; rfl
  have lowercase : ∀ (a' b' : E), b' ≠ 0 → ∀ w' : SL(2, E),
      (w' : Matrix (Fin 2) (Fin 2) E) 0 1 = b' → (w' : Matrix (Fin 2) (Fin 2) E) 0 0 = a' →
        ∃ g : SL(2, E), (g⁻¹ * w' * g : SL(2, E)) 0 0 = 1 := by
    intro a' b' hb0 w' hb' ha'
    refine ⟨sl2Lower E ((1 + a') / b'), ?_⟩
    rw [entry_conj_lower, ha', hb', mul_div_cancel₀ _ hb0]
    linear_combination a' * h2
  by_cases hb0 : b = 0
  · by_cases hc0 : c = 0
    ·
      have had : a * d = 1 := by rw [hb0, hc0] at hdet; linear_combination hdet
      have hane : a ≠ d := by
        rintro rfl
        have hsq : (a - 1) ^ 2 = 0 := by linear_combination had + (1 - a) * h2
        have ha1 : a = 1 := by
          have := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
          linear_combination this
        apply hw
        have hd1 : a = 1 := ha1
        ext i j
        rw [hm]
        fin_cases i <;> fin_cases j <;> simp [hb0, hc0, hd1]
      set w₁ : SL(2, E) := (sl2Upper E 1)⁻¹ * w * sl2Upper E 1 with hw₁
      have h00 : (w₁ : Matrix (Fin 2) (Fin 2) E) 0 0 = a := by
        rw [hw₁, entry_conj_upper, ha, hc, hc0]; ring
      have h01 : (w₁ : Matrix (Fin 2) (Fin 2) E) 0 1 = a - d := by
        rw [hw₁, entry01_conj_upper, ha, hb, hc, hd, hb0, hc0]; ring
      have hne : a - d ≠ 0 := sub_ne_zero.mpr hane
      obtain ⟨g₂, hg₂⟩ := lowercase a (a - d) hne w₁ h01 h00
      refine ⟨sl2Upper E 1 * g₂, ?_⟩
      have e : (sl2Upper E 1 * g₂)⁻¹ * w * (sl2Upper E 1 * g₂) = g₂⁻¹ * w₁ * g₂ := by
        rw [hw₁]; group
      rw [e]; exact hg₂
    · refine ⟨sl2Upper E ((1 + a) / c), ?_⟩
      rw [entry_conj_upper, ha, hc, div_mul_cancel₀ _ hc0]
      linear_combination (-1 : E) * h2
  · exact lowercase a b hb0 w hb ha

end Factorization

section Main

variable {E : Type*} [Field E] [Finite E] [CharP E 2]
  {M : Type*} [AddCommGroup M] [Finite M] [DistribMulAction SL(2, E) M]

theorem card_sl2 : Nat.card SL(2, E) = Nat.card E * (Nat.card E ^ 2 - 1) := by
  let := Fintype.ofFinite E
  have hq : 1 < Fintype.card E := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card E ^ 2 - Fintype.card E =
      Fintype.card E * (Fintype.card E - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem fixedSub_lower_mul_upper_eq_bot (h2 : ∀ m : M, m + m = 0)
    (hdec : IsCompl (fixedSub M (sl2UpperSub E : Set SL(2, E)))
      (fixedSub M (sl2LowerSub E : Set SL(2, E))))
    {t s : E} (ht : t ≠ 0) (hs : s ≠ 0) :
    fixedSub M {sl2Lower E t * sl2Upper E s} = ⊥ := by
  have hx := fixedSub_singleton_eq (L₁ := sl2UpperSub E) (L₂ := sl2LowerSub E)
    (x := sl2Lower E t) (sl2Lower_mem_sub t) (closure_upper_insert_lower ht) hdec
  have hy := fixedSub_singleton_eq (L₁ := sl2LowerSub E) (L₂ := sl2UpperSub E)
    (x := sl2Upper E s) (sl2Upper_mem_sub s) (closure_lower_insert_upper hs) hdec.symm
  refine fixedSub_mul_eq_bot h2 (sl2Lower_mul_self t) (sl2Upper_mul_self s) ?_
  rw [hx, hy, inf_comm]
  exact hdec.inf_eq_bot

theorem dvd_card_sub_one_of_prime_dvd (h2 : ∀ m : M, m + m = 0)
    (hdec : IsCompl (fixedSub M (sl2UpperSub E : Set SL(2, E)))
      (fixedSub M (sl2LowerSub E : Set SL(2, E))))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrE : r ∣ Nat.card E ^ 2 - 1) :
    r ∣ Nat.card M - 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd : r ∣ Nat.card SL(2, E) := by
    rw [card_sl2]; exact Dvd.dvd.mul_left hrE _
  obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hw₀r : w₀ ^ r = 1 := by rw [← hw₀]; exact pow_orderOf_eq_one w₀
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hw₀
    exact hr.one_lt.ne hw₀
  obtain ⟨g, hg⟩ := exists_conj_entry_one hw₀1
  set w : SL(2, E) := g⁻¹ * w₀ * g with hwdef
  have hwr : w ^ r = 1 := by
    have h := conj_pow (a := g⁻¹) (b := w₀) (i := r)
    rw [inv_inv] at h
    rw [hwdef, h, hw₀r, mul_one, inv_mul_cancel]
  have hw1 : w ≠ 1 := by
    intro h
    apply hw₀1
    have : g⁻¹ * w₀ * g = 1 := h
    calc w₀ = g * (g⁻¹ * w₀ * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hwe := eq_lower_mul_upper_of_entry_one w hg
  set t := (w : Matrix (Fin 2) (Fin 2) E) 1 0 with ht
  set s := (w : Matrix (Fin 2) (Fin 2) E) 0 1 with hs
  have hodd : ∀ x : SL(2, E), x * x = 1 → x ^ r = 1 → x = 1 := by
    intro x hx hxr
    obtain ⟨k, hk⟩ : ∃ k, r = 2 * k + 1 := by
      have := hr.eq_one_or_self_of_dvd 2
      rcases hr.eq_two_or_odd' with h | h
      · exact absurd h hr2
      · exact h.exists_bit1
    have : x ^ r = x := by
      rw [hk, pow_succ, pow_mul, sq, hx, one_pow, one_mul]
    rw [← this]; exact hxr
  have ht0 : t ≠ 0 := by
    intro h0
    apply hw1
    have : w = sl2Upper E s := by
      rw [hwe, h0, sl2Lower_zero, one_mul]
    rw [this] at hwr ⊢
    exact hodd _ (sl2Upper_mul_self s) hwr
  have hs0 : s ≠ 0 := by
    intro h0
    apply hw1
    have : w = sl2Lower E t := by
      rw [hwe, h0, sl2Upper_zero, mul_one]
    rw [this] at hwr ⊢
    exact hodd _ (sl2Lower_mul_self t) hwr
  have hfix : fixedSub M {w} = ⊥ := by
    rw [hwe]
    exact fixedSub_lower_mul_upper_eq_bot h2 hdec ht0 hs0
  exact dvd_card_sub_one_of_fixedSub_eq_bot hr hwr hfix

theorem sl2_card_eq_pow (h2 : ∀ m : M, m + m = 0)
    (hdec : IsCompl (fixedSub M (sl2UpperSub E : Set SL(2, E)))
      (fixedSub M (sl2LowerSub E : Set SL(2, E)))) :
    ∃ n : ℕ, Nat.card M = Nat.card E ^ (2 * n) := by
  obtain ⟨N, hN⟩ := exists_card_eq_two_pow h2
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card E = 2 ^ f := by
    let := Fintype.ofFinite E
    obtain ⟨n, -, hn⟩ := FiniteField.card E 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · exfalso
      have := Finite.one_lt_card (α := E)
      rw [h, pow_zero] at hf
      omega
    · exact h
  have key : 2 * f ∣ N := by
    refine dvd_of_forall_prime_dvd (by omega) fun r hr hrd => ?_
    have hr2 : r ≠ 2 := by
      rintro rfl
      have h1 : 2 ∣ 2 ^ (2 * f) := dvd_pow_self 2 (by omega)
      have h3 := Nat.dvd_sub h1 hrd
      rw [show 2 ^ (2 * f) - (2 ^ (2 * f) - 1) = 1 by
        have := Nat.one_le_two_pow (n := 2 * f); omega] at h3
      exact absurd h3 (by norm_num)
    have hrE : r ∣ Nat.card E ^ 2 - 1 := by
      rw [hf, ← pow_mul, mul_comm]; exact hrd
    have := dvd_card_sub_one_of_prime_dvd h2 hdec hr hr2 hrE
    rwa [hN] at this
  obtain ⟨n, hn⟩ := key
  refine ⟨n, ?_⟩
  rw [hN, hn, hf, ← pow_mul]
  ring_nf

end Main

end CFSG.ClassicalGroups.F2Fixed
