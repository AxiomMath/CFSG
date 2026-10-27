module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Std

public section

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap CFSG.LieType.Universal.Spin Finset

@[expose] def typeSign (ε : Bool) (n : ℕ) : ℕ := if ε then 2 ^ n - 1 else 2 ^ n + 1

@[expose] def chi2 (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma chi2_add (a b : ZMod 2) : chi2 (a + b) = chi2 a * chi2 b := by
  revert a b; decide

lemma chi2_sum {α : Type*} (s : Finset α) (f : α → ZMod 2) :
    chi2 (∑ i ∈ s, f i) = ∏ i ∈ s, chi2 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi2]
  | insert a s ha ih => rw [sum_insert ha, prod_insert ha, chi2_add, ih]

lemma two_mul_card_zeros {α : Type*} [Fintype α] (f : α → ZMod 2) :
    2 * ((Fintype.card {a // f a = 0} : ℕ) : ℤ) = Fintype.card α + ∑ a, chi2 (f a) := by
  classical
  have h1 : ∑ a, chi2 (f a) =
      ((univ.filter fun a => f a = 0).card : ℤ) - ((univ.filter fun a => ¬ f a = 0).card : ℤ) := by
    simp only [chi2]
    rw [sum_ite]
    simp [sub_eq_add_neg]
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (fun a => f a = 0)
  rw [h1, Fintype.card_subtype, ← Finset.card_univ]
  have h3 : ((univ.filter fun a => f a = 0).card : ℤ) +
      ((univ.filter fun a => ¬ f a = 0).card : ℤ) = (univ : Finset α).card := by exact_mod_cast h2
  linarith

lemma sum_sumArrow {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : (α → ZMod 2) → ℤ) (G : (β → ZMod 2) → ℤ) :
    ∑ v : α ⊕ β → ZMod 2, F (v ∘ Sum.inl) * G (v ∘ Sum.inr) =
      (∑ x, F x) * ∑ y, G y := by
  rw [← Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow α β (ZMod 2)).symm
    (fun p : (α → ZMod 2) × (β → ZMod 2) => F p.1 * G p.2)
    (fun v => F (v ∘ Sum.inl) * G (v ∘ Sum.inr))]
  · rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  · intro p
    simp [Equiv.sumArrowEquivProdArrow, Function.comp_def]

lemma sum_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ZMod 2 × ZMod 2 → ℤ) :
    ∑ v : ι ⊕ ι → ZMod 2, ∏ i, h (v (.inl i), v (.inr i)) = (∑ a, h a) ^ Fintype.card ι := by
  let e : (ι ⊕ ι → ZMod 2) ≃ (ι → ZMod 2 × ZMod 2) :=
    { toFun := fun v i => (v (.inl i), v (.inr i))
      invFun := fun w => Sum.elim (fun i => (w i).1) (fun i => (w i).2)
      left_inv := fun v => by ext (i | i) <;> rfl
      right_inv := fun w => by ext i <;> rfl }
  refine (Fintype.sum_equiv e _ (fun w : ι → ZMod 2 × ZMod 2 => ∏ i, h (w i))
    (fun v => rfl)).trans ?_
  have := prod_univ_sum (fun _ : ι => (univ : Finset (ZMod 2 × ZMod 2))) (fun _ a => h a)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp

lemma gauss_plus (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∑ v : ι ⊕ ι → ZMod 2, chi2 (∑ i, v (.inl i) * v (.inr i)) = 2 ^ Fintype.card ι := by
  have h : ∑ a : ZMod 2 × ZMod 2, chi2 (a.1 * a.2) = 2 := by decide
  simp only [chi2_sum]
  rw [sum_prod_pi (fun a => chi2 (a.1 * a.2)), h]

lemma gauss_aniso :
    ∑ u : Fin 2 → ZMod 2, chi2 (u 0 ^ 2 + 1 * u 0 * u 1 + 1 * u 1 ^ 2) = -2 := by
  decide

lemma card_zeros_eq_of_sum {α : Type*} [Fintype α] (f : α → ZMod 2) {S : ℤ}
    (hS : ∑ a, chi2 (f a) = S) :
    2 * ((Fintype.card {a // f a = 0} : ℕ) : ℤ) = Fintype.card α + S := by
  rw [two_mul_card_zeros, hS]

lemma card_zeros_quadPlus_aux (m : ℕ) :
    2 * ((Nat.card {v : Fin m ⊕ Fin m → ZMod 2 // quadPlus m (ZMod 2) v = 0} : ℕ) : ℤ) =
      4 ^ m + 2 ^ m := by
  rw [Nat.card_eq_fintype_card]
  have := card_zeros_eq_of_sum (fun v : Fin m ⊕ Fin m → ZMod 2 => quadPlus m (ZMod 2) v)
    (S := 2 ^ m) (by
      simp only [quadPlus_apply]
      simpa using gauss_plus (Fin m))
  rw [this]
  simp [Fintype.card_sum]
  rw [← two_mul, pow_mul]
  norm_num

lemma gauss_minus (m : ℕ) :
    ∑ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2,
      chi2 (quadMinus m (ZMod 2) 1 1 v) = -2 * 2 ^ (m - 1) := by
  let ψ : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) ≃
      ((Fin (m - 1) ⊕ Fin (m - 1)) ⊕ Fin 2 → ZMod 2) :=
    (Equiv.sumAssoc (Fin (m - 1)) (Fin (m - 1)) (Fin 2)).symm.arrowCongr (Equiv.refl _)
  refine (Fintype.sum_equiv ψ _
    (fun w => chi2 (∑ i, (w ∘ Sum.inl) (.inl i) * (w ∘ Sum.inl) (.inr i)) *
      chi2 ((w ∘ Sum.inr) 0 ^ 2 + 1 * (w ∘ Sum.inr) 0 * (w ∘ Sum.inr) 1 +
        1 * (w ∘ Sum.inr) 1 ^ 2)) (fun v => ?_)).trans ?_
  · rw [quadMinus_apply, ← chi2_add]
    congr 1
    simp [ψ, Equiv.arrowCongr, Function.comp_def]
    ring
  · rw [sum_sumArrow (fun x : Fin (m - 1) ⊕ Fin (m - 1) → ZMod 2 =>
      chi2 (∑ i, x (.inl i) * x (.inr i)))
      (fun y : Fin 2 → ZMod 2 => chi2 (y 0 ^ 2 + 1 * y 0 * y 1 + 1 * y 1 ^ 2))]
    have h1 : ∑ x : Fin (m - 1) ⊕ Fin (m - 1) → ZMod 2, chi2 (∑ i, x (.inl i) * x (.inr i)) =
        2 ^ (m - 1) := by simpa using gauss_plus (Fin (m - 1))
    rw [h1, gauss_aniso]
    ring

lemma card_zeros_quadMinus_aux {m : ℕ} (hm : 1 ≤ m) :
    2 * ((Nat.card {v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2 //
        quadMinus m (ZMod 2) 1 1 v = 0} : ℕ) : ℤ) = 4 ^ m - 2 ^ m := by
  rw [Nat.card_eq_fintype_card]
  have := card_zeros_eq_of_sum
    (fun v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2 => quadMinus m (ZMod 2) 1 1 v)
    (S := -2 * 2 ^ (m - 1)) (gauss_minus m)
  rw [this]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp [Fintype.card_sum]
  rw [show (4 : ℤ) ^ (k + 1) = 2 ^ (k + (k + 2)) by
    rw [show k + (k + 2) = 2 * (k + 1) by ring, pow_mul]; norm_num]
  ring

theorem card_zeros_quadPlus {m : ℕ} (hm : 1 ≤ m) :
    Nat.card {v : Fin m ⊕ Fin m → ZMod 2 // quadPlus m (ZMod 2) v = 0} =
      2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  have h := card_zeros_quadPlus_aux m
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have h2 : (2 * (k + 1) - 1) = 2 * k + 1 := by omega
  rw [h2]
  have : ((Nat.card {v : Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2 //
      quadPlus (k + 1) (ZMod 2) v = 0} : ℕ) : ℤ) = ((2 ^ (2 * k + 1) + 2 ^ (k + 1 - 1) : ℕ) : ℤ) := by
    push_cast
    try simp only [Nat.add_sub_cancel]
    have : (4 : ℤ) ^ (k + 1) = 2 * 2 ^ (2 * k + 1) := by
      rw [pow_succ, pow_succ, pow_mul]; norm_num; ring
    rw [this, show (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k by ring] at h
    linarith
  exact_mod_cast this

theorem card_zeros_quadMinus {m : ℕ} (hm : 1 ≤ m) :
    Nat.card {v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2 //
        quadMinus m (ZMod 2) 1 1 v = 0} = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  have h := card_zeros_quadMinus_aux hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  have h2 : (2 * (k + 1) - 1) = 2 * k + 1 := by omega
  rw [h2]
  have hle : 2 ^ (k + 1 - 1) ≤ 2 ^ (2 * k + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have : ((Nat.card {v : Fin (k + 1 - 1) ⊕ Fin (k + 1 - 1) ⊕ Fin 2 → ZMod 2 //
      quadMinus (k + 1) (ZMod 2) 1 1 v = 0} : ℕ) : ℤ) =
      ((2 ^ (2 * k + 1) - 2 ^ (k + 1 - 1) : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle]
    push_cast
    try simp only [Nat.add_sub_cancel]
    have : (4 : ℤ) ^ (k + 1) = 2 * 2 ^ (2 * k + 1) := by
      rw [pow_succ, pow_succ, pow_mul]; norm_num; ring
    rw [this, show (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k by ring] at h
    linarith
  exact_mod_cast this

theorem card_zeros_of_isStdSpace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {Q : QuadraticForm (ZMod 2) V} {ε : Bool} {m : ℕ} (hm : 1 ≤ m) (h : IsStdSpace ε Q m) :
    (Nat.card {v : V // Q v = 0} : ℤ) =
      2 ^ (2 * m - 1) + (if ε then 1 else -1) * 2 ^ (m - 1) := by
  cases ε
  · obtain ⟨φ, hφ⟩ := h
    have e : {v : V // Q v = 0} ≃
        {v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2 // quadMinus m (ZMod 2) 1 1 v = 0} :=
      φ.toEquiv.subtypeEquiv fun v => by simp [hφ v]
    rw [Nat.card_congr e, card_zeros_quadMinus hm]
    have hle : 2 ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.cast_sub hle]
    simp [sub_eq_add_neg]
  · obtain ⟨φ, hφ⟩ := h
    have e : {v : V // Q v = 0} ≃
        {v : Fin m ⊕ Fin m → ZMod 2 // quadPlus m (ZMod 2) v = 0} :=
      φ.toEquiv.subtypeEquiv fun v => by simp [hφ v]
    rw [Nat.card_congr e, card_zeros_quadPlus hm]
    simp

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
