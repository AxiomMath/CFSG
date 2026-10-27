module

public import CFSG.ClassicalGroups.Orthogonal.CharTwo
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

variable {K : Type*} [Field K] {n : ℕ}

section Plus

theorem polar_single_inl_quadPlus (i : Fin n) (y : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (Pi.single (Sum.inl i) 1) y = y (Sum.inr i) := by
  rw [polar_comm, polar_quadPlus_single_inl]

theorem polar_single_inr_quadPlus (i : Fin n) (y : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (Pi.single (Sum.inr i) 1) y = y (Sum.inl i) := by
  rw [polar_comm, polar_quadPlus_single_inr]

theorem quadPlus_single (k : Fin n ⊕ Fin n) : quadPlus n K (Pi.single k 1) = 0 := by
  rw [quadPlus_apply]
  rcases k with i | i <;> simp [Pi.single_apply]

variable (K) in
@[expose] def plusPair (i : Fin n) : HypPair (quadPlus n K) where
  e := Pi.single (Sum.inl i) 1
  f := Pi.single (Sum.inr i) 1
  Q_e := quadPlus_single _
  Q_f := quadPlus_single _
  polar_ef := by rw [polar_single_inl_quadPlus]; simp

theorem plusPair_e (i : Fin n) : (plusPair K i).e = Pi.single (Sum.inl i) 1 := rfl

theorem plusPair_f (i : Fin n) : (plusPair K i).f = Pi.single (Sum.inr i) 1 := rfl

theorem plusPair_orth {i j : Fin n} (hij : i ≠ j) : (plusPair K i).Orth (plusPair K j) where
  ee := by rw [plusPair_e, plusPair_e, polar_single_inl_quadPlus]; simp
  ef := by rw [plusPair_e, plusPair_f, polar_single_inl_quadPlus]; simp [hij]
  fe := by rw [plusPair_f, plusPair_e, polar_single_inr_quadPlus]; simp [hij]
  ff := by rw [plusPair_f, plusPair_f, polar_single_inr_quadPlus]; simp

variable (K) in
def plusFamily (hn : 0 < n) (i : ℕ) : HypPair (quadPlus n K) :=
  if h : i < n then plusPair K ⟨i, h⟩ else plusPair K ⟨0, hn⟩

theorem plusFamily_of_lt (hn : 0 < n) {i : ℕ} (h : i < n) :
    plusFamily K hn i = plusPair K ⟨i, h⟩ := by
  rw [plusFamily, dite_eq_left h]

theorem plusFamily_orth (hn : 0 < n) :
    ∀ i j, i < n → j < n → i ≠ j → (plusFamily K hn i).Orth (plusFamily K hn j) := by
  intro i j hi hj hij
  rw [plusFamily_of_lt hn hi, plusFamily_of_lt hn hj]
  exact plusPair_orth fun h => hij (congrArg Fin.val h)

theorem eq_zero_of_mem_tailSpace_plusFamily (hn : 0 < n) {x : Fin n ⊕ Fin n → K}
    (hx : x ∈ tailSpace (plusFamily K hn) n) : x = 0 := by
  rw [mem_tailSpace] at hx
  funext k
  rcases k with i | i
  · have := (hx i i.2).2
    rwa [plusFamily_of_lt hn i.2, plusPair_f, polar_single_inr_quadPlus] at this
  · have := (hx i i.2).1
    rwa [plusFamily_of_lt hn i.2, plusPair_e, polar_single_inl_quadPlus] at this

end Plus

section Odd

theorem polar_single_inl_quadOdd (i : Fin n) (y : Fin n ⊕ Fin n ⊕ Unit → K) :
    polar (quadOdd n K) (Pi.single (Sum.inl i) 1) y = y (Sum.inr (Sum.inl i)) := by
  rw [polar_comm, polar_quadOdd_single_inl]

theorem polar_single_inr_quadOdd (i : Fin n) (y : Fin n ⊕ Fin n ⊕ Unit → K) :
    polar (quadOdd n K) (Pi.single (Sum.inr (Sum.inl i)) 1) y = y (Sum.inl i) := by
  rw [polar_comm, polar_quadOdd_single_inr_inl]

theorem quadOdd_single_inl (i : Fin n) : quadOdd n K (Pi.single (Sum.inl i) 1) = 0 := by
  rw [quadOdd_apply]
  simp [Pi.single_apply]

theorem quadOdd_single_inr (i : Fin n) :
    quadOdd n K (Pi.single (Sum.inr (Sum.inl i)) 1) = 0 := by
  rw [quadOdd_apply]
  simp [Pi.single_apply]

variable (K) in
@[expose] def oddPair (i : Fin n) : HypPair (quadOdd n K) where
  e := Pi.single (Sum.inl i) 1
  f := Pi.single (Sum.inr (Sum.inl i)) 1
  Q_e := quadOdd_single_inl i
  Q_f := quadOdd_single_inr i
  polar_ef := by rw [polar_single_inl_quadOdd]; simp

theorem oddPair_e (i : Fin n) : (oddPair K i).e = Pi.single (Sum.inl i) 1 := rfl

theorem oddPair_f (i : Fin n) : (oddPair K i).f = Pi.single (Sum.inr (Sum.inl i)) 1 := rfl

theorem oddPair_orth {i j : Fin n} (hij : i ≠ j) : (oddPair K i).Orth (oddPair K j) where
  ee := by rw [oddPair_e, oddPair_e, polar_single_inl_quadOdd]; simp
  ef := by rw [oddPair_e, oddPair_f, polar_single_inl_quadOdd]; simp [hij]
  fe := by rw [oddPair_f, oddPair_e, polar_single_inr_quadOdd]; simp [hij]
  ff := by rw [oddPair_f, oddPair_f, polar_single_inr_quadOdd]; simp

end Odd

section Minus

variable {b c : K}

theorem polar_single_inl_quadMinus (i : Fin (n - 1)) (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (quadMinus n K b c) (Pi.single (Sum.inl i) 1) y = y (Sum.inr (Sum.inl i)) := by
  rw [polar_comm, polar_quadMinus_single_inl]

theorem polar_single_inr_quadMinus (i : Fin (n - 1)) (y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    polar (quadMinus n K b c) (Pi.single (Sum.inr (Sum.inl i)) 1) y = y (Sum.inl i) := by
  rw [polar_comm, polar_quadMinus_single_inr_inl]

theorem quadMinus_single_inl (i : Fin (n - 1)) :
    quadMinus n K b c (Pi.single (Sum.inl i) 1) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

theorem quadMinus_single_inr (i : Fin (n - 1)) :
    quadMinus n K b c (Pi.single (Sum.inr (Sum.inl i)) 1) = 0 := by
  rw [quadMinus_apply]
  simp [Pi.single_apply]

variable (K b c) in
@[expose] def minusPair (i : Fin (n - 1)) : HypPair (quadMinus n K b c) where
  e := Pi.single (Sum.inl i) 1
  f := Pi.single (Sum.inr (Sum.inl i)) 1
  Q_e := quadMinus_single_inl i
  Q_f := quadMinus_single_inr i
  polar_ef := by rw [polar_single_inl_quadMinus]; simp

theorem minusPair_e (i : Fin (n - 1)) : (minusPair K b c i).e = Pi.single (Sum.inl i) 1 := rfl

theorem minusPair_f (i : Fin (n - 1)) :
    (minusPair K b c i).f = Pi.single (Sum.inr (Sum.inl i)) 1 := rfl

theorem minusPair_orth {i j : Fin (n - 1)} (hij : i ≠ j) :
    (minusPair K b c i).Orth (minusPair K b c j) where
  ee := by rw [minusPair_e, minusPair_e, polar_single_inl_quadMinus]; simp
  ef := by rw [minusPair_e, minusPair_f, polar_single_inl_quadMinus]; simp [hij]
  fe := by rw [minusPair_f, minusPair_e, polar_single_inr_quadMinus]; simp [hij]
  ff := by rw [minusPair_f, minusPair_f, polar_single_inr_quadMinus]; simp

variable (K b c) in
def minusFamily (hn : 0 < n - 1) (i : ℕ) : HypPair (quadMinus n K b c) :=
  if h : i < n - 1 then minusPair K b c ⟨i, h⟩ else minusPair K b c ⟨0, hn⟩

theorem minusFamily_of_lt (hn : 0 < n - 1) {i : ℕ} (h : i < n - 1) :
    minusFamily K b c hn i = minusPair K b c ⟨i, h⟩ := by
  rw [minusFamily, dite_eq_left h]

theorem minusFamily_orth (hn : 0 < n - 1) :
    ∀ i j, i < n - 1 → j < n - 1 → i ≠ j →
      (minusFamily K b c hn i).Orth (minusFamily K b c hn j) := by
  intro i j hi hj hij
  rw [minusFamily_of_lt hn hi, minusFamily_of_lt hn hj]
  exact minusPair_orth fun h => hij (congrArg Fin.val h)

theorem coord_eq_zero_of_mem_tailSpace_minusFamily (hn : 0 < n - 1)
    {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hx : x ∈ tailSpace (minusFamily K b c hn) (n - 1)) (i : Fin (n - 1)) :
    x (Sum.inl i) = 0 ∧ x (Sum.inr (Sum.inl i)) = 0 := by
  rw [mem_tailSpace] at hx
  constructor
  · have := (hx i i.2).2
    rwa [minusFamily_of_lt hn i.2, minusPair_f, polar_single_inr_quadMinus] at this
  · have := (hx i i.2).1
    rwa [minusFamily_of_lt hn i.2, minusPair_e, polar_single_inl_quadMinus] at this

theorem binary_eq_zero_of_irreducible (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {u v : K}
    (h : u ^ 2 + b * u * v + c * v ^ 2 = 0) : u = 0 ∧ v = 0 := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨?_, rfl⟩
    have : u ^ 2 = 0 := by linear_combination h
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  · exfalso
    apply hirr (u / v)
    field_simp
    linear_combination h

theorem eq_zero_of_mem_tailSpace_minusFamily (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn : 0 < n - 1) {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hx : x ∈ tailSpace (minusFamily K b c hn) (n - 1)) (hQ : quadMinus n K b c x = 0) :
    x = 0 := by
  have hc := coord_eq_zero_of_mem_tailSpace_minusFamily hn hx
  rw [quadMinus_apply, Finset.sum_eq_zero fun i _ => by rw [(hc i).1, zero_mul], zero_add] at hQ
  obtain ⟨hu, hv⟩ := binary_eq_zero_of_irreducible hirr (u := x (Sum.inr (Sum.inr 0)))
    (v := x (Sum.inr (Sum.inr 1))) hQ
  funext k
  rcases k with i | i | j
  · exact (hc i).1
  · exact (hc i).2
  · fin_cases j
    · exact hu
    · exact hv

theorem exists_eq_smul_of_mem_tailSpace_minusFamily [Finite K] (h2 : (2 : K) = 0)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 0 < n - 1)
    {x : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hx : x ∈ tailSpace (minusFamily K b c hn) (n - 1)) (hx0 : x ≠ 0)
    {y : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K}
    (hy : y ∈ tailSpace (minusFamily K b c hn) (n - 1))
    (hxy : polar (quadMinus n K b c) x y = 0) : ∃ a : K, y = a • x := by
  have hcx := coord_eq_zero_of_mem_tailSpace_minusFamily hn hx
  have hcy := coord_eq_zero_of_mem_tailSpace_minusFamily hn hy
  have hb : b ≠ 0 := by
    intro hb0
    apply discr_ne_zero_of_finite hirr
    have h4 : (4 : K) = 2 * 2 := by norm_num
    rw [h4, h2, hb0]
    ring
  have hpol : x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 1)) =
      y (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1)) := by
    rw [polar_quadMinus, Finset.sum_eq_zero fun i _ => by rw [(hcx i).1, (hcx i).2, zero_mul,
      mul_zero, add_zero], zero_add, h2] at hxy
    have h1 : b * (x (Sum.inr (Sum.inr 0)) * y (Sum.inr (Sum.inr 1)) +
        y (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1))) = 0 := by linear_combination hxy
    have h3 := (mul_eq_zero.mp h1).resolve_left hb
    linear_combination h3 - y (Sum.inr (Sum.inr 0)) * x (Sum.inr (Sum.inr 1)) * h2
  have hext : ∀ a : K, a * x (Sum.inr (Sum.inr 0)) = y (Sum.inr (Sum.inr 0)) →
      a * x (Sum.inr (Sum.inr 1)) = y (Sum.inr (Sum.inr 1)) → y = a • x := by
    intro a h0 h1
    funext k
    rcases k with i | i | j
    · simp [(hcx i).1, (hcy i).1]
    · simp [(hcx i).2, (hcy i).2]
    · fin_cases j
      · simpa using h0.symm
      · simpa using h1.symm
  by_cases hu : x (Sum.inr (Sum.inr 0)) = 0
  · have hv : x (Sum.inr (Sum.inr 1)) ≠ 0 := by
      intro hv
      apply hx0
      funext k
      rcases k with i | i | j
      · exact (hcx i).1
      · exact (hcx i).2
      · fin_cases j
        · exact hu
        · exact hv
    have hyu : y (Sum.inr (Sum.inr 0)) = 0 := by
      rw [hu, zero_mul] at hpol
      exact (mul_eq_zero.mp hpol.symm).resolve_right hv
    refine ⟨y (Sum.inr (Sum.inr 1)) / x (Sum.inr (Sum.inr 1)), hext _ ?_ ?_⟩
    · rw [hu, mul_zero, hyu]
    · field_simp
  · refine ⟨y (Sum.inr (Sum.inr 0)) / x (Sum.inr (Sum.inr 0)), hext _ ?_ ?_⟩
    · field_simp
    · field_simp
      linear_combination -hpol

end Minus

end CFSG.ClassicalGroups.Orthogonal
