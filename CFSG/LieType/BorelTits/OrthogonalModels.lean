module

public import CFSG.LieType.BorelTits.OrthogonalForm

public section

namespace CFSG.LieType.BorelTits

open CFSG.Assembly.LowTwoRank

@[expose] def quadPlusPolar (n : ℕ) (K : Type) [Field K] (u v : Fin n ⊕ Fin n → K) : K :=
  ∑ i, (u (.inl i) * v (.inr i) + v (.inl i) * u (.inr i))

@[expose] noncomputable def quadPlusForm (n : ℕ) (K : Type) [Field K] :
    QuadForm K (Fin n ⊕ Fin n → K) where
  Q := StatedQuadPlus n K
  polar :=
    { σ := RingEquiv.refl K
      β := quadPlusPolar n K
      add_left := fun u u' v => by
        simp only [quadPlusPolar, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      smul_left := fun c u v => by
        simp only [quadPlusPolar, Pi.smul_apply, smul_eq_mul, RingEquiv.refl_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      add_right := fun u v v' => by
        simp only [quadPlusPolar, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      smul_right := fun c u v => by
        simp only [quadPlusPolar, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      refl := fun u v h => by
        rw [← h]
        unfold quadPlusPolar
        exact Finset.sum_congr rfl fun i _ => by ring
      nondeg := fun u h => by
        funext j
        rcases j with j | j
        · have := h (Pi.single (.inr j) 1)
          simpa [quadPlusPolar, Pi.single_apply] using this
        · have := h (Pi.single (.inl j) 1)
          simpa [quadPlusPolar, Pi.single_apply] using this }
  polar_σ := rfl
  Q_smul := fun c v => by
    simp only [StatedQuadPlus, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  Q_add := fun u v => by
    simp only [StatedQuadPlus, quadPlusPolar, Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring

@[expose] def quadOddPolar (n : ℕ) (K : Type) [Field K] (u v : Fin n ⊕ Fin n ⊕ Unit → K) : K :=
  ∑ i, (u (.inl i) * v (.inr (.inl i)) + v (.inl i) * u (.inr (.inl i))) +
    2 * u (.inr (.inr ())) * v (.inr (.inr ()))

@[expose] noncomputable def quadOddForm (n : ℕ) (K : Type) [Field K] (h2 : (2 : K) ≠ 0) :
    QuadForm K (Fin n ⊕ Fin n ⊕ Unit → K) where
  Q := StatedQuadOdd n K
  polar :=
    { σ := RingEquiv.refl K
      β := quadOddPolar n K
      add_left := fun u u' v => by
        simp only [quadOddPolar, Pi.add_apply]
        rw [add_add_add_comm, ← Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      smul_left := fun c u v => by
        simp only [quadOddPolar, Pi.smul_apply, smul_eq_mul, RingEquiv.refl_apply, mul_add,
          Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      add_right := fun u v v' => by
        simp only [quadOddPolar, Pi.add_apply]
        rw [add_add_add_comm, ← Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      smul_right := fun c u v => by
        simp only [quadOddPolar, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      refl := fun u v h => by
        rw [← h]
        unfold quadOddPolar
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      nondeg := fun u h => by
        funext j
        rcases j with j | j | ⟨⟩
        · have := h (Pi.single (.inr (.inl j)) 1)
          simpa [quadOddPolar, Pi.single_apply] using this
        · have := h (Pi.single (.inl j) 1)
          simpa [quadOddPolar, Pi.single_apply] using this
        · have := h (Pi.single (.inr (.inr ())) 1)
          simp [quadOddPolar] at this
          simpa [h2] using this }
  polar_σ := rfl
  Q_smul := fun c v => by
    simp only [StatedQuadOdd, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  Q_add := fun u v => by
    simp only [StatedQuadOdd, quadOddPolar, Pi.add_apply]
    have : ∀ i, (u (.inl i) + v (.inl i)) * (u (.inr (.inl i)) + v (.inr (.inl i))) =
        u (.inl i) * u (.inr (.inl i)) + v (.inl i) * v (.inr (.inl i)) +
          (u (.inl i) * v (.inr (.inl i)) + v (.inl i) * u (.inr (.inl i))) := fun i => by ring
    simp only [this, Finset.sum_add_distrib]
    ring


@[expose] def quadMinusPolar (n : ℕ) (K : Type) [Field K] (b c : K)
    (u v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) : K :=
  ∑ i, (u (.inl i) * v (.inr (.inl i)) + v (.inl i) * u (.inr (.inl i))) +
    (2 * u (.inr (.inr 0)) * v (.inr (.inr 0)) +
      b * (u (.inr (.inr 0)) * v (.inr (.inr 1)) + v (.inr (.inr 0)) * u (.inr (.inr 1))) +
      2 * c * u (.inr (.inr 1)) * v (.inr (.inr 1)))

theorem four_mul_sub_sq_ne_zero {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : 4 * c - b ^ 2 ≠ 0 := by
  intro h
  by_cases h2 : (2 : K) = 0
  · have hb : b = 0 := by
      have : b ^ 2 = 0 := by
        have h4 : (4 : K) = 2 * 2 := by norm_num
        rw [h4, h2, zero_mul, zero_mul, zero_sub, neg_eq_zero] at h
        exact h
      exact pow_eq_zero_iff (two_ne_zero) |>.mp this
    have hchar : ringChar K = 2 := by
      have := ringChar.dvd (R := K) (x := 2) (by exact_mod_cast h2)
      exact (Nat.prime_two.eq_one_or_self_of_dvd _ this).resolve_left (CharP.ringChar_ne_one)
    obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hchar (-c)
    apply hirr s
    rw [hb, zero_mul, add_zero, ← sq] at *
    rw [← hs]
    ring
  · apply hirr (-b / 2)
    field_simp
    linear_combination h

@[expose] noncomputable def quadMinusForm (n : ℕ) (K : Type) [Field K] [Finite K] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    QuadForm K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) where
  Q := StatedQuadMinus n K b c
  polar :=
    { σ := RingEquiv.refl K
      β := quadMinusPolar n K b c
      add_left := fun u u' v => by
        simp only [quadMinusPolar, Pi.add_apply]
        rw [add_add_add_comm, ← Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      smul_left := fun c' u v => by
        simp only [quadMinusPolar, Pi.smul_apply, smul_eq_mul, RingEquiv.refl_apply, mul_add,
          Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      add_right := fun u v v' => by
        simp only [quadMinusPolar, Pi.add_apply]
        rw [add_add_add_comm, ← Finset.sum_add_distrib]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      smul_right := fun c' u v => by
        simp only [quadMinusPolar, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      refl := fun u v h => by
        rw [← h]
        unfold quadMinusPolar
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · ring
      nondeg := fun u h => by
        have hD := four_mul_sub_sq_ne_zero hirr
        have h0 := h (Pi.single (.inr (.inr 0)) 1)
        have h1 := h (Pi.single (.inr (.inr 1)) 1)
        simp [quadMinusPolar] at h0 h1
        have hu0 : u (.inr (.inr 0)) = 0 := by
          have : (4 * c - b ^ 2) * u (.inr (.inr 0)) = 0 := by linear_combination 2 * c * h0 - b * h1
          exact (mul_eq_zero.mp this).resolve_left hD
        have hu1 : u (.inr (.inr 1)) = 0 := by
          have : (4 * c - b ^ 2) * u (.inr (.inr 1)) = 0 := by linear_combination 2 * h1 - b * h0
          exact (mul_eq_zero.mp this).resolve_left hD
        funext j
        rcases j with j | j | j
        · have := h (Pi.single (.inr (.inl j)) 1)
          simpa [quadMinusPolar, Pi.single_apply] using this
        · have := h (Pi.single (.inl j) 1)
          simpa [quadMinusPolar, Pi.single_apply] using this
        · fin_cases j
          · exact hu0
          · exact hu1 }
  polar_σ := rfl
  Q_smul := fun c' v => by
    simp only [StatedQuadMinus, Pi.smul_apply, smul_eq_mul]
    rw [show ∑ i, c' * v (.inl i) * (c' * v (.inr (.inl i))) =
        ∑ i, c' ^ 2 * (v (.inl i) * v (.inr (.inl i))) from
      Finset.sum_congr rfl fun i _ => by ring, ← Finset.mul_sum]
    ring
  Q_add := fun u v => by
    simp only [StatedQuadMinus, quadMinusPolar, Pi.add_apply]
    have : ∀ i, (u (.inl i) + v (.inl i)) * (u (.inr (.inl i)) + v (.inr (.inl i))) =
        u (.inl i) * u (.inr (.inl i)) + v (.inl i) * v (.inr (.inl i)) +
          (u (.inl i) * v (.inr (.inl i)) + v (.inl i) * u (.inr (.inl i))) := fun i => by ring
    simp only [this, Finset.sum_add_distrib]
    ring


end CFSG.LieType.BorelTits
