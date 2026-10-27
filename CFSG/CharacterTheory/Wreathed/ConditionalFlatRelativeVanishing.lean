module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesVanishing

public section

open scoped BigOperators

namespace CFSG.Wreathed.FlatRelative

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed.ConditionalFourier

variable {G : Type} [Group G] [Fintype G]

theorem weighted_section_rows_vanish (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) (a b u : G)
    (ha : a * a = 1) (hb : b * b = 1) (e : ℕ) (hu : orderOf u ∣ 2 ^ e)
    (hnoinv : ∀ t : G, IsConj a t → t * u * t⁻¹ ≠ u⁻¹) (lam φ : G → ℂ)
    (v₀ v₁ : basis.index → ℂ)
    (hrow : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ∀ r ∈ Subgroup.centralizer {u}, Odd (orderOf r) →
        (basis.representation χ).character (u * r) = lam r * (v₀ χ + v₁ χ * φ r))
    (hlam : ∀ r ∈ Subgroup.centralizer {u}, Odd (orderOf r) → lam r ≠ 0)
    (hindep : ∀ α β : ℂ, (∀ r ∈ Subgroup.centralizer {u}, Odd (orderOf r) →
      α + β * φ r = 0) → α = 0 ∧ β = 0) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character a * (basis.representation χ).character b * v₀ χ /
          (basis.representation χ).character 1 = 0 ∧
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character a * (basis.representation χ).character b * v₁ χ /
          (basis.representation χ).character 1 = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hvanish, -⟩ := CFSG.LyonsUnitaryFour.brauer_noninverting_block_section_vanishing basis
    ideal 2 B a b u ha hb e hu hnoinv
  refine hindep _ _ fun r hr hodd => ?_
  have h := hvanish r hr (Nat.coprime_two_left.mpr hodd)
  rw [Finset.sum_congr rfl fun χ hχ => by rw [hrow χ hχ r hr hodd]] at h
  have h' : lam r * ((∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character a * (basis.representation χ).character b * v₀ χ /
          (basis.representation χ).character 1) +
      (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character a * (basis.representation χ).character b * v₁ χ /
          (basis.representation χ).character 1) * φ r) = 0 := by
    rw [← h, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  exact (mul_eq_zero.mp h').resolve_left (hlam r hr hodd)

omit [Fintype G] in
theorem indep_of_unique_row {C : Set G} {f lam φ : G → ℂ} (v : Fin 2 → ℂ)
    (hrow : ∀ r ∈ C, Odd (orderOf r) → f r = lam r * (v 0 + v 1 * φ r))
    (huniq : ∀ w : Fin 2 → ℂ, (∀ r ∈ C, Odd (orderOf r) → f r = lam r * (w 0 + w 1 * φ r)) →
      w = v)
    (α β : ℂ) (h : ∀ r ∈ C, Odd (orderOf r) → α + β * φ r = 0) : α = 0 ∧ β = 0 := by
  have hw := huniq ![v 0 + α, v 1 + β] fun r hr hodd => by
    rw [hrow r hr hodd]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -(lam r) * h r hr hodd
  have h0 := congrFun hw 0
  have h1 := congrFun hw 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  exact ⟨by linear_combination h0, by linear_combination h1⟩

theorem weighted_fourier_even (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) {x a : G} (hx : x * x = 1)
    {m M : ℕ} (hm : m = 2 * M) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {e : ℕ}
    (ha : orderOf a ∣ 2 ^ e) (hnc : ∀ k ∈ Finset.Ico 1 m, k ≠ M → ¬ IsConj (a ^ k) (a ^ k)⁻¹)
    (C : ℕ → Subgroup G) (hC : ∀ k, C k = Subgroup.centralizer {a ^ k}) (lam Φ : G → ℂ) (ε : ℤ)
    (hlam : ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, lam r ≠ 0) (v v₀ : basis.index → ℕ → Fin 2 → ℂ)
    (hrow : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, Odd (orderOf r) →
        (basis.representation χ).character (a ^ k * r) =
          lam r * (v χ k 0 + v χ k 1 * (1 + ε * Φ r)))
    (hrow₀ : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ∀ k ∈ Finset.Ico 1 m, ∀ r ∈ C k, Odd (orderOf r) →
        (basis.representation χ).character (a ^ k * r) =
          lam r * (v₀ χ k 0 + v₀ χ k 1 * (1 + ε * Φ r)))
    (huniq : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      ∀ k ∈ Finset.Ico 1 m, ∀ w : Fin 2 → ℂ, (∀ r ∈ C k, Odd (orderOf r) →
        (basis.representation χ).character (a ^ k * r) = lam r * (w 0 + w 1 * (1 + ε * Φ r))) →
        w = v₀ χ k)
    {χ' : basis.index} (hχ' : χ' ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B)
    {j : ℕ} (hj : Even j) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character x * (basis.representation χ).character x /
        (basis.representation χ).character 1 * fourierTransform m ζ (fun k => v χ k 0) j = 0 := by
  refine ConditionalGlobalDegrees.weighted_fourier_vanishing hζ hm (fun χ k => v χ k 0) _
    (fun k hk hkM => ?_) hj
  have hindep : ∀ α β : ℂ, (∀ r ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf r) →
      α + β * (1 + ε * Φ r) = 0) → α = 0 ∧ β = 0 := by
    intro α β h
    refine indep_of_unique_row (C := (C k : Set G))
      (f := fun r => (basis.representation χ').character (a ^ k * r)) (lam := lam)
      (φ := fun r => 1 + ε * Φ r) (v₀ χ' k) (hrow₀ χ' hχ' k hk) (huniq χ' hχ' k hk) α β ?_
    intro r hr hodd
    rw [hC] at hr
    exact h r hr hodd
  have h := (weighted_section_rows_vanish basis ideal B x x (a ^ k) hx hx e
    ((orderOf_pow_dvd k).trans ha) (fun t _ h => hnc k hk hkM (isConj_iff.mpr ⟨t, h⟩)) lam
    (fun r => 1 + ε * Φ r) (fun χ => v χ k 0) (fun χ => v χ k 1)
    (fun χ hχ r hr hodd => hrow χ hχ k hk r (by rw [hC]; exact hr) hodd)
    (fun r hr _ => hlam k hk r (by rw [hC]; exact hr)) hindep).1
  rw [← h]
  exact Finset.sum_congr rfl fun χ _ => by ring

theorem weighted_root_rows (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] (B : basis.index) {x y : G} (hx : x * x = 1)
    {m M : ℕ} (hm4 : (4 : ℤ) ∣ m) {ζ : ℂ} (hyord : orderOf y = 2 * m) {e : ℕ}
    (he : 2 * m = 2 ^ e)
    (hyconj : ∀ h t : ℤ, Odd h → Odd t → (IsConj (y ^ h) (y ^ t) ↔ h ≡ t [ZMOD m]))
    (Y₀ : basis.index → ℂ)
    (hY : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      Y₀ χ = (M : ℂ)⁻¹ * ∑ i ∈ Finset.range M,
        (basis.representation χ).character (y ^ (2 * i + 1)) *
          ζ ^ (-(((0 : ℕ) : ℤ) * (2 * i + 1)))) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
      (basis.representation χ).character x * (basis.representation χ).character x /
        (basis.representation χ).character 1 * Y₀ χ = 0 := by
  have hnr : ∀ i : ℕ, ¬ IsConj (y ^ (2 * i + 1)) (y ^ (2 * i + 1))⁻¹ := by
    intro i hc
    have hodd : Odd ((2 * i + 1 : ℕ) : ℤ) := ⟨i, by push_cast; ring⟩
    rw [← zpow_natCast, ← zpow_neg] at hc
    have hmod := ((hyconj _ _ hodd hodd.neg).mp hc).dvd
    have h4 : (4 : ℤ) ∣ -((2 * i + 1 : ℕ) : ℤ) - ((2 * i + 1 : ℕ) : ℤ) := hm4.trans hmod
    push_cast at h4
    omega
  have hu : ∀ i : ℕ, orderOf (y ^ (2 * i + 1)) ∣ 2 ^ e := fun i => by
    rw [← he, ← hyord]
    exact orderOf_pow_dvd _
  have hzero : ∀ i ∈ Finset.range M,
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character x * (basis.representation χ).character x *
          (basis.representation χ).character (y ^ (2 * i + 1) * 1) /
            (basis.representation χ).character 1 = 0 := fun i _ =>
    ConditionalGlobalDegrees.weighted_section_vanishing basis ideal B hx (hu i) (hnr i)
      (Subgroup.one_mem _) (by rw [orderOf_one]; exact odd_one)
  calc ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
        (basis.representation χ).character x * (basis.representation χ).character x /
          (basis.representation χ).character 1 * Y₀ χ
      = (M : ℂ)⁻¹ * ∑ i ∈ Finset.range M,
          ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) B,
            (basis.representation χ).character x * (basis.representation χ).character x *
              (basis.representation χ).character (y ^ (2 * i + 1) * 1) /
                (basis.representation χ).character 1 := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [hY χ hχ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one]
        ring
    _ = 0 := by rw [Finset.sum_eq_zero hzero, mul_zero]

end CFSG.Wreathed.FlatRelative
