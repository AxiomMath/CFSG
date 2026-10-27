module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityCancellation

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem full_odd_power_weighted_average_eigenmultiplicity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (hy : y ^ (2 * m) = 1) (root : ℂ) (hroot : IsPrimitiveRoot root (2 * m)) (t : ℕ) :
    (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m,
      (root ^ t)⁻¹ ^ (2 * k + 1) * data.character (y ^ (2 * k + 1)) =
      ((cyclicEigenmultiplicity data y root t : ℤ) -
        cyclicEigenmultiplicity data y root (t + m) : ℤ) := by
  have havgt := character_cyclic_eigenmultiplicity_average data y (2 * m)
    (by omega) hy root hroot t
  have havgm := character_cyclic_eigenmultiplicity_average data y (2 * m)
    (by omega) hy root hroot (t + m)
  have hshift (k : ℕ) :
      (root ^ (t + m))⁻¹ ^ k = (-1 : ℂ) ^ k * (root ^ t)⁻¹ ^ k := by
    rw [pow_add, primitive_twice_root_half hm hroot, mul_neg_one,
      inv_neg, neg_eq_neg_one_mul, mul_pow]
  simp only [hshift] at havgm
  have hsplit := sum_range_twice_even_odd
    (fun k => (root ^ t)⁻¹ ^ k * data.character (y ^ k)) m
  have hsplitm := sum_range_twice_even_odd
    (fun k => (-1 : ℂ) ^ k * (root ^ t)⁻¹ ^ k * data.character (y ^ k)) m
  have hsign : ∀ k : ℕ, (-1 : ℂ) ^ (2 * k) = 1 ∧
      (-1 : ℂ) ^ (2 * k + 1) = -1 := by
    intro k
    exact ⟨Even.neg_one_pow (even_two_mul k),
      Odd.neg_one_pow (show Odd (2 * k + 1) from ⟨k, rfl⟩)⟩
  simp only [hsign, one_mul, neg_mul, Finset.sum_neg_distrib] at hsplitm
  rw [hsplit] at havgt
  rw [hsplitm] at havgm
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  rw [← havgt, ← havgm]
  push_cast
  field_simp
  ring

@[expose] def signedEvenEigenmultiplicity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (root : ℂ) (m r : ℕ) : ℤ :=
  (cyclicEigenmultiplicity data y root (2 * r) : ℤ) -
    cyclicEigenmultiplicity data y root (2 * r + m)

theorem signed_even_character_expansion {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1)))
    (h : ℕ) (hh : Odd h) :
    data.character (y ^ h) = ∑ r ∈ Finset.range (m / 2),
      (signedEvenEigenmultiplicity data y root m r : ℂ) * (root ^ 2) ^ (r * h) := by
  have htwice : 2 * (m / 2) = m := by
    obtain ⟨a, ha⟩ := heven
    omega
  have hexp := character_cyclic_eigenmultiplicity_expansion data y (2 * m)
    (by omega) hy root hroot h
  rw [show 2 * m = m + m by omega, Finset.sum_range_add] at hexp
  have hpair (t : ℕ) : root ^ ((m + t) * h) = -root ^ (t * h) := by
    rw [Nat.add_mul, pow_add]
    have hmh : root ^ (m * h) = -1 := by
      rw [pow_mul, primitive_twice_root_half hm hroot, Odd.neg_one_pow hh]
    rw [hmh]
    ring
  have hpaired : data.character (y ^ h) = ∑ t ∈ Finset.range m,
      (((cyclicEigenmultiplicity data y root t : ℤ) -
        cyclicEigenmultiplicity data y root (t + m) : ℤ) : ℂ) * root ^ (t * h) := by
    rw [hexp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [hpair, Nat.add_comm m t]
    push_cast
    ring
  rw [hpaired]
  conv_lhs => rw [← htwice]
  rw [sum_range_twice_even_odd]
  have hodd : ∀ k : ℕ,
      (((cyclicEigenmultiplicity data y root (2 * k + 1) : ℤ) -
        cyclicEigenmultiplicity data y root (2 * k + 1 + 2 * (m / 2)) : ℤ) : ℂ) = 0 := by
    intro k
    rw [htwice, odd_eigenmultiplicity_eq_half_period data y m hm heven hy root hroot
      hconj (2 * k + 1) (show Odd (2 * k + 1) from ⟨k, rfl⟩), sub_self, Int.cast_zero]
  simp only [hodd, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  rw [htwice, signedEvenEigenmultiplicity, ← pow_mul]
  congr 2
  ring

theorem odd_power_character_half_period {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ)
    (hy : y ^ (2 * m) = 1) (hconj : IsConj y (y ^ (m + 1)))
    (h : ℕ) (hh : Odd h) : data.character (y ^ (h + m)) = data.character (y ^ h) := by
  have hpower : (y ^ (m + 1)) ^ h = y ^ (h + m) := by
    obtain ⟨k, hk⟩ := hh
    have he : (m + 1) * h = h + m + (2 * m) * k := by rw [hk]; ring
    rw [← pow_mul, he, pow_add, pow_mul, hy, one_pow, mul_one]
  have hch := hconj.pow h
  rw [hpower] at hch
  obtain ⟨c, hc⟩ := isConj_iff.mp hch
  rw [← hc]
  exact Representation.char_conj data.representation _ c

theorem half_odd_power_weighted_average_eigenmultiplicity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1))) (r : ℕ) :
    ((m / 2 : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (m / 2),
      (root ^ 2)⁻¹ ^ (r * (2 * k + 1)) * data.character (y ^ (2 * k + 1)) =
        (signedEvenEigenmultiplicity data y root m r : ℂ) := by
  have htwice : 2 * (m / 2) = m := by obtain ⟨a, ha⟩ := heven; omega
  have hhalf : 0 < m / 2 := by omega
  have havg := full_odd_power_weighted_average_eigenmultiplicity data y m hm hy root hroot (2 * r)
  have hrootm : ((root ^ (2 * r))⁻¹) ^ m = 1 := by
    rw [← inv_pow, ← pow_mul]
    have he : (2 * r) * m = (2 * m) * r := by ring
    rw [he, pow_mul, inv_pow, hroot.pow_eq_one, inv_one, one_pow]
  have hrepeat (k : ℕ) :
      (root ^ (2 * r))⁻¹ ^ (2 * (m / 2 + k) + 1) *
        data.character (y ^ (2 * (m / 2 + k) + 1)) =
      (root ^ (2 * r))⁻¹ ^ (2 * k + 1) * data.character (y ^ (2 * k + 1)) := by
    have he : 2 * (m / 2 + k) + 1 = (2 * k + 1) + m := by omega
    rw [he, pow_add, hrootm, mul_one,
      odd_power_character_half_period data y m hy hconj (2 * k + 1)
        (show Odd (2 * k + 1) from ⟨k, rfl⟩)]
  have hsplit : ∑ k ∈ Finset.range m,
      (root ^ (2 * r))⁻¹ ^ (2 * k + 1) * data.character (y ^ (2 * k + 1)) =
      2 * ∑ k ∈ Finset.range (m / 2),
        (root ^ (2 * r))⁻¹ ^ (2 * k + 1) * data.character (y ^ (2 * k + 1)) := by
    conv_lhs => rw [show m = m / 2 + m / 2 by omega]
    rw [Finset.sum_range_add]
    simp only [hrepeat]
    ring
  rw [hsplit] at havg
  have hphase (k : ℕ) :
      (root ^ (2 * r))⁻¹ ^ (2 * k + 1) = (root ^ 2)⁻¹ ^ (r * (2 * k + 1)) := by
    simp only [pow_mul, inv_pow]
  simp only [hphase] at havg
  have hscale : (m : ℂ)⁻¹ * 2 = ((m / 2 : ℕ) : ℂ)⁻¹ := by
    have hmc : ((m / 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hhalf.ne'
    have hcast : (m : ℂ) = 2 * ((m / 2 : ℕ) : ℂ) := by
      exact_mod_cast htwice.symm
    rw [hcast]
    field_simp
  unfold signedEvenEigenmultiplicity
  rw [← havg, ← mul_assoc, hscale]

theorem finite_order_zpow_eq_nat_remainder {G : Type*} [Group G]
    (y : G) (period : ℕ) (hp : 0 < period) (hy : y ^ period = 1) (h : ℤ) :
    y ^ h = y ^ (h % (period : ℤ)).toNat := by
  have hnonneg := Int.emod_nonneg h (show (period : ℤ) ≠ 0 by exact_mod_cast hp.ne')
  calc
    y ^ h = y ^ (h % (period : ℤ)) := zpow_eq_zpow_emod' h hy
    _ = y ^ ((h % (period : ℤ)).toNat : ℤ) := by rw [Int.toNat_of_nonneg hnonneg]
    _ = y ^ (h % (period : ℤ)).toNat := zpow_natCast _ _

theorem odd_twice_remainder {m : ℕ} (hm : 0 < m) (h : ℤ) (hh : Odd h) :
    Odd (h % ((2 * m : ℕ) : ℤ)).toNat := by
  have hnonneg := Int.emod_nonneg h (show ((2 * m : ℕ) : ℤ) ≠ 0 by positivity)
  have hmod : h % ((2 * m : ℕ) : ℤ) % 2 = 1 := by
    rw [Int.emod_emod_of_dvd h (show (2 : ℤ) ∣ ((2 * m : ℕ) : ℤ) by
      exact ⟨(m : ℤ), by push_cast; ring⟩)]
    exact Int.odd_iff.mp hh
  have hint : Odd (h % ((2 * m : ℕ) : ℤ)) := Int.odd_iff.mpr hmod
  have hcast : ((h % ((2 * m : ℕ) : ℤ)).toNat : ℤ) = h % ((2 * m : ℕ) : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  rw [← hcast] at hint
  exact_mod_cast hint

theorem signed_even_character_zpow_expansion {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (heven : Even m) (hy : y ^ (2 * m) = 1) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * m)) (hconj : IsConj y (y ^ (m + 1)))
    (h : ℤ) (hh : Odd h) :
    data.character (y ^ h) = ∑ r ∈ Finset.range (m / 2),
      (signedEvenEigenmultiplicity data y root m r : ℂ) * (root ^ 2) ^ ((r : ℤ) * h) := by
  let k := (h % ((2 * m : ℕ) : ℤ)).toNat
  have hyk := finite_order_zpow_eq_nat_remainder y (2 * m) (by omega) hy h
  rw [hyk, signed_even_character_expansion data y m hm heven hy root hroot hconj k
    (odd_twice_remainder hm h hh)]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  let u : ℂˣ := Units.mk0 root (hroot.ne_zero (by omega))
  have hu : u ^ (2 * m) = 1 := by
    apply Units.ext
    exact hroot.pow_eq_one
  have heq := finite_order_zpow_eq_nat_remainder u (2 * m) (by omega) hu h
  have hpow := congrArg Units.val (congrArg (fun z : ℂˣ => z ^ (2 * r)) heq)
  have hval : (u : ℂ) = root := rfl
  simp only [Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, hval] at hpow
  calc
    (root ^ 2) ^ (r * k) = (root ^ k) ^ (2 * r) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ = (root ^ h) ^ (2 * r) := hpow.symm
    _ = (root ^ 2) ^ ((r : ℤ) * h) := by
      rw [← zpow_natCast (root ^ h), ← zpow_mul, ← zpow_natCast root, ← zpow_mul]
      congr 1
      push_cast
      ring

theorem actual_root_signed_even_section_expansion {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
        v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        (basis.representation χ).character (actualRoot S e ^ h * v) =
          ∑ r ∈ Finset.range (2 ^ n / 2),
            (signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e)
              root (2 ^ n) r : ℂ) * (root ^ 2) ^ ((r : ℤ) * h) := by
  intro χ hχ h v hh hv hvcentral
  rw [(actual_root_principal_columns n hn S e basis ideal principal hprincipal h hh).1
    χ hχ v hvcentral hv]
  apply signed_even_character_zpow_expansion _ _ _ (pow_pos (by omega) _)
    (Even.pow_of_ne_zero even_two (by omega)) _ root hroot _ h hh
  · rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  · exact isConj_iff.mpr ⟨wreathModelHom S e (Original.x2 (2 ^ n)),
      actualRoot_conjugate_half n (by omega) S e⟩

theorem actual_root_signed_even_average {G : Type} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (data : FiniteComplexRepresentation G) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) (r : ℕ) :
    ((2 ^ n / 2 : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n / 2),
      (root ^ 2)⁻¹ ^ (r * (2 * k + 1)) * data.character (actualRoot S e ^ (2 * k + 1)) =
        (signedEvenEigenmultiplicity data (actualRoot S e) root (2 ^ n) r : ℂ) := by
  apply half_odd_power_weighted_average_eigenmultiplicity data (actualRoot S e) (2 ^ n)
    (pow_pos (by omega) _) (Even.pow_of_ne_zero even_two (by omega)) _ root hroot _ r
  · rw [← actualRoot_orderOf n hn S e]
    exact pow_orderOf_eq_one _
  · exact isConj_iff.mpr ⟨wreathModelHom S e (Original.x2 (2 ^ n)),
      actualRoot_conjugate_half n (by omega) S e⟩

theorem signedEvenEigenmultiplicity_zero {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (root : ℂ) (m : ℕ) :
    signedEvenEigenmultiplicity data y root m 0 = oddPowerCoefficient data y root m := by
  simp only [signedEvenEigenmultiplicity, oddPowerCoefficient, Nat.mul_zero, Nat.zero_add]

theorem actual_root_integral_column_half_average {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    (∀ χ : basis.index,
      (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) =
        ((2 ^ n / 2 : ℕ) : ℂ)⁻¹ * ∑ k : Fin (2 ^ n / 2),
          (basis.representation χ).character (actualRoot S e ^ (2 * (k : ℤ) + 1))) ∧
      ∀ g ∉ squareRootSection (actualRoot S e),
        oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) g = 0 := by
  refine ⟨?_, actual_root_odd_power_column_support n hn S e basis ideal
    principal hprincipal root hroot⟩
  intro χ
  have h := actual_root_signed_even_average n hn S e (basis.representation χ) root hroot 0
  simp only [Nat.zero_mul, pow_zero, one_mul, signedEvenEigenmultiplicity_zero] at h
  rw [← h, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [← zpow_natCast]
  congr 1

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
