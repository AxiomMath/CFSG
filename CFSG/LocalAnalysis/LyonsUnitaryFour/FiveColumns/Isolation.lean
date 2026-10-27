module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.ActualColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.SignedDegreeOfColumns
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.FourierInversion
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.IsolatedCharacterField
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.PrimePartBound

public section

open scoped BigOperators

namespace CFSG.LyonsUnitaryFour

open IntermediateField CFSG.TwoRankLowerBound.Helpers

theorem fiveFourier_congr {X : Type*} [Monoid X] {f g : X → ℂ} (ζ : ℂ) (u v : X)
    (h : ∀ j < 5, f (u * v ^ j) = g (u * v ^ j)) (i : ℕ) :
    fiveFourier f ζ u v i = fiveFourier g ζ u v i := by
  unfold fiveFourier
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h j (Finset.mem_range.mp hj)]

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem character_eq_sum_columns (χ : G → ℂ) (z y : G) (d : Fin 5 → ℤ)
    (hd : ∀ i : Fin 5, ((d i : ℤ) : ℂ) = fiveFourier χ lyonsZeta z y i) {l : ℕ} (hl : l < 5) :
    χ (z * y ^ l) = ∑ i : Fin 5, ((d i : ℤ) : ℂ) * lyonsZeta ^ ((i : ℕ) * l) := by
  rw [fiveFourier_inversion χ lyonsZeta_isPrimitiveRoot z y hl, Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [hd i]

theorem columnRow_eq_of_character_eq (basis : FiniteIrreducibleCharacterBasis G)
    {B : Finset basis.index} (z t y : G) (dt : basis.index → ℤ) (d : Fin 5 → basis.index → ℤ)
    (hdt : ∀ χ ∈ B, ((dt χ : ℤ) : ℂ) = (basis.representation χ).character t)
    (hd : ∀ χ ∈ B, ∀ i : Fin 5,
      ((d i χ : ℤ) : ℂ) = fiveFourier (basis.representation χ).character lyonsZeta z y i)
    {b χ : basis.index} (hb : b ∈ B) (hχ : χ ∈ B)
    (ht : (basis.representation b).character t = (basis.representation χ).character t)
    (hzy : ∀ j < 5, (basis.representation b).character (z * y ^ j) =
      (basis.representation χ).character (z * y ^ j)) :
    columnRow dt d b = columnRow dt d χ := by
  have hdt' : dt b = dt χ := Int.cast_injective (α := ℂ) (by rw [hdt b hb, hdt χ hχ, ht])
  have hd' : ∀ i, d i b = d i χ := fun i => Int.cast_injective (α := ℂ) (by
    rw [hd b hb, hd χ hχ]
    exact fiveFourier_congr lyonsZeta z y hzy i)
  simp only [columnRow, hdt', hd']

@[expose] def lyonsColumnPoints (z t y : G) : Set G :=
  {g | g = 1 ∨ g = t ∨ ∃ l < 5, g = z * y ^ l}

theorem lyons_isolated_column_prime_bound [IsSimpleGroup G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (z t y : G) (dt : basis.index → ℤ) (d : Fin 5 → basis.index → ℤ)
    (hdt : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((dt χ : ℤ) : ℂ) = (basis.representation χ).character t)
    (hd : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ i : Fin 5,
        ((d i χ : ℤ) : ℂ) = fiveFourier (basis.representation χ).character lyonsZeta z y i)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (hdeg : 4 ≤ labelDegree basis χ)
    (huniq : ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      normalizedColumnRow dt d ψ = normalizedColumnRow dt d χ →
        columnSign dt d ψ * labelDegree basis ψ = columnSign dt d χ * labelDegree basis χ →
          ψ = χ)
    {q : ℕ} (hq : q.Prime) (hqG : q ∣ Nat.card G) :
    (q : ℤ) ≤ labelDegree basis χ + 1 := by
  set X := lyonsColumnPoints z t y with hXdef
  have hX : ∀ x ∈ X, (basis.representation χ).character x ∈ ℚ⟮lyonsZeta⟯ := by
    rintro x (rfl | rfl | ⟨l, hl, rfl⟩)
    · rw [← labelDegree_cast]
      exact IntermediateField.intCast_mem _ _
    · rw [← hdt χ hχ]
      exact IntermediateField.intCast_mem _ _
    · rw [character_eq_sum_columns _ z y (fun i => d i χ) (hd χ hχ) hl]
      exact sum_mem fun i _ => mul_mem (IntermediateField.intCast_mem _ _)
        (pow_mem (mem_adjoin_simple_self ℚ lyonsZeta) _)
  have hiso : ∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∀ x ∈ X, (basis.representation b).character x = (basis.representation χ).character x) →
        b = χ := by
    intro b hb hagree
    have hrow := columnRow_eq_of_character_eq basis z t y dt d hdt hd hb hχ
      (hagree t (Or.inr (Or.inl rfl))) fun j hj => hagree _ (Or.inr (Or.inr ⟨j, hj, rfl⟩))
    have hdeg' : labelDegree basis b = labelDegree basis χ := Int.cast_injective (α := ℂ) (by
      rw [labelDegree_cast, labelDegree_cast]
      exact hagree 1 (Or.inl rfl))
    refine huniq b hb ?_ ?_
    · unfold normalizedColumnRow
      rw [hrow]
    · unfold columnSign
      rw [hrow, hdeg']
  have hval : ∀ g, (basis.representation χ).character g ∈
      ℚ⟮Complex.exp (2 * Real.pi * Complex.I / 5)⟯ := fun g =>
    character_mem_adjoin_of_isolated_principal_block basis ideal (N := 5 * Nat.card G)
      (Nat.mul_pos (by norm_num) Nat.card_pos) (dvd_mul_left _ _)
      (by rw [pow_mul, lyonsZeta_isPrimitiveRoot.pow_eq_one, one_pow]) hprincipal hχ X hX hiso g
  have hn : 4 ≤ Module.finrank ℂ (basis.representation χ).vector := by
    have : (4 : ℤ) ≤ Module.finrank ℂ (basis.representation χ).vector := hdeg
    exact_mod_cast this
  have := prime_le_of_simple_cyclotomic_five_character basis χ hn hval hq hqG
  unfold labelDegree
  exact_mod_cast this

theorem lyons_isolated_rotation_fixed_rational
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (z t y : G) (dt : basis.index → ℤ) (d : Fin 5 → basis.index → ℤ)
    (hdt : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ((dt χ : ℤ) : ℂ) = (basis.representation χ).character t)
    (hd : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ i : Fin 5,
        ((d i χ : ℤ) : ℂ) = fiveFourier (basis.representation χ).character lyonsZeta z y i)
    {χ : basis.index}
    (hχ : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
    (huniq : ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      normalizedColumnRow dt d ψ = normalizedColumnRow dt d χ → ψ = χ)
    (hrot : (normalizedColumnRow dt d χ).rotate = normalizedColumnRow dt d χ) (g : G) :
    ∃ q : ℚ, (basis.representation χ).character g = q := by
  set X := lyonsColumnPoints z t y with hXdef
  have hrc : (columnRow dt d χ).rotate = columnRow dt d χ := by
    unfold normalizedColumnRow at hrot
    split_ifs at hrot
    · exact hrot
    · rw [LyonsRow.rotate_neg] at hrot
      exact neg_injective hrot
  simp only [columnRow, LyonsRow.rotate, Prod.mk.injEq] at hrc
  obtain ⟨-, -, h31, h12, h24, -⟩ := hrc
  have hX : ∀ x ∈ X, ∃ q : ℚ, (basis.representation χ).character x = q := by
    rintro x (rfl | rfl | ⟨l, hl, rfl⟩)
    · exact ⟨labelDegree basis χ, by rw [← labelDegree_cast]; push_cast; rfl⟩
    · exact ⟨dt χ, by rw [← hdt χ hχ]; push_cast; rfl⟩
    · rw [character_eq_sum_columns _ z y (fun i => d i χ) (hd χ hχ) hl]
      have hsum : ∑ j ∈ Finset.range 5, lyonsZeta ^ (j * l) = if 5 ∣ l then 5 else 0 := by
        rw [← sum_range_five_pow_mul lyonsZeta_isPrimitiveRoot l]
        exact Finset.sum_congr rfl fun j _ => by rw [Nat.mul_comm]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
      rw [Fin.sum_univ_five]
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, pow_zero,
        mul_one, one_mul] at hsum ⊢
      rw [show ((3 : Fin 5) : ℕ) = 3 from rfl, show ((4 : Fin 5) : ℕ) = 4 from rfl,
        h31, ← h12, ← h24, ← h12]
      by_cases h5 : 5 ∣ l
      · rw [ite_eq_left h5] at hsum
        refine ⟨d 0 χ + 4 * d 1 χ, ?_⟩
        push_cast
        linear_combination (d 1 χ : ℂ) * hsum
      · rw [ite_eq_right h5] at hsum
        refine ⟨d 0 χ - d 1 χ, ?_⟩
        push_cast
        linear_combination (d 1 χ : ℂ) * hsum
  have hiso : ∀ b ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      (∀ x ∈ X, (basis.representation b).character x = (basis.representation χ).character x) →
        b = χ := by
    intro b hb hagree
    have hrow := columnRow_eq_of_character_eq basis z t y dt d hdt hd hb hχ
      (hagree t (Or.inr (Or.inl rfl))) fun j hj => hagree _ (Or.inr (Or.inr ⟨j, hj, rfl⟩))
    refine huniq b hb ?_
    unfold normalizedColumnRow
    rw [hrow]
  exact character_rat_of_isolated_principal_block basis ideal hprincipal hχ X hX hiso g

end CFSG.LyonsUnitaryFour
