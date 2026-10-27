module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntrinsic

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical ComplexConjugate

variable {G : Type} [Group G] [Fintype G]

theorem actual_root_odd_power_column_section_value
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n))
    (h : ℤ) (hh : Odd h) (v : G) (hv : Odd (orderOf v))
    (hc : v ∈ Subgroup.centralizer ({actualRoot S e} : Set G)) :
    oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n)
      (actualRoot S e ^ h * v) = 4 := by
  let I := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
  let c : basis.index → ℕ → ℤ := fun χ r =>
    signedEvenEigenmultiplicity (basis.representation χ) (actualRoot S e) root (2 ^ n) r
  have hhalf : 0 < 2 ^ n / 2 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨hvalues, hgram, _, _, _, _⟩ :=
    CFSG.Wreathed.ConditionalSquareRoot.actualRoot_signed_even_columns n hn S e basis ideal
      principal hprincipal hroot
  have hc0 : ∀ χ, c χ 0 =
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) := by
    intro χ
    simp only [c, signedEvenEigenmultiplicity, oddPowerCoefficient, mul_zero, zero_add]
  change (∑ χ ∈ I,
    (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) *
      (basis.representation χ).character (actualRoot S e ^ h * v)) = 4
  simp only [← hc0]
  calc
    (∑ χ ∈ I, (c χ 0 : ℂ) * (basis.representation χ).character
        (actualRoot S e ^ h * v)) =
        ∑ χ ∈ I, ∑ r ∈ Finset.range (2 ^ n / 2),
          (c χ 0 : ℂ) * (c χ r : ℂ) * (root ^ 2) ^ ((r : ℤ) * h) := by
      apply Finset.sum_congr rfl
      intro χ hχ
      rw [(hvalues χ hχ h hh v hc hv).1, (hvalues χ hχ h hh v hc hv).2,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
    _ = ∑ r ∈ Finset.range (2 ^ n / 2),
        ((∑ χ ∈ I, c χ 0 * c χ r : ℤ) : ℂ) * (root ^ 2) ^ ((r : ℤ) * h) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      push_cast
      rw [Finset.sum_mul]
    _ = 4 := by
      rw [Finset.sum_eq_single 0]
      · rw [hgram 0 hhalf 0 hhalf, ite_eq_left rfl]
        simp
      · intro r hr hr0
        rw [hgram 0 hhalf r (Finset.mem_range.mp hr), ite_eq_right (Ne.symm hr0)]
        simp
      · intro h0
        exact (h0 (Finset.mem_range.mpr hhalf)).elim

theorem actual_root_principal_average_indicator
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∀ g : G, rootPrincipalAverageColumn n ideal (actualRoot S e) g =
      if g ∈ squareRootSection (actualRoot S e) then 4 else 0 := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  rw [actual_root_principal_average_column_eq n hn S e basis ideal principal hprincipal
    root hroot]
  have hclass : BlocksIsClassFunction
      (oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n)) := by
    intro g a
    unfold oddPowerPrincipalColumn
    exact Finset.sum_congr rfl fun χ _ => congrArg
      (fun z : ℂ =>
        (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) * z)
      (Representation.char_conj (basis.representation χ).representation g a)
  have hon := (classFunction_section_value_iff hclass).mp
    (fun h v hh hv hc => actual_root_odd_power_column_section_value n hn S e basis ideal
      principal hprincipal root hroot h hh v hv hc)
  intro g
  split_ifs with hg
  · exact hon g hg
  · exact actual_root_odd_power_column_support n hn S e basis ideal principal hprincipal
      root hroot g hg

theorem actual_root_principal_average_eq_of_ideals
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal₁ ideal₂ : Ideal ComplexAlgebraicIntegers)
    [ideal₁.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal₁) 2]
    [ideal₂.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal₂) 2] :
    rootPrincipalAverageColumn n ideal₁ (actualRoot S e) =
      rootPrincipalAverageColumn n ideal₂ (actualRoot S e) := by
  ext g
  rw [actual_root_principal_average_indicator n hn S e ideal₁,
    actual_root_principal_average_indicator n hn S e ideal₂]

theorem actual_root_integral_section_indicator
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    (fun g : G => if g ∈ squareRootSection (actualRoot S e) then (4 : ℂ) else 0) ∈
      BlocksVChar G := by
  have heq : (fun g : G => if g ∈ squareRootSection (actualRoot S e) then (4 : ℂ) else 0) =
      rootPrincipalAverageColumn n ideal (actualRoot S e) := by
    ext g
    exact (actual_root_principal_average_indicator n hn S e ideal g).symm
  rw [heq]
  exact (actual_root_intrinsic_integral_column n hn S e ideal).1

theorem actual_root_section_cardinality
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    4 * Nat.card {g : G // g ∈ squareRootSection (actualRoot S e)} = Nat.card G := by
  have hpair := (actual_root_intrinsic_integral_column n hn S e ideal).2.2.2.1
  unfold BlocksInnerProduct at hpair
  simp only [Pi.one_apply, one_mul, actual_root_principal_average_indicator n hn S e ideal]
    at hpair
  have hconj (g : G) :
      (starRingEnd ℂ) (if g ∈ squareRootSection (actualRoot S e) then (4 : ℂ) else 0) =
        if g ∈ squareRootSection (actualRoot S e) then (4 : ℂ) else 0 := by
    by_cases hg : g ∈ squareRootSection (actualRoot S e)
    · rw [ite_eq_left hg]
      exact map_natCast (starRingEnd ℂ) 4
    · rw [ite_eq_right hg, map_zero]
  simp only [hconj] at hpair
  have hsum : (∑ g : G, if g ∈ squareRootSection (actualRoot S e) then (4 : ℂ) else 0) =
      4 * (Nat.card {g : G // g ∈ squareRootSection (actualRoot S e)} : ℂ) := by
    simp [← Finset.sum_filter, Nat.card_eq_fintype_card, Fintype.card_subtype, nsmul_eq_mul,
      mul_comm]
  rw [hsum] at hpair
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h := congrArg (fun z : ℂ => (Nat.card G : ℂ) * z) hpair
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h
  exact_mod_cast h

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
