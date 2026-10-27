module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntegralAverage
public import CFSG.CharacterTheory.BlockBasics.Bridge

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem degree_zero_has_negative_coordinate {ι : Type*} (I : Finset ι)
    (degree : ι → ℕ) (hdegree : ∀ i ∈ I, 0 < degree i) (c : ι → ℤ)
    (hzero : ∑ i ∈ I, c i * degree i = 0) (p : ι) (hp : p ∈ I) (hcp : 0 < c p) :
    ∃ i ∈ I, i ≠ p ∧ c i < 0 := by
  have hnegative : ∃ i ∈ I, c i < 0 := by
    by_contra! hnone
    have hnonneg : ∀ i ∈ I, 0 ≤ c i * (degree i : ℤ) := by
      intro i hi
      exact mul_nonneg (hnone i hi) (by omega)
    have hzeros := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    have hprodpos : 0 < c p * (degree p : ℤ) :=
      mul_pos hcp (by exact_mod_cast hdegree p hp)
    rw [hzeros p hp] at hprodpos
    omega
  obtain ⟨i, hi, hci⟩ := hnegative
  exact ⟨i, hi, (fun h => by subst i; omega), hci⟩

theorem finite_integral_column_degree {G : Type} [Group G] {ι : Type*} (I : Finset ι)
    (χ : ι → BlocksIrr G) (c : ι → ℤ) :
    (∑ i ∈ I, c i • (χ i : G → ℂ)) 1 =
      ((∑ i ∈ I, c i * irreducibleDegree (χ i) : ℤ) : ℂ) := by
  simp only [Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply,
    irreducibleDegree_cast, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

theorem actual_root_signed_degree_sum_zero {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) *
        (Module.finrank ℂ (basis.representation χ).vector : ℤ) = 0 := by
  have hzero := actual_root_odd_power_column_degree_zero n hn S e basis ideal principal
    hprincipal root hroot
  change (∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
    (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) *
      (basis.representation χ).character 1) = 0 at hzero
  simp only [FiniteComplexRepresentation.character, Representation.char_one] at hzero
  exact_mod_cast hzero

theorem actual_root_exists_negative_principal_irreducible {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∃ χ : basis.index, χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (basis.representation χ).character ∈ BlocksIrr G ∧
      (basis.representation χ).character ∈ BlocksPrincipalBlock ideal G ∧
      (basis.representation χ).character ≠ 1 ∧
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 ∧
      cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root 0 + 1 ≤
        cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root (2 ^ n) := by
  let degree : basis.index → ℕ := fun χ => Module.finrank ℂ (basis.representation χ).vector
  let c : basis.index → ℤ := fun χ =>
    oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n)
  have hdpos : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      0 < degree χ := by
    intro χ _
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hzero := actual_root_signed_degree_sum_zero n hn S e basis ideal principal
    hprincipal root hroot
  have hcp := actual_root_odd_power_principal_coefficient n hn S e basis principal
    hprincipal root hroot
  obtain ⟨χ, hχ, hχp, hc⟩ := degree_zero_has_negative_coordinate
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) degree hdpos c hzero
      principal (coefficientBlock_self_mem basis _ principal) (by
        change 0 < oddPowerCoefficient (basis.representation principal)
          (actualRoot S e) root (2 ^ n)
        omega)
  have hblock : (basis.representation χ).character ∈ BlocksPrincipalBlock ideal G := by
    change (basis.representation χ).character ∈ BlocksBlockOf ideal G (1 : G → ℂ)
    rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
    exact ⟨χ, hχ, rfl⟩
  have hnontrivial : (basis.representation χ).character ≠ 1 := by
    intro h
    exact hχp (basis.distinct (h.trans hprincipal.symm))
  refine ⟨χ, hχ, CFSG.BlockBasics.basis_character_mem_irr basis χ, hblock, hnontrivial, hc, ?_⟩
  change (cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root 0 : ℤ) -
    cyclicEigenmultiplicity (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 at hc
  omega

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
