module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityEigenmultiplicities
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityLocalColumns

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

theorem originalRoot_conjugate_half (n : ℕ) (hn : 1 ≤ n) :
    Original.x2 (2 ^ n) * originalRoot (2 ^ n) * (Original.x2 (2 ^ n))⁻¹ =
      originalRoot (2 ^ n) ^ (2 ^ n + 1) := by
  have hhalf : -((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) = ((2 ^ n / 2 : ℕ) : ZMod (2 ^ n)) := by
    apply neg_eq_iff_add_eq_zero.mpr
    rw [← Nat.cast_add]
    have hd : 2 ^ n / 2 + 2 ^ n / 2 = 2 ^ n := by
      have hm := wreath_modulus_twice_half n hn
      omega
    rw [hd]
    exact ZMod.natCast_self _
  rw [Original.x2_eq, originalRoot_eq, conjugate_swap_by_base, sub_zero, zero_add,
    zero_sub, hhalf]
  rw [pow_succ, ← originalRoot_eq, originalRoot_pow_modulus n hn,
    Original.x_eq, originalRoot_eq, element_base_mul]
  simp only [add_comm, add_zero]

theorem actualRoot_conjugate_half {G : Type} [Group G]
    (n : ℕ) (hn : 1 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x2 (2 ^ n)) * actualRoot S e *
      (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ =
        actualRoot S e ^ (2 ^ n + 1) := by
  have h := congrArg (wreathModelHom S e) (originalRoot_conjugate_half n hn)
  simpa only [map_mul, map_inv, map_pow, actualRoot] using h

theorem primitive_twice_root_half {m : ℕ} (hm : 0 < m) {root : ℂ}
    (hroot : IsPrimitiveRoot root (2 * m)) : root ^ m = -1 := by
  have h := hroot.pow (by omega) (show 2 * m = m * 2 by omega)
  exact h.eq_neg_one_of_two_right

theorem sum_range_twice_even_odd (f : ℕ → ℂ) (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m), f k) =
      (∑ k ∈ Finset.range m, f (2 * k)) +
        ∑ k ∈ Finset.range m, f (2 * k + 1) := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Nat.mul_succ, Finset.sum_range_add, hm, Finset.sum_range_succ,
      Finset.sum_range_succ]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_zero]
    ring

theorem full_odd_power_average_eigenmultiplicity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (hy : y ^ (2 * m) = 1) (root : ℂ) (hroot : IsPrimitiveRoot root (2 * m)) :
    (m : ℂ)⁻¹ * ∑ k ∈ Finset.range m, data.character (y ^ (2 * k + 1)) =
      ((cyclicEigenmultiplicity data y root 0 : ℤ) -
        cyclicEigenmultiplicity data y root m : ℤ) := by
  have havg0 := character_cyclic_eigenmultiplicity_average data y (2 * m)
    (by omega) hy root hroot 0
  have havgm := character_cyclic_eigenmultiplicity_average data y (2 * m)
    (by omega) hy root hroot m
  simp only [pow_zero, inv_one, one_pow, one_mul] at havg0
  rw [primitive_twice_root_half hm hroot] at havgm
  have hsplit := sum_range_twice_even_odd (fun k => data.character (y ^ k)) m
  have hsplitm := sum_range_twice_even_odd
    (fun k => ((-1 : ℂ)⁻¹) ^ k * data.character (y ^ k)) m
  have hsign : ∀ k : ℕ, ((-1 : ℂ)⁻¹) ^ (2 * k) = 1 ∧
      ((-1 : ℂ)⁻¹) ^ (2 * k + 1) = -1 := by
    intro k
    simp only [inv_neg, inv_one, Even.neg_one_pow (even_two_mul k),
      Odd.neg_one_pow (show Odd (2 * k + 1) from ⟨k, rfl⟩)]
    trivial
  simp only [hsign, one_mul, neg_one_mul, Finset.sum_neg_distrib] at hsplitm
  rw [hsplit] at havg0
  rw [hsplitm] at havgm
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  push_cast
  rw [← havg0, ← havgm]
  push_cast
  field_simp
  ring

@[expose] def oddPowerCoefficient {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (root : ℂ) (m : ℕ) : ℤ :=
  (cyclicEigenmultiplicity data y root 0 : ℤ) -
    cyclicEigenmultiplicity data y root m

theorem actual_root_odd_power_average {G : Type} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (data : FiniteComplexRepresentation G) (root : ℂ)
    (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n),
      data.character (actualRoot S e ^ (2 * k + 1)) =
        (oddPowerCoefficient data (actualRoot S e) root (2 ^ n) : ℂ) := by
  apply full_odd_power_average_eigenmultiplicity data _ _ (pow_pos (by omega) _) _ root hroot
  rw [← actualRoot_orderOf n hn S e]
  exact pow_orderOf_eq_one _

@[expose] def oddPowerPrincipalColumn {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsPrime] (principal : basis.index) (y : G) (root : ℂ) (m : ℕ) : G → ℂ :=
  fun g => ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
    (oddPowerCoefficient (basis.representation χ) y root m : ℂ) *
      (basis.representation χ).character g

theorem oddPowerPrincipalColumn_mem_virtual {G : Type} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsPrime] (principal : basis.index) (y : G) (root : ℂ) (m : ℕ) :
    oddPowerPrincipalColumn basis ideal principal y root m ∈ BlocksVChar G := by
  have hsum : oddPowerPrincipalColumn basis ideal principal y root m =
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation χ) y root m •
          (basis.representation χ).character := by
    ext g
    simp only [oddPowerPrincipalColumn, Finset.sum_apply, zsmul_eq_mul,
      Pi.mul_apply, Pi.intCast_apply]
  rw [hsum]
  exact (BlocksVChar G).sum_mem fun χ _ => (BlocksVChar G).zsmul_mem
    (AddSubgroup.subset_closure
      (by
        rw [blocksIrr_eq_irreducible_characters]
        exact ⟨basis.representation χ, basis.irreducible χ, rfl⟩)) _

theorem actual_root_odd_power_column_support {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∀ g ∉ squareRootSection (actualRoot S e),
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) g = 0 := by
  apply original_integral_average_supported n hn S e (actualRoot S e)
    (actualRoot_orderOf n hn S e) basis ideal principal hprincipal
    (Finset.range (2 ^ n)) (fun k => (2 * k + 1 : ℕ))
    (fun k _ => by exact_mod_cast (show Odd (2 * k + 1) from ⟨k, rfl⟩))
    (fun χ => oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n))
    (((2 ^ n : ℕ) : ℂ)⁻¹)
  · intro g
    rfl
  · intro χ _
    simpa only [zpow_natCast] using
      (actual_root_odd_power_average n hn S e (basis.representation χ) root hroot).symm

theorem actual_root_odd_power_column_degree_zero {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) 1 = 0 := by
  apply actual_root_odd_power_column_support n hn S e basis ideal principal hprincipal root hroot
  apply one_not_mem_squareRootSection (a := n + 1) (by omega)
  rw [actualRoot_orderOf n hn S e, pow_succ, Nat.mul_comm]

theorem oddPowerCoefficient_eq_one_of_trivial_character {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (y : G) (m : ℕ) (hm : 0 < m)
    (hy : y ^ (2 * m) = 1) (root : ℂ) (hroot : IsPrimitiveRoot root (2 * m))
    (htrivial : data.character = 1) : oddPowerCoefficient data y root m = 1 := by
  have havg := full_odd_power_average_eigenmultiplicity data y m hm hy root hroot
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [htrivial] at havg
  simp only [Pi.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, inv_mul_cancel₀ hmc] at havg
  change (cyclicEigenmultiplicity data y root 0 : ℤ) -
    cyclicEigenmultiplicity data y root m = 1
  exact_mod_cast havg.symm

theorem actual_root_odd_power_principal_coefficient {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    oddPowerCoefficient (basis.representation principal) (actualRoot S e) root (2 ^ n) = 1 := by
  apply oddPowerCoefficient_eq_one_of_trivial_character _ _ _ (pow_pos (by omega) _)
    _ root hroot hprincipal
  rw [← actualRoot_orderOf n hn S e]
  exact pow_orderOf_eq_one _

theorem actual_root_integral_odd_power_column {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) ∈
        BlocksVChar G ∧
      (∀ g ∉ squareRootSection (actualRoot S e),
        oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) g = 0) ∧
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) 1 = 0 ∧
      oddPowerCoefficient (basis.representation principal) (actualRoot S e) root (2 ^ n) = 1 ∧
      ∀ χ : basis.index, ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n),
        (basis.representation χ).character (actualRoot S e ^ (2 * k + 1)) =
          (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) := by
  exact ⟨oddPowerPrincipalColumn_mem_virtual basis ideal principal _ root _,
    actual_root_odd_power_column_support n hn S e basis ideal principal hprincipal root hroot,
    actual_root_odd_power_column_degree_zero n hn S e basis ideal principal hprincipal root hroot,
    actual_root_odd_power_principal_coefficient n hn S e basis principal hprincipal root hroot,
    fun χ => actual_root_odd_power_average n hn S e (basis.representation χ) root hroot⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity

