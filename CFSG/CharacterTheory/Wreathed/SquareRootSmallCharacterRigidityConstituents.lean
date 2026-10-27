module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityIntegralAverage
public import CFSG.CharacterTheory.BlockBasics.Bridge

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G]

theorem innerProduct_finite_integral_column {ι : Type*} (I : Finset ι)
    (f : G → ℂ) (χ : ι → G → ℂ) (c : ι → ℤ) :
    BlocksInnerProduct f (∑ i ∈ I, c i • χ i) =
      ∑ i ∈ I, (c i : ℂ) * BlocksInnerProduct f (χ i) := by
  induction I using Finset.induction_on with
  | empty => simp [BlocksInnerProduct]
  | @insert i I hi hI =>
    rw [Finset.sum_insert hi, innerProduct_add_right, innerProduct_zsmul_right, hI,
      Finset.sum_insert hi]

theorem negative_integral_column_has_constituent {ι : Type*} (I : Finset ι)
    (χ : ι → BlocksIrr G) (c : ι → ℤ) (θ : FiniteComplexRepresentation.{0, 0} G)
    {t : ℤ} (ht : t < 0)
    (hpair : BlocksInnerProduct θ.character (∑ i ∈ I, c i • (χ i : G → ℂ)) = t) :
    ∃ i ∈ I, c i < 0 ∧ ∃ k : ℕ, 0 < k ∧
      BlocksInnerProduct θ.character (χ i : G → ℂ) = (k : ℂ) ∧
      irreducibleDegree (χ i) ≤ Module.finrank ℂ θ.vector := by
  obtain ⟨μ, hμ, _⟩ :=
    (complex_representation_character_decomposition θ.representation).2.1
  change θ.character = μ.sum (fun χ k => (k : ℂ) • (χ : G → ℂ)) at hμ
  have hcoeff (ψ : BlocksIrr G) :
      BlocksInnerProduct θ.character (ψ : G → ℂ) = (μ ψ : ℂ) := by
    rw [hμ]
    exact natural_expansion_coefficient μ ψ
  have hsum : ∑ i ∈ I, c i * (μ (χ i) : ℤ) = t := by
    rw [innerProduct_finite_integral_column] at hpair
    simp only [hcoeff] at hpair
    exact_mod_cast hpair
  have hnegative : ∃ i ∈ I, c i * (μ (χ i) : ℤ) < 0 := by
    by_contra! hnone
    have hnonneg := Finset.sum_nonneg hnone
    rw [hsum] at hnonneg
    omega
  obtain ⟨i, hi, hneg⟩ := hnegative
  have hμpos : 0 < μ (χ i) := by
    by_contra h
    have hzero : μ (χ i) = 0 := by omega
    simp only [hzero, Nat.cast_zero, mul_zero] at hneg
    omega
  have hcneg : c i < 0 := by
    have hnat : (0 : ℤ) ≤ μ (χ i) := by omega
    by_contra h
    have hnonneg := mul_nonneg (show 0 ≤ c i by omega) hnat
    omega
  have hdegree : ∑ ψ ∈ μ.support, μ ψ * irreducibleDegree ψ =
      Module.finrank ℂ θ.vector := by
    have h := congrFun hμ 1
    change θ.representation.character 1 = _ at h
    rw [Representation.char_one, natural_expansion_degree] at h
    exact_mod_cast h.symm
  refine ⟨i, hi, hcneg, μ (χ i), hμpos, hcoeff _, ?_⟩
  have hle := multiplicity_degree_le μ (χ i)
  rw [hdegree] at hle
  nlinarith

theorem innerProduct_of_constant_on_support (U : Set G) (f T : G → ℂ) (δ : ℂ)
    (hT : ∀ g ∉ U, T g = 0) (hf : ∀ g ∈ U, f g = δ) :
    BlocksInnerProduct f T = δ * BlocksInnerProduct (1 : G → ℂ) T := by
  rw [innerProduct_eq_of_agree_on_support U f (fun _ => δ) T hT hf]
  unfold BlocksInnerProduct
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.mul_sum]
  ring

theorem oddPowerPrincipalColumn_principal_pairing
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsPrime] (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (y : G) (root : ℂ) (m : ℕ) :
    BlocksInnerProduct (1 : G → ℂ) (oddPowerPrincipalColumn basis ideal principal y root m) =
      (oddPowerCoefficient (basis.representation principal) y root m : ℂ) := by
  have hcolumn : oddPowerPrincipalColumn basis ideal principal y root m =
      ∑ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation χ) y root m •
          (basis.representation χ).character := by
    ext g
    simp only [oddPowerPrincipalColumn, Finset.sum_apply, zsmul_eq_mul,
      Pi.mul_apply, Pi.intCast_apply]
  rw [hcolumn, innerProduct_finite_integral_column]
  have hpair (χ : basis.index) :
      BlocksInnerProduct (1 : G → ℂ) (basis.representation χ).character =
        if χ = principal then 1 else 0 := by
    rw [← hprincipal, blocksInnerProduct_eq_characterPairing _
      (AddSubgroup.subset_closure (CFSG.BlockBasics.basis_character_mem_irr basis χ))]
    simpa only [basis.distinct.eq_iff, eq_comm] using
      characterPairing_irreducible (basis.representation principal) (basis.representation χ)
        (basis.irreducible principal) (basis.irreducible χ)
  simp only [hpair, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', coefficientBlock_self_mem, ite_true]

theorem actual_section_minus_one_column_pairing
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n))
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        θ.character (actualRoot S e ^ h * v) = -1) :
    BlocksInnerProduct θ.character
      (oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n)) = -1 := by
  have hclass : BlocksIsClassFunction θ.character :=
    fun g a => Representation.char_conj θ.representation g a
  rw [innerProduct_of_constant_on_support (squareRootSection (actualRoot S e))
    θ.character _ (-1) (actual_root_odd_power_column_support n hn S e basis ideal
      principal hprincipal root hroot) ((classFunction_section_value_iff hclass).mp hsection)]
  rw [oddPowerPrincipalColumn_principal_pairing basis ideal principal hprincipal,
    actual_root_odd_power_principal_coefficient n hn S e basis principal hprincipal root hroot]
  norm_num

theorem actual_section_minus_one_has_principal_constituent
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n))
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        θ.character (actualRoot S e ^ h * v) = -1) :
    ∃ χ : basis.index, (basis.representation χ).character ∈ BlocksIrr G ∧
      (basis.representation χ).character ∈ BlocksPrincipalBlock ideal G ∧
      (basis.representation χ).character ≠ 1 ∧
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 ∧
      ∃ k : ℕ, 0 < k ∧
        BlocksInnerProduct θ.character (basis.representation χ).character = (k : ℂ) ∧
        Module.finrank ℂ (basis.representation χ).vector ≤ Module.finrank ℂ θ.vector := by
  let χ : basis.index → BlocksIrr G := fun i =>
    ⟨(basis.representation i).character, CFSG.BlockBasics.basis_character_mem_irr basis i⟩
  let c : basis.index → ℤ := fun i =>
    oddPowerCoefficient (basis.representation i) (actualRoot S e) root (2 ^ n)
  have hcolumn : oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) =
      ∑ i ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        c i • (χ i : G → ℂ) := by
    ext g
    simp only [oddPowerPrincipalColumn, Finset.sum_apply, zsmul_eq_mul,
      Pi.mul_apply, Pi.intCast_apply, c, χ]
  have hpair := actual_section_minus_one_column_pairing n hn S e basis ideal principal
    hprincipal root hroot θ hsection
  rw [hcolumn] at hpair
  obtain ⟨i, hi, hci, k, hk, hki, hdeg⟩ := negative_integral_column_has_constituent
    (coefficientBlock basis (localizedComplexIntegerRing ideal) principal) χ c θ
      (show (-1 : ℤ) < 0 by omega) (by exact_mod_cast hpair)
  have hblock : (basis.representation i).character ∈ BlocksPrincipalBlock ideal G := by
    change (basis.representation i).character ∈ BlocksBlockOf ideal G (1 : G → ℂ)
    rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
    exact ⟨i, hi, rfl⟩
  have hnontrivial : (basis.representation i).character ≠ 1 := by
    intro h
    have hcoeff := oddPowerCoefficient_eq_one_of_trivial_character (basis.representation i)
      (actualRoot S e) (2 ^ n) (pow_pos (by omega) _) (by
        rw [← actualRoot_orderOf n hn S e]
        exact pow_orderOf_eq_one _) root hroot h
    change oddPowerCoefficient (basis.representation i) (actualRoot S e) root (2 ^ n) < 0 at hci
    omega
  have hdeg' : Module.finrank ℂ (basis.representation i).vector = irreducibleDegree (χ i) := by
    have h := irreducibleDegree_cast (χ i)
    change (basis.representation i).representation.character 1 = _ at h
    rw [Representation.char_one] at h
    exact_mod_cast h
  exact ⟨i, CFSG.BlockBasics.basis_character_mem_irr basis i, hblock, hnontrivial, hci,
    k, hk, hki, by rwa [hdeg']⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
