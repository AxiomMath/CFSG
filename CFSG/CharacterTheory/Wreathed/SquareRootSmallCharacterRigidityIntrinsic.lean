module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityThreeLabels
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityMinimalDegree

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

@[expose] def rootCharacterAverage {G : Type} [Group G] (n : ℕ) (y : G) (χ : G → ℂ) : ℂ :=
  ((2 ^ n : ℕ) : ℂ)⁻¹ * ∑ k ∈ Finset.range (2 ^ n), χ (y ^ (2 * k + 1))

@[expose] def rootPrincipalAverageColumn {G : Type} [Group G] (n : ℕ)
    (ideal : Ideal ComplexAlgebraicIntegers) (y : G) : G → ℂ :=
  fun g => ∑ᶠ χ ∈ BlocksPrincipalBlock ideal G, rootCharacterAverage n y χ * χ g

theorem actual_root_character_average_integer {G : Type} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (θ : FiniteComplexRepresentation.{0, 0} G) :
    ∃ k : ℤ, rootCharacterAverage n (actualRoot S e) θ.character = (k : ℂ) := by
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  exact ⟨oddPowerCoefficient θ (actualRoot S e) root (2 ^ n),
    actual_root_odd_power_average n hn S e θ root hroot⟩

theorem actual_root_principal_average_column_eq {G : Type} [Group G] [Fintype G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    rootPrincipalAverageColumn n ideal (actualRoot S e) =
      oddPowerPrincipalColumn basis ideal principal (actualRoot S e) root (2 ^ n) := by
  ext g
  unfold rootPrincipalAverageColumn
  change (∑ᶠ χ ∈ BlocksBlockOf ideal G (1 : G → ℂ),
    rootCharacterAverage n (actualRoot S e) χ * χ g) = _
  rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal,
    finsum_mem_image basis.distinct.injOn, finsum_mem_coe_finset]
  apply Finset.sum_congr rfl
  intro χ _
  rw [show rootCharacterAverage n (actualRoot S e) (basis.representation χ).character =
    (oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) : ℂ) from
      actual_root_odd_power_average n hn S e (basis.representation χ) root hroot]

variable {G : Type} [Group G] [Fintype G]

private theorem intrinsic_basis_principal :
    ∃ (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index),
      (basis.representation principal).character = 1 := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  exact ⟨basis, principal, hprincipal⟩

theorem actual_root_intrinsic_integral_column
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    rootPrincipalAverageColumn n ideal (actualRoot S e) ∈ BlocksVChar G ∧
      (∀ g ∉ squareRootSection (actualRoot S e),
        rootPrincipalAverageColumn n ideal (actualRoot S e) g = 0) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) 1 = 0 ∧
      BlocksInnerProduct (1 : G → ℂ) (rootPrincipalAverageColumn n ideal (actualRoot S e)) = 1 ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        BlocksInnerProduct θ.character (rootPrincipalAverageColumn n ideal (actualRoot S e)) =
          -1 := by
  obtain ⟨basis, principal, hprincipal⟩ := intrinsic_basis_principal (G := G)
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  rw [actual_root_principal_average_column_eq n hn S e basis ideal principal hprincipal
    root hroot]
  obtain ⟨hvirtual, hoff, hzero, _, _⟩ := actual_root_integral_odd_power_column
    n hn S e basis ideal principal hprincipal root hroot
  refine ⟨hvirtual, hoff, hzero, ?_, ?_⟩
  · rw [oddPowerPrincipalColumn_principal_pairing basis ideal principal hprincipal,
      actual_root_odd_power_principal_coefficient n hn S e basis principal hprincipal root hroot]
    norm_num
  · exact fun θ hθ => actual_section_minus_one_column_pairing n hn S e basis ideal principal
      hprincipal root hroot θ hθ

theorem actual_root_intrinsic_three_characters
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (α : Fin 3 → BlocksIrr G) (β : Fin 3 → ℤ), Function.Injective α ∧
      (∀ i, (α i : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (α i : G → ℂ) ≠ 1 ∧
        (β i = 1 ∨ β i = -1) ∧
        rootCharacterAverage n (actualRoot S e) (α i : G → ℂ) = (β i : ℂ)) ∧
      (∀ χ : BlocksIrr G, (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G →
        (rootCharacterAverage n (actualRoot S e) (χ : G → ℂ) ≠ 0 ↔
          (χ : G → ℂ) = 1 ∨ ∃ i, α i = χ)) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) =
        (1 : G → ℂ) + ∑ i, β i • (α i : G → ℂ) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) ∈ BlocksVChar G ∧
      (∀ g ∉ squareRootSection (actualRoot S e),
        rootPrincipalAverageColumn n ideal (actualRoot S e) g = 0) ∧
      rootPrincipalAverageColumn n ideal (actualRoot S e) 1 = 0 ∧
      ((1 : ℤ) + ∑ i, β i * (irreducibleDegree (α i) : ℤ) = 0) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G,
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        ∃ i : Fin 3, β i = -1 ∧ ∃ k : ℕ, 0 < k ∧
          BlocksInnerProduct θ.character (α i : G → ℂ) = (k : ℂ) ∧
          irreducibleDegree (α i) ≤ Module.finrank ℂ θ.vector := by
  obtain ⟨basis, principal, hprincipal⟩ := intrinsic_basis_principal (G := G)
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  obtain ⟨ι, β, hι, hdata, hsupport, hsum, _, _, hdegree, hdetect⟩ :=
    actual_root_three_labels_and_genuine_section_detection n hn S e basis ideal principal
      hprincipal root hroot
  let α : Fin 3 → BlocksIrr G := fun i =>
    ⟨(basis.representation (ι i)).character, (hdata i).2.2.1⟩
  have hα : Function.Injective α := by
    intro i j h
    exact hι (basis.distinct (congrArg Subtype.val h))
  have hαdegree : ∀ i, irreducibleDegree (α i) =
      Module.finrank ℂ (basis.representation (ι i)).vector := by
    intro i
    have h := irreducibleDegree_cast (α i)
    change (basis.representation (ι i)).representation.character 1 = _ at h
    rw [Representation.char_one] at h
    exact_mod_cast h.symm
  obtain ⟨hvirtual, hoff, hzero, _, _⟩ := actual_root_intrinsic_integral_column n hn S e ideal
  refine ⟨α, β, hα, ?_, ?_, ?_, hvirtual, hoff, hzero, ?_, ?_⟩
  · intro i
    obtain ⟨_, _, _, hblock, hnontrivial, hβ, hc⟩ := hdata i
    refine ⟨hblock, hnontrivial, hβ, ?_⟩
    change rootCharacterAverage n (actualRoot S e) (basis.representation (ι i)).character = _
    rw [show rootCharacterAverage n (actualRoot S e) (basis.representation (ι i)).character =
      (oddPowerCoefficient (basis.representation (ι i)) (actualRoot S e) root (2 ^ n) : ℂ) from
        actual_root_odd_power_average n hn S e (basis.representation (ι i)) root hroot, hc]
  · intro χ hχ
    obtain ⟨ψ, hψ⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis χ.property
    have hψblock : ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
      change (χ : G → ℂ) ∈ BlocksBlockOf ideal G (1 : G → ℂ) at hχ
      rw [← hψ, ← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
        at hχ
      obtain ⟨ψ', hψ', heq⟩ := hχ
      rwa [basis.distinct heq] at hψ'
    rw [← hψ, show rootCharacterAverage n (actualRoot S e) (basis.representation ψ).character =
      (oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) : ℂ) from
        actual_root_odd_power_average n hn S e (basis.representation ψ) root hroot]
    rw [Int.cast_ne_zero, hsupport ψ hψblock]
    constructor
    · rintro (hp | ⟨i, hi⟩)
      · left
        rw [hp]
        exact hprincipal
      · right
        refine ⟨i, ?_⟩
        apply Subtype.ext
        change (basis.representation (ι i)).character = (χ : G → ℂ)
        rw [hi, hψ]
    · rintro (hp | ⟨i, hi⟩)
      · left
        exact basis.distinct (hp.trans hprincipal.symm)
      · right
        refine ⟨i, ?_⟩
        apply basis.distinct
        change (basis.representation (ι i)).character = (basis.representation ψ).character
        have h := congrArg Subtype.val hi
        exact h.trans hψ.symm
  · rw [actual_root_principal_average_column_eq n hn S e basis ideal principal hprincipal
      root hroot]
    exact hsum
  · simpa only [hαdegree] using hdegree
  · intro θ hθ
    obtain ⟨i, hi, k, hk, hpair, hdeg⟩ := hdetect θ hθ
    exact ⟨i, hi, k, hk, hpair, by rwa [hαdegree]⟩

theorem actual_root_intrinsic_minimal_degree
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    ∃ (d : ℕ) (χ : BlocksIrr G), 0 < d ∧
      (χ : G → ℂ) ∈ BlocksPrincipalBlock ideal G ∧ (χ : G → ℂ) ≠ 1 ∧
      (∃ c : ℤ, c < 0 ∧ rootCharacterAverage n (actualRoot S e) (χ : G → ℂ) = (c : ℂ)) ∧
      irreducibleDegree χ = d ∧
      (∀ ψ : BlocksIrr G, (ψ : G → ℂ) ∈ BlocksPrincipalBlock ideal G →
        (∃ c : ℤ, c < 0 ∧ rootCharacterAverage n (actualRoot S e) (ψ : G → ℂ) = (c : ℂ)) →
          d ≤ irreducibleDegree ψ) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G, Module.finrank ℂ θ.vector ≤ d →
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        θ.character ∈ BlocksIrr G ∧ θ.character ∈ BlocksPrincipalBlock ideal G ∧
          θ.character ≠ 1 ∧ Module.finrank ℂ θ.vector = d ∧
          ∃ ψ : BlocksIrr G, θ.character = (ψ : G → ℂ) ∧ irreducibleDegree ψ = d ∧
            ∃ c : ℤ, c < 0 ∧
              rootCharacterAverage n (actualRoot S e) (ψ : G → ℂ) = (c : ℂ) := by
  obtain ⟨basis, principal, hprincipal⟩ := intrinsic_basis_principal (G := G)
  let root := Complex.exp (2 * Real.pi * Complex.I / (2 * 2 ^ n : ℕ))
  have hroot : IsPrimitiveRoot root (2 * 2 ^ n) :=
    Complex.isPrimitiveRoot_exp _ (by positivity)
  obtain ⟨d, label, hd, _, hirr, hblock, hnontrivial, hc, hdegree, hfloor, hdetect⟩ :=
    actual_root_minimal_degree_section_test n hn S e basis ideal principal hprincipal root hroot
  let χ : BlocksIrr G := ⟨(basis.representation label).character, hirr⟩
  have hχdegree : irreducibleDegree χ = d := by
    have h := irreducibleDegree_cast χ
    change (basis.representation label).representation.character 1 = _ at h
    rw [Representation.char_one, hdegree] at h
    exact_mod_cast h.symm
  refine ⟨d, χ, hd, hblock, hnontrivial, ?_, hχdegree, ?_, ?_⟩
  · exact ⟨_, hc, actual_root_odd_power_average n hn S e (basis.representation label)
      root hroot⟩
  · intro ψ hψ ⟨c, hc, havg⟩
    obtain ⟨labelψ, heq⟩ := CFSG.BlockBasics.exists_label_of_mem_irr basis ψ.property
    have hmem : labelψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
      change (ψ : G → ℂ) ∈ BlocksBlockOf ideal G (1 : G → ℂ) at hψ
      rw [← heq, ← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
        at hψ
      obtain ⟨label', hlabel', heq'⟩ := hψ
      rwa [basis.distinct heq'] at hlabel'
    have hcoeff : oddPowerCoefficient (basis.representation labelψ) (actualRoot S e) root
        (2 ^ n) = c := by
      have h := actual_root_odd_power_average n hn S e (basis.representation labelψ) root hroot
      change rootCharacterAverage n (actualRoot S e) (basis.representation labelψ).character =
        _ at h
      rw [heq, havg] at h
      exact_mod_cast h.symm
    have hdeg := hfloor labelψ hmem (by rw [hcoeff]; exact hc)
    have h := irreducibleDegree_cast ψ
    rw [← heq] at h
    change (basis.representation labelψ).representation.character 1 = _ at h
    rw [Representation.char_one] at h
    have heqdeg : Module.finrank ℂ (basis.representation labelψ).vector =
        irreducibleDegree ψ := by exact_mod_cast h
    rwa [heqdeg] at hdeg
  · intro θ hθdegree hθ
    obtain ⟨hθirr, hθblock, hθnontrivial, hθdeg, ψ, hψ, hcψ⟩ := hdetect θ hθdegree hθ
    let ψI : BlocksIrr G := ⟨θ.character, hθirr⟩
    refine ⟨hθirr, hθblock, hθnontrivial, hθdeg, ψI, rfl, ?_, ?_⟩
    · have h := irreducibleDegree_cast ψI
      change θ.representation.character 1 = _ at h
      rw [Representation.char_one, hθdeg] at h
      exact_mod_cast h.symm
    · refine ⟨_, hcψ, ?_⟩
      change rootCharacterAverage n (actualRoot S e) θ.character = _
      rw [hψ]
      exact actual_root_odd_power_average n hn S e (basis.representation ψ) root hroot

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
