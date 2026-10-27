module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityConstituents
public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityNegativeDegree

public noncomputable section
namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity
open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators Classical

variable {G : Type} [Group G] [Fintype G]

theorem character_eq_of_positive_multiplicity_and_degree
    (θ : FiniteComplexRepresentation.{0, 0} G) (χ : BlocksIrr G)
    (k : ℕ) (hk : 0 < k) (hpair : BlocksInnerProduct θ.character (χ : G → ℂ) = (k : ℂ))
    (hdegree : Module.finrank ℂ θ.vector ≤ irreducibleDegree χ) :
    θ.character = (χ : G → ℂ) ∧ Module.finrank ℂ θ.vector = irreducibleDegree χ := by
  obtain ⟨μ, hμ, _⟩ :=
    (complex_representation_character_decomposition θ.representation).2.1
  change θ.character = μ.sum (fun ψ r => (r : ℂ) • (ψ : G → ℂ)) at hμ
  have hdegreeμ : ∑ ψ ∈ μ.support, μ ψ * irreducibleDegree ψ =
      Module.finrank ℂ θ.vector := by
    have h := congrFun hμ 1
    change θ.representation.character 1 = _ at h
    rw [Representation.char_one, natural_expansion_degree] at h
    exact_mod_cast h.symm
  have hμχ : μ χ = k := by
    rw [hμ, natural_expansion_coefficient] at hpair
    exact_mod_cast hpair
  have hsingle := natural_expansion_single_of_degree_bound μ χ (by omega)
    (by rwa [hdegreeμ])
  rw [hsingle] at hμ
  have hchar : θ.character = (χ : G → ℂ) := by simpa using hμ
  refine ⟨hchar, ?_⟩
  have h := congrFun hchar 1
  change θ.representation.character 1 = _ at h
  rw [Representation.char_one, irreducibleDegree_cast] at h
  exact_mod_cast h

theorem actual_section_irreducible_of_negative_degree_floor
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) (d : ℕ)
    (hfloor : ∀ χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 →
        d ≤ Module.finrank ℂ (basis.representation χ).vector)
    (θ : FiniteComplexRepresentation.{0, 0} G)
    (hdegree : Module.finrank ℂ θ.vector ≤ d)
    (hsection : ∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
      v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
        θ.character (actualRoot S e ^ h * v) = -1) :
    θ.character ∈ BlocksIrr G ∧ θ.character ∈ BlocksPrincipalBlock ideal G ∧
      θ.character ≠ 1 ∧ Module.finrank ℂ θ.vector = d ∧
      ∃ χ : basis.index, θ.character = (basis.representation χ).character ∧
        oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 := by
  obtain ⟨χ, hirr, hblock, hnontrivial, hc, k, hk, hpair, hdeg⟩ :=
    actual_section_minus_one_has_principal_constituent n hn S e basis ideal principal
      hprincipal root hroot θ hsection
  have hχblock : χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal := by
    change (basis.representation χ).character ∈ BlocksBlockOf ideal G (1 : G → ℂ) at hblock
    rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal] at hblock
    obtain ⟨i, hi, heq⟩ := hblock
    rwa [basis.distinct heq] at hi
  have hχfloor := hfloor χ hχblock hc
  have hχdegree : Module.finrank ℂ (basis.representation χ).vector = d := by omega
  let χI : BlocksIrr G := ⟨(basis.representation χ).character, hirr⟩
  have hχIdegree : irreducibleDegree χI = Module.finrank ℂ (basis.representation χ).vector := by
    have h := irreducibleDegree_cast χI
    change (basis.representation χ).representation.character 1 = _ at h
    rw [Representation.char_one] at h
    exact_mod_cast h.symm
  obtain ⟨heq, hθdegree⟩ := character_eq_of_positive_multiplicity_and_degree θ χI k hk hpair
    (by rwa [hχIdegree, hχdegree])
  change θ.character = (basis.representation χ).character at heq
  refine ⟨by rwa [heq], by rwa [heq], by rwa [heq], ?_, χ, heq, hc⟩
  rwa [hχIdegree, hχdegree] at hθdegree

theorem actual_root_exists_least_negative_principal_degree
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∃ (d : ℕ) (χ : basis.index), 0 < d ∧
      χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (basis.representation χ).character ∈ BlocksIrr G ∧
      (basis.representation χ).character ∈ BlocksPrincipalBlock ideal G ∧
      (basis.representation χ).character ≠ 1 ∧
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 ∧
      Module.finrank ℂ (basis.representation χ).vector = d ∧
      ∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) < 0 →
          d ≤ Module.finrank ℂ (basis.representation ψ).vector := by
  let I := (coefficientBlock basis (localizedComplexIntegerRing ideal) principal).filter
    (fun χ => oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0)
  have hI : I.Nonempty := by
    obtain ⟨χ, hχ, _, _, _, hc, _⟩ := actual_root_exists_negative_principal_irreducible
      n hn S e basis ideal principal hprincipal root hroot
    exact ⟨χ, Finset.mem_filter.mpr ⟨hχ, hc⟩⟩
  obtain ⟨χ, hχI, hleast⟩ := Finset.exists_min_image I
    (fun χ => Module.finrank ℂ (basis.representation χ).vector) hI
  obtain ⟨hχ, hc⟩ := Finset.mem_filter.mp hχI
  have hdegree : 0 < Module.finrank ℂ (basis.representation χ).vector := by
    have h := irreducible_character_degree_ne_zero (basis.representation χ) (basis.irreducible χ)
    rw [FiniteComplexRepresentation.character, Representation.char_one] at h
    exact Nat.pos_of_ne_zero (by exact_mod_cast h)
  have hblock : (basis.representation χ).character ∈ BlocksPrincipalBlock ideal G := by
    change (basis.representation χ).character ∈ BlocksBlockOf ideal G (1 : G → ℂ)
    rw [← hprincipal, ← CFSG.BlockBasics.coefficientBlock_image basis ideal principal]
    exact ⟨χ, hχ, rfl⟩
  have hnontrivial : (basis.representation χ).character ≠ 1 := by
    intro h
    have hχp := basis.distinct (h.trans hprincipal.symm)
    subst χ
    rw [actual_root_odd_power_principal_coefficient n hn S e basis principal
      hprincipal root hroot] at hc
    omega
  refine ⟨_, χ, hdegree, hχ, CFSG.BlockBasics.basis_character_mem_irr basis χ,
    hblock, hnontrivial, hc, rfl, ?_⟩
  intro ψ hψ hcψ
  exact hleast ψ (Finset.mem_filter.mpr ⟨hψ, hcψ⟩)

theorem actual_root_minimal_degree_section_test
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
    [ideal.IsMaximal] [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (principal : basis.index) (hprincipal : (basis.representation principal).character = 1)
    (root : ℂ) (hroot : IsPrimitiveRoot root (2 * 2 ^ n)) :
    ∃ (d : ℕ) (χ : basis.index), 0 < d ∧
      χ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal ∧
      (basis.representation χ).character ∈ BlocksIrr G ∧
      (basis.representation χ).character ∈ BlocksPrincipalBlock ideal G ∧
      (basis.representation χ).character ≠ 1 ∧
      oddPowerCoefficient (basis.representation χ) (actualRoot S e) root (2 ^ n) < 0 ∧
      Module.finrank ℂ (basis.representation χ).vector = d ∧
      (∀ ψ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) < 0 →
          d ≤ Module.finrank ℂ (basis.representation ψ).vector) ∧
      ∀ θ : FiniteComplexRepresentation.{0, 0} G, Module.finrank ℂ θ.vector ≤ d →
        (∀ (h : ℤ) (v : G), Odd h → Odd (orderOf v) →
          v ∈ Subgroup.centralizer ({actualRoot S e} : Set G) →
            θ.character (actualRoot S e ^ h * v) = -1) →
        θ.character ∈ BlocksIrr G ∧ θ.character ∈ BlocksPrincipalBlock ideal G ∧
          θ.character ≠ 1 ∧ Module.finrank ℂ θ.vector = d ∧
          ∃ ψ : basis.index, θ.character = (basis.representation ψ).character ∧
            oddPowerCoefficient (basis.representation ψ) (actualRoot S e) root (2 ^ n) < 0 := by
  obtain ⟨d, χ, hd, hχ, hirr, hblock, hnontrivial, hc, hχdegree, hfloor⟩ :=
    actual_root_exists_least_negative_principal_degree n hn S e basis ideal
      principal hprincipal root hroot
  exact ⟨d, χ, hd, hχ, hirr, hblock, hnontrivial, hc, hχdegree, hfloor,
    fun θ hdegree hsection => actual_section_irreducible_of_negative_degree_floor
      n hn S e basis ideal principal hprincipal root hroot d hfloor θ hdegree hsection⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
