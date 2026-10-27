module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveDegreeEightSupport

public section

open scoped Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem simple_local_parameter_five_faithful_rational_centralizer_degree_eight
    {G : Type}
    [Group G] [Fintype G] [IsSimpleGroup G] (hGnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ)
    (hn : 4 ≤ n) (S : Sylow 2 G) (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 5 1)
    (basis : FiniteIrreducibleCharacterBasis G) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2] :
    let B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal
    ∃ χ ψ : basis.index, χ ≠ ψ ∧ χ ∈ B ∧ ψ ∈ B ∧
      (basis.representation χ).IsIrreducible ∧ (basis.representation ψ).IsIrreducible ∧
      Function.Injective (basis.representation χ).representation ∧
      Function.Injective (basis.representation ψ).representation ∧
      (∀ g, ∃ q : ℚ, (basis.representation χ).character g = q) ∧
      (∀ g, ∃ q : ℚ, (basis.representation ψ).character g = q) ∧
      (basis.representation χ).character 1 = 21 ∧ (basis.representation ψ).character 1 = 20 ∧
      (basis.representation χ).character t = 5 ∧ (basis.representation ψ).character t = -4 ∧
      (∀ u : C t, u ∈ N t → (basis.representation χ).character (t * u) = 5 ∧
        (basis.representation ψ).character (t * u) = -4) ∧
      (∀ x : G, Odd (orderOf x) →
        (basis.representation ψ).character x = (basis.representation χ).character x - 1) ∧
      (let η : C t → ℂ := fun c =>
          ((basis.representation χ).character c - (basis.representation χ).character (t * c)) / 2
        ∀ V : FiniteComplexRepresentation.{0, 0} G,
          V.character = (basis.representation χ).character →
          let ρC : Representation ℂ (C t) V.vector := V.representation.comp (C t).subtype
          let E : Submodule ℂ V.vector := Module.End.eigenspace (ρC (tInC t)) (-1)
          ∃ hE : ∀ c : C t, E ≤ E.comap (ρC c),
            (ρC.subrepresentation E hE).character = η ∧ η 1 = 8 ∧ Module.finrank ℂ E = 8 ∧
            Function.Injective (ρC.subrepresentation E hE) ∧
            (∀ c : C t, ∃ q : ℚ, η c = q) ∧
            (∀ u : C t, u ∈ N t → ρC.subrepresentation E hE u = 1 → u = 1) ∧
            (∀ u : C t, u ∈ N t → ∃ q : ℚ, η u = q) ∧
            (∀ c u : C t, u ∈ N t → η (c * u * c⁻¹) = η u)) ∧
      Nat.card (N t) ∣ 3 ^ 4 * 5 * 7 ∧
      B.val.map (fun c => Module.finrank ℂ (basis.representation c).vector) =
        {1, 125, 21, 105, 20, 126, 126, 126} := by
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hGnonab
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg,
      -, hOF⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc 5 1
      (by norm_num) (by decide) le_rfl hmodel ideal basis principal hprincipal localBasis
      localPrincipal hlocalPrincipal
  have hq5 : Nat.card F = 5 := by rw [hcard, pow_one]
  exact local_parameter_five_degree_eight_of_family hGnonab n hn S fS t ht hnonab hcentral hnc
    hmodel basis ideal principal hprincipal localBasis localPrincipal (Nat.card F) hq5 _ rfl _ δ₁
    δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg (hOF S fS hcent)

end CFSG.Semidihedral.Principal
