module

public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterSevenNineOrdersSupport
public import CFSG.CharacterTheory.BlockBasics.LocalRing

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem perfect_local_parameter_seven_nine_exact_order_alternatives
    {G : Type} [Group G]
    [Fintype G] [Group.IsPerfect G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2))
    [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))]
    (hnonab : ∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a)
    (hcentral : Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥)
    (hnc : ∀ U : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic U)
    (p f : ℕ) (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hq : p ^ f = 7 ∨ p ^ f = 9)
    (hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (CFSG.generalizedFitting (Gamma t)) .PSL 2 p f) :
    let CN : Subgroup (N t) :=
      ((Subgroup.centralizer {(fS (s n) : G)}).comap (C t).subtype).subgroupOf (N t)
    let a₀ := Nat.card CN
    let b₀ := CN.index
    let X : ℕ × ℕ := (Nat.card G, (C t).index)
    n = 5 ∧ Nat.card (C t) = 2 * a₀ * b₀ * p ^ f * ((p ^ f) ^ 2 - 1) ∧
      (Nat.card ↥(C t ⊓ Subgroup.centralizer {(fS (s n) : G)}) : ℤ) =
        2 * a₀ * ((p ^ f : ℕ) + if p ^ f = 7 then -1 else 1) ∧
      ((p ^ f = 7 ∧ (X = (2328480 * a₀ * b₀ ^ 3, 3465 * b₀ ^ 2) ∨
          X = (1876896 * a₀ * b₀ ^ 3, 2793 * b₀ ^ 2))) ∨
        (p ^ f = 9 ∧ (X = (8514720 * a₀ * b₀ ^ 3, 5913 * b₀ ^ 2) ∨
          X = (6441120 * a₀ * b₀ ^ 3, 4473 * b₀ ^ 2) ∨
          X = (7236000 * a₀ * b₀ ^ 3, 5025 * b₀ ^ 2)))) ∧
      b₀ ^ 2 ∣ (C t).index := by
  have hG : ∀ U : Subgroup G, U.index ≠ 2 := RotationCongruence.index_ne_two_of_isPerfect
  obtain ⟨-, ht2, hcent, -, -, -⟩ := supplied_t_s_facts hn fS ht
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨principal, hprincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible basis
    (principalFiniteComplexRepresentation G) (principalFiniteComplexRepresentation_isIrreducible G)
  rw [principalFiniteComplexRepresentation_character] at hprincipal
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists (G := C t)
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation (C t))
    (principalFiniteComplexRepresentation_isIrreducible (C t))
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨⟨ideal, hmax, h2⟩, hchar⟩ := CFSG.BlockBasics.residue_prime_existence 2 Nat.prime_two
  have : ideal.IsMaximal := hmax
  have : CharP (ComplexAlgebraicIntegers ⧸ ideal) 2 := hchar ideal hmax h2
  obtain ⟨F, hF, hFfin, ρ, hcard, -, -, -, -, -, δ₁, δ₂, δ₃, δ₄, χ₁, χ₂, χ₃, χ₄, ψ, ν, hfam, hdeg,
      -, hOF⟩ :=
    actual_nonsimple_layer_principal_order_formulas n hn S fS hG t ht2 hnonab hcentral hnc p f
      hp hpodd hf hmodel ideal basis principal hprincipal localBasis localPrincipal
      hlocalPrincipal
  exact local_parameter_seven_nine_orders_of_family n hn S fS t ht hnonab hcentral hnc p f hp
    hpodd hf hq hmodel basis ideal principal hprincipal localBasis localPrincipal (Nat.card F)
    hcard _ rfl _ δ₁ δ₂ δ₃ δ₄ χ₁ χ₂ χ₃ χ₄ ψ ν hfam hdeg (hOF S fS hcent)

end CFSG.Semidihedral.Principal
