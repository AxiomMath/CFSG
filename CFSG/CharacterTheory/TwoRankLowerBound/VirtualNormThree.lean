module

public import CFSG.CharacterTheory.TwoRankLowerBound.NormThree
public import CFSG.CharacterTheory.TwoRankLowerBound.CharacterExpansion

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem virtual_character_norm_three_involution_product_contradicts_simple
    {G : Type*} [Group G] [Fintype G] [IsSimpleGroup G]
    (involution : G) (horder : orderOf involution = 2) (function : G → ℂ)
    (hvirtual : function ∈ virtualCharacters G)
    (hprincipal : characterPairing function 1 = 1)
    (hnorm : characterPairing function function = 3)
    (hidentity : function 1 = 0) (hinvolution : function involution = 0)
    (hvanishing : ∀ left right : G, orderOf left = 2 → orderOf right = 2 →
      function (left * right) = 0) : False := by
  obtain ⟨data⟩ := virtualCharacter_exists_irreducibleCharacterExpansion hvirtual
  obtain ⟨principal, hprincipalcharacter, hcoefficient⟩ :=
    expansion_exists_principal_of_pairing_one data hprincipal
  let : ∀ label : data.index, (data.representation label).representation.IsIrreducible :=
    data.irreducible
  have hquadratic := character_expansion_quadratic_zero_of_involution_product_vanishing
    involution horder function hvanishing (fun label => (data.representation label).vector)
    (fun label => (data.representation label).representation)
    (fun label => (data.coefficient label : ℂ))
    (fun label => irreducible_character_degree_ne_zero _ (data.irreducible label)) data.expansion
  obtain ⟨label, hne, _, hequal⟩ := integer_norm_three_quadratic_rigidity data.coefficient principal
    (fun label => (data.representation label).character 1)
    (fun label => (data.representation label).character involution)
    hcoefficient (expansion_integer_norm_of_pairing_three data hnorm)
    (congrFun hprincipalcharacter 1) (congrFun hprincipalcharacter involution)
    (fun label => irreducible_character_degree_ne_zero _ (data.irreducible label))
    ((data.expansion 1).symm.trans hidentity)
    ((data.expansion involution).symm.trans hinvolution) hquadratic
  have hnonprincipal : (data.representation label).character ≠ 1 := by
    intro htrivial
    exact hne (data.distinct (htrivial.trans hprincipalcharacter.symm))
  exact representation_involution_character_ne_degree_of_simple
    (data.representation label).representation
    (irreducible_character_ne_one_has_nontrivial_action _ (data.irreducible label) hnonprincipal)
    involution horder hequal

theorem rank_one_root_virtual_character_norm_three_contradicts_simple
    {G : Type*} [Group G] [Fintype G] [IsSimpleGroup G]
    (hrank : CFSG.Open.twoRank G ≤ 1)
    (involution : G) (horder : orderOf involution = 2)
    (function : Subgroup.centralizer ({involution} : Set G) → ℂ)
    (hsupport : ∀ element : Subgroup.centralizer ({involution} : Set G),
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (hvirtual : function ∈ virtualCharacters (Subgroup.centralizer ({involution} : Set G)))
    (hprincipal : characterPairing
      (inducedFunction (Subgroup.centralizer ({involution} : Set G)) function) 1 = 1)
    (hnorm : characterPairing
      (inducedFunction (Subgroup.centralizer ({involution} : Set G)) function)
      (inducedFunction (Subgroup.centralizer ({involution} : Set G)) function) = 3)
    (hidentity : inducedFunction (Subgroup.centralizer ({involution} : Set G)) function 1 = 0)
    (hinvolution : inducedFunction (Subgroup.centralizer ({involution} : Set G)) function involution = 0) :
    False := by
  obtain ⟨data⟩ := virtualCharacter_exists_irreducibleCharacterExpansion
    (inducedFunction_mem_virtualCharacters _ hvirtual)
  obtain ⟨principal, hprincipalcharacter, hcoefficient⟩ :=
    expansion_exists_principal_of_pairing_one data hprincipal
  let : ∀ label : data.index, (data.representation label).representation.IsIrreducible :=
    data.irreducible
  have hnormcoeff := expansion_integer_norm_of_pairing_three data hnorm
  apply rank_one_norm_three_character_witness_contradicts_simple hrank involution horder
    (fun label => (data.representation label).vector)
    (fun label => (data.representation label).representation) data.coefficient principal
    hcoefficient hnormcoeff
  · intro element
    exact congrFun hprincipalcharacter element
  · intro label
    exact irreducible_character_degree_ne_zero _ (data.irreducible label)
  · intro label hne
    apply irreducible_character_ne_one_has_nontrivial_action _ (data.irreducible label)
    intro hequal
    exact hne (data.distinct (hequal.trans hprincipalcharacter.symm))
  · exact (data.expansion 1).symm.trans hidentity
  · exact (data.expansion involution).symm.trans hinvolution
  · exact hsupport
  · exact data.expansion

end CFSG.TwoRankLowerBound.Helpers
