module

public import CFSG.CharacterTheory.BrauerThirdMainTheorem.Projection
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues

public section

open CFSG
namespace CFSG.BrauerThirdMainTheorem.Helpers

theorem centralizer_subgroupOf_iff {G : Type*} [Group G]
    (subgroup overgroup : Subgroup G) (hsubgroup : subgroup ≤ overgroup) (element : overgroup) :
    element ∈ Subgroup.centralizer (subgroup.subgroupOf overgroup : Set overgroup) ↔
      element.val ∈ Subgroup.centralizer (subgroup : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hcentral factor hfactor
    have hequal := hcentral ⟨factor, hsubgroup hfactor⟩ hfactor
    exact congrArg Subtype.val hequal
  · intro hcentral factor hfactor
    exact Subtype.ext (hcentral factor.val hfactor)

theorem brauerProj_transitive {G : Type*} [Group G]
    (small large overgroup finalGroup : Subgroup G)
    (hsmall : small ≤ large) (hlarge : large ≤ overgroup) (hfinal : finalGroup ≤ overgroup)
    (coefficients : G → ℂ) (element : finalGroup) :
    BlocksBrauerProj (large.subgroupOf overgroup) (finalGroup.subgroupOf overgroup)
      (BlocksBrauerProj small overgroup coefficients)
      ⟨⟨element.val, hfinal element.property⟩, element.property⟩ =
      BlocksBrauerProj large finalGroup coefficients element := by
  classical
  rw [brauerProj_apply, centralizer_subgroupOf_iff large overgroup hlarge, brauerProj_apply,
    brauerProj_apply]
  by_cases hcentral : element.val ∈ Subgroup.centralizer (large : Set G)
  · have hsmallCentral := Subgroup.centralizer_le hsmall hcentral
    simp only [hcentral, hsmallCentral, ↓reduceIte]
  · simp only [hcentral, ↓reduceIte]

theorem brauerCorr_unique_image (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    (G : Type) [Group G] [Finite G] (subgroup overgroup : Subgroup G)
    {localBlock : Set (overgroup → ℂ)} (hlocal : localBlock.Nonempty)
    {left right : Set (G → ℂ)} (hleft : BlocksIsBlock m G left) (hright : BlocksIsBlock m G right)
    (hleftCorr : BlocksBrauerCorr m subgroup overgroup localBlock left)
    (hrightCorr : BlocksBrauerCorr m subgroup overgroup localBlock right) : left = right := by
  obtain ⟨localCharacter, hlocalCharacter⟩ := hlocal
  obtain ⟨leftCharacter, hleftCharacter⟩ := block_nonempty m hleft
  obtain ⟨rightCharacter, hrightCharacter⟩ := block_nonempty m hright
  have hsame : rightCharacter ∈ BlocksBlockOf m G leftCharacter := by
    apply mem_blockOf_of_centralChar_congr m hm G (block_subset_irr m hleft hleftCharacter)
      (block_subset_irr m hright hrightCharacter)
    intro coefficients hcoefficients
    have hleftScalar := hleftCorr coefficients hcoefficients leftCharacter hleftCharacter
      localCharacter hlocalCharacter
    have hrightScalar := hrightCorr coefficients hcoefficients rightCharacter hrightCharacter
      localCharacter hlocalCharacter
    have hnegative : BlocksCentralChar localCharacter (BlocksBrauerProj subgroup overgroup coefficients) -
        BlocksCentralChar leftCharacter coefficients ∈ BlocksLocalMaxIdeal m := by
      convert localMaxIdeal_neg m hleftScalar using 1
      ring
    exact localMaxIdeal_trans m hm hrightScalar hnegative
  rw [block_eq_blockOf_member m hleft hleftCharacter, block_eq_blockOf_member m hright hrightCharacter]
  exact (blockOf_eq_of_mem m (block_subset_irr m hleft hleftCharacter) hsame).symm

end CFSG.BrauerThirdMainTheorem.Helpers
