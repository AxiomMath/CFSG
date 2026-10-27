module

public import CFSG.LocalAnalysis.ComponentClassification.ComponentFamilyPumpUpFusion
public import CFSG.LocalAnalysis.ComponentClassification.BlockFusion

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockFactorInvolutions

theorem mem_fusion_set {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component)
    (member : G) (hmember : member ∈ factor) (horder : orderOf member = 2) :
    member ∈ BlockFusion.involutions component := by
  classical
  let Index := ↥(UniversalOrbitBlock.block component)
  let : Fintype Index := Fintype.ofFinite Index
  have hfamilyCard : 3 ≤ Fintype.card Index := by simpa only [Nat.card_eq_fintype_card] using hcard
  let first : Index := ⟨factor, hfactor⟩
  obtain ⟨other, hother, _⟩ := ComponentFamilyPumpUpFusion.exists_outside_two hfamilyCard first first
  exact ⟨horder, other.val, other.property,
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (UniversalOrbitBlock.block_commutes component heven huniversal factor hfactor other.val other.property
        (fun heq => hother (Subtype.ext heq.symm))) hmember⟩

theorem complement_le {G : Type*} [Group G] (proper containing : Subgroup G)
    (hproper : proper ≠ ⊤) (hcomplement : ∀ member : G, member ∉ proper → member ∈ containing) :
    containing = ⊤ := by
  have houtside : ∃ member : G, member ∉ proper := by
    by_contra hnone
    apply hproper
    apply top_unique
    intro member _
    exact Classical.not_not.mp (fun hnot => hnone ⟨member, hnot⟩)
  obtain ⟨outside, houtside⟩ := houtside
  apply top_unique
  intro member _
  by_cases hmember : member ∈ proper
  · have hproductOutside : outside * member ∉ proper := by
      intro hproduct
      have houtsideMem := proper.mul_mem hproduct (proper.inv_mem hmember)
      exact houtside (by simpa only [mul_inv_cancel_right] using houtsideMem)
    have hmem := containing.mul_mem (containing.inv_mem (hcomplement outside houtside))
      (hcomplement (outside * member) hproductOutside)
    simpa only [inv_mul_cancel_left] using hmem
  · exact hcomplement member hmember

end CFSG.ComponentClassification.BlockFactorInvolutions
