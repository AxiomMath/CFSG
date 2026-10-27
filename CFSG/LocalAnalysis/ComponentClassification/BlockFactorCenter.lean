module

public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentClassification.MappedCenter

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockFactorCenter

theorem generated {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component)
    (factor : Subgroup G) (hfactor : factor ∈ UniversalOrbitBlock.block component) :
    (Subgroup.center factor).map factor.subtype ≤ (Subgroup.center (UniversalOrbitBlock.generated component)).map
      (UniversalOrbitBlock.generated component).subtype := by
  have hcontained : (Subgroup.center factor).map factor.subtype ≤ UniversalOrbitBlock.generated component :=
    (MappedCenter.contained factor).trans (CommutingComponentFamily.factor_le _ factor hfactor)
  have hcentralizes : UniversalOrbitBlock.generated component ≤
      Subgroup.centralizer ((Subgroup.center factor).map factor.subtype : Set G) := by
    apply sSup_le
    intro other hother
    by_cases heq : other = factor
    · subst other
      exact Subgroup.le_centralizer_iff.mp (MappedCenter.centralizes factor)
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (UniversalOrbitBlock.block_commutes component heven huniversal other hother factor hfactor heq)).trans
          (Subgroup.centralizer_le (MappedCenter.contained factor))
  intro member hmember
  refine Subgroup.mem_map.mpr ⟨⟨member, hcontained hmember⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcentralizes other.property) member hmember).symm

end CFSG.ComponentClassification.BlockFactorCenter
