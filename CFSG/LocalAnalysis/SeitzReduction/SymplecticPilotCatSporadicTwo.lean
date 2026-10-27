module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSp4
public import CFSG.Sporadic.ThSchreier.ThSchreierCase

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeaf (MonsterInnerInput MonsterLocalComponentsInput)

theorem sp2mSporadicResidual_two_iff {f : ℕ} {s : TauCeti.SporadicName} :
    sp2mSporadicResidual 2 f s ↔
      (f = 2 ∧ (s = .He ∨ s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B)) ∨
        (f = 3 ∧ (s = .Co1 ∨ s = .Th ∨ s = .Fi24Prime ∨ s = .B)) := by
  unfold sp2mSporadicResidual
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · exact h
    all_goals omega
  · exact fun h => .inl ⟨rfl, h⟩

section Residual

theorem catSp2mSporadicResidual_two : CatSp2mSporadicResidual 2 := by
  intro S _ _ hS hna s ⟨e⟩ σ hσ f D hD hDm hcase hr
  rcases sp2mSporadicResidual_two_iff.mp hr with ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · rcases hs with rfl | rfl | rfl | rfl
    · exact SporadicRefine.sp4_false_of_he hS hna e hσ hD hDm hcase
    · exact SporadicRefine.sp4_false_of_fi23 hS hna e hσ (.inl rfl) hD hDm
    · exact SporadicRefine.sp4_false_of_fi24 hS hna e hσ (.inl rfl) hD hDm
    · exact SporadicRefine.sp4_false_of_baby hS hna e hσ (.inl rfl) hD hDm
  · rcases hs with rfl | rfl | rfl | rfl
    · exact SporadicRefine.sp4_false_of_co1 hS hna e hσ (.inr rfl) hD hDm
    ·
      have hinn : σ ∈ ComponentClassification.OuterAutomorphisms.inner S := by
        rw [(Sporadic.ThSchreier.ctuc_Th_full_automorphism_group.2 S ⟨e⟩).1]
        exact Subgroup.mem_top σ
      obtain ⟨u, rfl⟩ := hinn
      have hB := ComponentClassification.CatLeaf.isComponent_map_mulEquiv
        (MulEquiv.subgroupCongr (F4Pilot.fixedSubgroup_conj u)) hD
      exact ComponentClassification.RestrictedStd.Spor.compsSatisfy_of_charP
        ((Sporadic.ThSchreier.ctuc_Th_inner_involution_centralizers_characteristic_two.2.2 S
          ⟨e⟩).1 u (OmegaPilot.orderOf_eq_two_of_conj hS hna hσ)).1
        (fun (_ : Type) [Group _] => False) _ hB
    · exact SporadicRefine.sp4_false_of_fi24 hS hna e hσ (.inr rfl) hD hDm
    · exact SporadicRefine.sp4_false_of_baby hS hna e hσ (.inr rfl) hD hDm

end Residual

end CFSG.SeitzReduction.SymplecticPilot
