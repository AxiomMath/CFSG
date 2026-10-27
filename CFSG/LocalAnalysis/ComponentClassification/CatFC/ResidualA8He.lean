module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.ResidualA8Gen
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC.ResidualA8

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section He


theorem heD_not_equiv_alt_eight :
    ¬ Nonempty (↥(genGroup 105 heDGens heDPerm) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨-, hDcard, -, -⟩ := heD_facts
  refine not_equiv_alt_eight_of_classes (classEquivS tabRep_heDGens heD_cert)
    (fun l => heDClassSizes.getD l 0) (card_classS tabRep_heDGens heD_cert) ⟨0, by norm_num⟩
    (classEquivS_zero tabRep_heDGens heD_cert (by norm_num)) ?_
  intro l hl
  rw [hDcard]
  revert l
  decide

theorem noAltEightComponent_heInnerGrp0 : NoAltEightComponent heInnerGrp0 := by
  obtain ⟨⟨hDs, hDnab⟩, hDcard, hDle, hDi⟩ := heD_facts
  have hker : Group.IsSolvable heRho0.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 heRho0.ker := IsPGroup.of_card (n := 2) (by rw [card_heRho0_ker]; norm_num)
    have : Group.IsNilpotent heRho0.ker := hp.isNilpotent
    infer_instance
  let eD : (genGroup 105 heDGens heDPerm).subgroupOf heRho0.range ≃* genGroup 105 heDGens heDPerm :=
    subgroupOfEquivOfLe hDle
  have hs : IsSimpleGroup ((genGroup 105 heDGens heDPerm).subgroupOf heRho0.range) :=
    eD.isSimpleGroup
  have hnc : ∃ a b : (genGroup 105 heDGens heDPerm).subgroupOf heRho0.range, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hDnab
    refine ⟨eD.symm a, eD.symm b, fun h => hab ?_⟩
    have := congrArg eD h
    simpa using this
  refine NoAltEightComponent.of_surjective_simple heRho0.rangeRestrict
    heRho0.rangeRestrict_surjective hker _ hDi hs hnc ?_
  rintro ⟨φ⟩
  exact heD_not_equiv_alt_eight ⟨eD.symm.trans φ⟩

theorem noAltEightComponent_he_fixed {S : Type} [Group S] (e : S ≃* NativeSporadic.He) {s : S}
    (hs : orderOf s = 2) : NoAltEightComponent (fixedSubgroup (MulAut.conj s)) := by
  rcases SeitzReduction.SporadicRefine.he_inner_fixedSubgroup_cases e s hs with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact NoAltEightComponent.of_mulEquiv φ noAltEightComponent_heInnerGrp0
  · exact NoAltEightComponent.of_mulEquiv φ
      (NoAltEightComponent.of_no_component fun B hB => heC1_no_component B hB)

end He

end CFSG.ComponentClassification.CatFC.ResidualA8
