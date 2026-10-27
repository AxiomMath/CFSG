module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearQuotient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearGenerated
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Statement

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem caseIJankoConfiguration_of_linear
    (hL : CaseILinear) : CaseIJankoConfiguration := by
  intro G _ _ S H z hset hz hesc ⟨J, hJ, hzJ⟩
  obtain ⟨n, hn, ⟨e⟩⟩ := hL G S H z hset hz hesc J hJ hzJ
  obtain ⟨D, hlin⟩ := exists_linearSylowData hset hz hesc hJ hzJ hn e
  have hn2 := caseOne_linear_eq_two hset hz hesc hJ hzJ hn e
  have htrans := caseOne_sylow_transitive hset hz hesc hJ hzJ hlin
  refine ⟨caseOne_sylow_comm hset hz hesc hJ hzJ hlin, caseOne_sylow_sq hset hz hesc hJ hzJ hlin,
    ?_, htrans, ?_, caseOne_generated_eq_top hset hz hesc hJ hzJ htrans⟩
  · rw [caseOne_card_sylow hset hz hesc hJ hzJ hlin, hn2]
    norm_num
  · exact ⟨J, caseOne_component_normal hset hz hesc hJ hzJ,
      caseOne_component_alternatingGroup hset hz hesc hJ hzJ hn e, hzJ,
      caseOne_component_sup_zpowers_eq_top hset hz hesc hJ hzJ hn e⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
