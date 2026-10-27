module

public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneBoundExtension
public import CFSG.CharacterTheory.Semidihedral.ParameterFiveCoreThree
public import CFSG.CharacterTheory.Semidihedral.ParameterFiveUnitary
public import CFSG.CharacterTheory.Semidihedral.SimpleLayerFrontierGaps

public section

namespace CFSG.Semidihedral.ParameterFive

theorem parameterFiveRecognition_of
    (hext : ExtensionOfOrderBoundStatement) :
    SimpleLayerFrontier.ParameterFiveRecognitionStatement := by
  intro G _ _ _ hGnonab n hn S fS t ht _ hnonab hcentral hnc hmodel
  exact statedClassicalModel_psu_of_card_oddCore_eq_one hGnonab n hn S fS t ht hnonab hcentral
    hnc hmodel
    (card_oddCore_eq_one_of_extension hext hGnonab n hn S fS t ht hnonab hcentral hnc hmodel)

theorem parameterFiveRecognition
    : SimpleLayerFrontier.ParameterFiveRecognitionStatement :=
  parameterFiveRecognition_of FieldFactorOne.centralizer_linear_character_extends_of_order_bound

end CFSG.Semidihedral.ParameterFive
