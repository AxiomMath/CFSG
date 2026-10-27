module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueEvenExceptional
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6OuterInvolutionOddCore

public section

namespace CFSG.ComponentClassification.CatalogueU

theorem evenE6OuterInvolutionInput_holds : EvenE6OuterInvolutionInput :=
  ⟨fun _ hf k _ hk H hIH α hαH hαI hα =>
      (RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core hf).1
        k hk H hIH α hαH hαI hα,
    fun _ hf K _ _ hK σ hσ H hIH α hαH hαI hα =>
      (RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core hf).2
        K hK σ.toRingHom hσ H hIH α hαH hαI hα⟩

theorem evenExceptionalCheck : EvenExceptionalCheck :=
  evenExceptionalCheck_of_E6Outer evenE6OuterInvolutionInput_holds

end CFSG.ComponentClassification.CatalogueU
