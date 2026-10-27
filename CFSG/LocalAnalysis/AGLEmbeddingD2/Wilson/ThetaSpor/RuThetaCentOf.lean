module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.SporThetaCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThree

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

theorem thetaCentOf_ru :
    Coordinator.ThetaCentOf .Ru := by
  intro X _ _ ⟨e⟩ b hb3 hb1
  exact thetaCent_of_ru e b hb3 hb1

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
