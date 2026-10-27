module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.SporThetaCent
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThree

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open CFSG.AGLEmbeddingD2.Wilson

theorem thetaCentOf_he :
    CFSG.AGLEmbeddingD2.Wilson.Coordinator.ThetaCentOf .He := by
  intro X _ _ ⟨e⟩ b hb3 hb1
  let e' : X ≃* Blueprint.NativeSporadic.He := e
  have hb3' : (e' b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hb1' : e' b ≠ 1 := fun h => hb1 (e'.injective (h.trans (map_one e').symm))
  have h := ThetaSpor.He.thetaCent_he (e' b) hb3' hb1'
  exact (@ThreeCore.aschbacherSolvableCore_three_centralizer_eq_bot_iff _ _ _ Units.instGroup _
    e' b).mpr h

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
