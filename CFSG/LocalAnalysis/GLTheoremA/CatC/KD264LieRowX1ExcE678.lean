module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcE78
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcE6
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley


theorem kd264X1At_E6_holds (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .E6 q) [Finite (TauCeti.CFSGIndex.lie d).Group] : KD264X1At d := by
  intro _ _ _ h4 _ _
  obtain ⟨x, hx⟩ := d
  obtain rfl : x = .E6 q := hd
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hx
  have hK2 : Nat.card K = 2 := hK.trans hq
  haveI := charP_two_of_card_two' hK2
  exact E6.e6_conclusion hK2 e

theorem kd264X1ExcE678_holds : KD264X1ExcE678 := by
  intro d q hd _
  rcases hd with h | h | h
  · exact kd264X1At_E6_holds d q h
  · exact kd264X1At_E7_holds d q h
  · exact kd264X1At_E8_holds d q h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
