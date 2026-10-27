module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerC3D4
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

theorem KD264Y1TwistedD4Model_holds : KD264Y1TwistedD4Model := by
  intro d q hq
  obtain ⟨d, hd⟩ := d
  have hq' : d = .twistedD 4 q := hq
  subst hq'
  rcases (CFSG.Models.lieModel_twistedD (G := (CFSGIndex.lie ⟨.twistedD 4 q, hd⟩).Group)
    4 q hd (MulEquiv.refl _)).2 with h | ⟨h0, _⟩
  · exact h
  · exact absurd h0 (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
