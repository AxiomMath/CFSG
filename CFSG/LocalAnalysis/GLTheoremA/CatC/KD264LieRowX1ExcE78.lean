module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcMax
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Parts
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section Index


theorem kd264X1At_E7 (hmax : ExcMaxRank Tag.E7 e7Neg) (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hd : d.1 = .E7 q) [Finite (TauCeti.CFSGIndex.lie d).Group] :
    KD264X1At d := by
  intro _ _ _ h4 _ _
  obtain ⟨x, hx⟩ := d
  obtain rfl : x = .E7 q := hd
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e7 q hx
  have hK2 : Nat.card K = 2 := hK.trans hq
  exact exc_conclusion 2 (Or.inl ⟨rfl, rfl⟩) e7Neg e7Neg_smul e7U e7V (by decide +kernel)
    (fun L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor => e7_good_pair S hq2 hAlg hρ hζ hζ' hTor) hmax K hK2
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 K).1
    (mulAut_mem_range_conj_E78 (Or.inl rfl) K hK2) e

theorem kd264X1At_E8 (hmax : ExcMaxRank Tag.E8 e8Neg) (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hd : d.1 = .E8 q) [Finite (TauCeti.CFSGIndex.lie d).Group] :
    KD264X1At d := by
  intro _ _ _ h4 _ _
  obtain ⟨x, hx⟩ := d
  obtain rfl : x = .E8 q := hd
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hx
  have hK2 : Nat.card K = 2 := hK.trans hq
  exact exc_conclusion 1 (Or.inr ⟨rfl, rfl⟩) e8Neg e8Neg_smul e8U e8V (by decide +kernel)
    (fun L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor => e8_good_pair S hq2 hAlg hρ hζ hζ' hTor) hmax K hK2
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_e8 K).1
    (mulAut_mem_range_conj_E78 (Or.inr rfl) K hK2) e

theorem kd264X1At_E7_holds (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .E7 q) [Finite (TauCeti.CFSGIndex.lie d).Group] : KD264X1At d :=
  kd264X1At_E7 exc_maxRank_E7 d q hd

theorem kd264X1At_E8_holds (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .E8 q) [Finite (TauCeti.CFSGIndex.lie d).Group] : KD264X1At d :=
  kd264X1At_E8 exc_maxRank_E8 d q hd

end Index

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc

end
