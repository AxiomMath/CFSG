module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.U3.Main

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.AGLEmbeddingD2.McLaughlin.OddIndex TauCeti

theorem kFactOvergroupU3 : KFactOvergroupU3 := by
  intro K _ _ d q hq hd ⟨e⟩
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 q.p q.exponent := by
    have := statedClassicalModel_of_lieModel' (by omega)
      (CFSG.Models.lieModel_twistedA 2 q hv e)
    rwa [hc, hf] at this
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  obtain ⟨F, _, _, _, _, hF, ⟨e'⟩⟩ := exists_mulEquiv_SU3 hmodel (hcard ▸ hq)
  exact L3.overgroupOddIndex_of_mulEquiv e' (U3.overgroupOddIndex_SU3 hF (hcard ▸ hq))

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
