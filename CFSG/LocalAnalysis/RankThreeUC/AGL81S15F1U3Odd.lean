module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3B

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open CFSG.Assembly.LowTwoRank CFSG.Models TauCeti CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

section U3OddFamily


theorem f1U3Odd_proved : F1U3Odd := by
  intro K _ _ d q hp2 hq3 hd ⟨e⟩
  obtain ⟨d1, hv⟩ := d
  simp only at hd
  subst hd
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_twistedA 2 q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_twistedA 2 q
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 q.p q.exponent := by
    have := statedClassicalModel_of_lieModel' (by omega) (lieModel_twistedA 2 q hv e)
    rwa [hc, hf] at this
  have hq : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq3' : (q.p ^ q.exponent) % 3 = 1 := hq ▸ hq3
  obtain ⟨F, _, _, _, _, hF, ⟨e'⟩⟩ := exists_mulEquiv_SU3 hmodel hq3'
  refine f1For_of_core e' ?_
  have hodd : (q.p ^ q.exponent) % 2 = 1 := by
    have : Odd q.p := (Fact.out : q.p.Prime).eq_two_or_odd'.resolve_left hp2
    exact Nat.odd_iff.1 this.pow
  by_cases h4 : (q.p ^ q.exponent) % 4 = 1
  · exact f1Core_SU3_of_mod4_one hF hq3' h4
  · exact f1Core_SU3_of_mod4_three hF hp2 hq3' (by omega)

end U3OddFamily

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
