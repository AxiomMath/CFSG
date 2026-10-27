module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockIbDefs
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.HBRTwistedA
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.HBATwistedA
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.RankTwoTwistedA

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.AGLEmbedding

section TwistedA


theorem blockIbRankFam_twistedA : BlockIbRankFam (IsLieOf IdxTwistedA) := by
  intro Y _ _ Lb Pb D x hP hX hD E hEL hEP hED hEab hE9 t ht htE htF
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedA r q =>
    have hd' : q.p = 2 := hd
    have hr : 2 ≤ r := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · exact hBR_twistedA_rank_two hP.comp hP.odd hP.parab hP.ne r (by omega) q hv hd' _ rfl e
        hD.rank hD.cyc hD.Dperf hD.Dle hD.hx hD.hx3 hD.hxC hD.free E hEL hEP hED hEab hE9 t ht htE
        htF
    · exact hBR_twistedA hP.comp hP.odd hP.parab hP.ne r h3 q hv hd' _ rfl e
        hD.rank hD.cyc hD.Dperf hD.Dle hD.hx hD.hx3 hD.hxC hD.free E hEL hEP hED hEab hE9 t ht htE
        htF
  | _ => exact hd.elim

theorem blockIbAbFam_twistedA : BlockIbAbFam (IsLieOf IdxTwistedA) := by
  intro Y _ _ Lb Pb D x hP hX hD U hUL hUP hUD hU3
  obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hX
  cases d with
  | twistedA r q =>
    have hd' : q.p = 2 := hd
    have hr : 2 ≤ r := TauCeti.LieTypeIndex.two_le_of_twistedA_inStandardRange ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    rcases Nat.lt_or_ge r 3 with h3 | h3
    · exact hBA_twistedA_rank_two hP.comp hP.odd hP.parab hP.ne r (by omega) q hv hd' _ rfl e
        hD.rank hD.cyc hD.Dperf hD.Dle hD.hx hD.hx3 hD.hxC hD.free U hUL hUP hUD hU3
    · exact hBA_twistedA hP.comp hP.odd hP.parab hP.ne r h3 q hv hd' _ rfl e
        hD.rank hD.cyc hD.Dperf hD.Dle hD.hx hD.hx3 hD.hxC hD.free U hUL hUP hUD hU3
  | _ => exact hd.elim

end TwistedA

end CFSG.HardMathSupport.Curtis.UnitaryLevi
