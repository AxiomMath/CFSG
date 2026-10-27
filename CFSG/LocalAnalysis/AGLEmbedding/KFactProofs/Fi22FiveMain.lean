module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallFiKCKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveOrbit
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveStar
public import CFSG.Sporadic.Bridge.Fi22Surj

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Fischer

theorem fiveData_fi22P :
    FiveData fi22P := by
  obtain ⟨x, y, hx, hy, hD, hN⟩ := orbit_part
  refine ⟨⟨x, y, 2582470066176, hD, ?_, by norm_num, hN, star_part hx hy hD⟩⟩
  rw [card_fi22P]
  norm_num

end CFSG.AGLEmbedding.KFactProofs.Fi22Five

namespace CFSG.AGLEmbedding

theorem kFactFi22Orbits :
    KFactFi22Orbits := by
  intro K _ _ hK T O hO hinv
  obtain ⟨φ⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact (KFactProofs.Fi22Five.fiveData_fi22P.of_mulEquiv
    ((φ.trans β.symm).trans CFSG.Monster.B.Fischer.fi22PermEquiv).symm).orbits T O hO hinv

theorem kFactFi22NoTwo :
    KFactFi22NoTwo := by
  intro K _ _ hK S U hU hSU
  obtain ⟨φ⟩ := hK
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact (KFactProofs.Fi22Five.fiveData_fi22P.of_mulEquiv
    ((φ.trans β.symm).trans CFSG.Monster.B.Fischer.fi22PermEquiv).symm).noTwo S U hU hSU

end CFSG.AGLEmbedding
