module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SplitExc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMaxOrbits
public import CFSG.Sporadic.Bridge.Fi22Surj

public section

namespace CFSG.AGLEmbedding.KFactProofs.Fi22Five

open CFSG.Monster.B.Fischer

theorem coreData_fi22P :
    CoreData fi22P := by
  obtain ⟨x, y, hx, hy, hD, hN⟩ := orbit_part
  obtain ⟨G₁, G₂, h₁, h₂, hG₁, hG₂⟩ := gen_part hx hy hD
  refine ⟨⟨x, y, 2582470066176, Subgroup.closure ({G₁, G₂} : Set fi22P),
    ⟨hD, hN, star5_part hx hy hD, closure_maximal h₁ h₂, ?_⟩, ?_, by norm_num⟩⟩
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hG₁, hG₂]
  · rw [card_fi22P]
    norm_num

end CFSG.AGLEmbedding.KFactProofs.Fi22Five

namespace CFSG.AGLEmbedding

theorem kFactUPrimeExcFi22 :
    KFactUPrimeExcFi22 := by
  intro K _ _ p hp T hT
  obtain ⟨rfl, ⟨φ⟩⟩ := hp
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact ((KFactProofs.Fi22Five.coreData_fi22P.of_mulEquiv
    ((φ.trans β.symm).trans CFSG.Monster.B.Fischer.fi22PermEquiv).symm).uPrime T hT)

end CFSG.AGLEmbedding
