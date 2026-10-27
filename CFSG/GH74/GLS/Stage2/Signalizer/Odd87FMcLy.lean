module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FMcLyLy
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FMcLyMcL
public import CFSG.Sporadic.Schreier.PairMcLOut

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem cell87_FMcLy
    (hCC : ∀ (Y : Type) [Group Y], NativeSporadic.IsSporadic Y .McL → McLOuterCC Y) :
    Cell87 FMcLy := by
  refine cell87_of_quot (F := FMcLy) ?_ ?_
  · intro Y _ _ hY
    rcases hY with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have h1 : OutAbelian NativeSporadic.McL :=
        outAbelian_of_outer_comm CFSG.Sporadic.Schreier.McL_outer_card_le_two.2.1
      exact outAbelian_of_mulEquiv e.symm h1
    · have h1 : OutAbelian NativeSporadic.Ly := outAbelian_of_inner_top fun φ => by
        obtain ⟨g, hg⟩ := (Subgroup.eq_top_iff' _).mp
          CFSG.ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput φ
        exact ⟨g, hg.symm⟩
      exact outAbelian_of_mulEquiv e.symm h1
  · intro Y _ _ hY p α Xh h
    rcases hY with hMcL | hLy
    · exact noQuotCfg_McL hMcL (hCC Y hMcL) h
    · exact noQuotCfg_Ly hLy h

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
