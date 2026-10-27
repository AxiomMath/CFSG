module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBJFacts
public import CFSG.Sporadic.FischerOddCore.Fi24R2Comp
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th
open CFSG.Sporadic.Fi24 (R J tR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem not_mem_fi24K_of_tR
    (h : TwoBJFacts)
    {x : Equiv.Perm (Fin 504)} (hx : ∀ j, fi24FPt (x j) = tR • fi24FPt j) : x ∉ fi24K := by
  refine h.1 x fun j => ?_
  have e := congrArg Fin.val (hx j)
  change idx 306936 tR (fi24FPt j).val = (fi24FPt (x j)).val
  rw [e, idx_of_lt tR (fi24FPt j).isLt]

theorem exists_fi24Q_ne
    (h : TwoBJFacts) :
    ∃ e ∈ fi24QWords.tail,
      fi24QElt fi24QWords[0]! * fi24QElt e ≠ fi24QElt e * fi24QElt fi24QWords[0]! := h.2

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
