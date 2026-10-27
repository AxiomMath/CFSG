module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBData
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th
open CFSG.Sporadic.Fi24 (R J tR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


@[expose] noncomputable def fi24QElt (e : List ℤ × ℕ) : J :=
  (wordG (fun z => if z = 1 then fi24Ca else fi24Cb) e.1) ^ e.2

@[expose] def TwoBJFacts : Prop :=
  (∀ x : Equiv.Perm (Fin 504),
      (∀ j : Fin 504, idx 306936 tR fi24FPts[j.val]! = fi24FPts[(x j).val]!) → x ∉ fi24K) ∧
    ∃ e ∈ fi24QWords.tail,
      fi24QElt fi24QWords[0]! * fi24QElt e ≠ fi24QElt e * fi24QElt fi24QWords[0]!

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

end
