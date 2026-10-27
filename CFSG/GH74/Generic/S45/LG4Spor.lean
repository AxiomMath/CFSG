module

public import CFSG.GH74.Generic.S45.LG4Defs
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporInputs

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.ComponentClassification.RestrictedStd.Spor (LyOuterTrivialInput)

theorem sporRowG_of_sporadic {s : TauCeti.SporadicName} (h : CFSG.GH74.Filter.S_sporadic s) :
    SporRowG s := by
  intro K _ _ y L hyp hS
  obtain ⟨hg, hyp⟩ := hyp
  have hnab : ∃ a b : K ⧸ center K, a * b ≠ b * a := hyp.1.1.2.2
  exact h (K ⧸ center K) hnab hS (Gen4.quotient _ hg)

theorem sporRowG_of_out :
    ∀ s ∈ CFSG.GH74.Filter.sporadicOut, SporRowG s :=
  fun s hs => sporRowG_of_sporadic (CFSG.GH74.Filter.t_sporadic_all CFSG.GH74.Filter.t_sporadic_M s hs)

end CFSG.GH74.Generic.S45
