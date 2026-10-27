module

public import CFSG.ClassicalInvolution.Asc77.AscC25J4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25J

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V CFSG.ClassicalInvolution.Asc77.C25H
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Final

variable {p f : ℕ} [Fact p.Prime]


theorem nstar9_of_typed9 (h11 : C25_11 p f) (hT : Typed9 p f) (h9 : p ^ f = 9) : NStar p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ t' h hg hnf hat
  obtain ⟨hp3, hf2⟩ := eq_three_two_of_pow_eq_nine (Fact.out : p.Prime) h9
  have h3 : 3 ≤ p ^ (f / 2) := by
    rw [hp3, hf2]
    norm_num
  obtain ⟨hzA, ht'a, hzX, a₀, b₀, T, hcases⟩ :=
    hT h9 G Ω K K' W S R R' z t u₁ u₂ t' h a haS ha2 hFa' hat
  exfalso
  rcases hcases with hz | h5' | h6'
  · exact hZ hz
  · exact false_of_omega5_9 h11 h haS ha2 hFa hFa' h3 hzA ht'a hzX T h5'
  · exact false_of_omega6_9 h haS ha2 hFa' hzA ht'a hzX T h6'


theorem c25_16invEven_of_typed9 (h11 : C25_11 p f) (hT : Typed9 p f) :
    Even f → T7U.C25_16inv p f :=
  C25I.c25_16invEven_typed h11 (nstar9_of_typed9 h11 hT)

end Final

end CFSG.ClassicalInvolution.Asc77.C25J
