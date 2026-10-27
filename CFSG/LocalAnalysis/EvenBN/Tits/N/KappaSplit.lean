module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56StepKappa

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open CFSG.Sporadic.Schreier.Tits

section Split


@[expose] def StepKappaBitD : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G},
    d.Thm49Statement → d.Hyp → d.ρ.range = titsD.subgroupOf titsA → d.S56KappaBit

@[expose] def StepKappaBitAhat : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {d : Data G},
    d.Thm49Statement → d.Hyp → d.ρ.range = ⊤ → d.S56KappaBit

end Split

section Proof


theorem stepKappaBit_of_split (hD : StepKappaBitD) (hA : StepKappaBitAhat) : StepKappaBit := by
  intro G _ _ d h49 hd
  rcases hd.range_ρ with h | h
  · exact hD h49 hd h
  · exact hA h49 hd h

end Proof

end CFSG.LocalAnalysis.EvenBN.Tits.N
