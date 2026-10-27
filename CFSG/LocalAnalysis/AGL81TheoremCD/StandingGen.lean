module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open

structure StandingGen (G : Type) [Group G] [Finite G] : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : IsKProper G
  charTwo : IsCharTwoType G
  rank : 3 ≤ evenRank G

end CFSG.LocalAnalysis.AGL81TheoremCD
