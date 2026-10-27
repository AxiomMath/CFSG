module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Graph
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

structure LinesThrough (a z : G) : Prop where
  two_B : ∀ x ∈ orb2B a z a, ∃ y ∈ orb2A a a, x * y ∈ orb2A a a
  four_B : ∀ x ∈ orb4B a a, ∃ y ∈ orb3A a a, x * y ∈ orb3A a a
  five_A : ∀ x ∈ orb5A a a, ∃ y ∈ orb4B a a, x * y ∈ orb6A a a
  five_E : ∀ x ∈ orb5E a a, ∃ y ∈ orb4B a a, x * y ∈ orb6A a a
  four_A : ∀ x ∈ orb4A a z a, ∃ y ∈ orb4B a a, x * y ∈ orb4B a a

@[expose] def PerpThreeA (a : G) : Prop :=
  ∀ x ∈ orb3A a a, gammaPerp a (orb2A a a ∩ orb2A a x) ⊆ {a, x, a * x * a}

@[expose] def OutIndex (a : G) : Prop :=
  (MulAut.conj : ↥(Gx a) →* MulAut ↥(Gx a)).range.index ≤ 2

structure SegevInputs (a z : G) : Prop where
  lines : LinesThrough a z
  perp : PerpThreeA a
  out : OutIndex a

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
