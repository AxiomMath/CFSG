module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallFinal
public import CFSG.ClassicalInvolution.RouteD.SmallBWired

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT

variable {p f : ℕ} [Fact p.Prime]

@[expose] def TwinTDCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  Gaps.TwinTDPatternOn p f fun k => k = m

theorem twinTDSmallPattern7_of_cases (h4 : TwinTDCase p f 4) (h5 : TwinTDCase p f 5)
    (h6 : TwinTDCase p f 6) (h7 : TwinTDCase p f 7) : Gaps.TwinTDSmallPattern7 p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  obtain ⟨hm4, hm7⟩ := hm
  have key : ∀ k : ℕ, TwinTDCase p f k → m = k → PartnerPatternMinus p f m (conjClass K) K β t :=
    fun k hk hmk => hk G hnab K z S m hmk hshape β hβ t ht hKβ hfix
  rcases (by omega : m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) with h | h | h | h
  · exact key 4 h4 h
  · exact key 5 h5 h
  · exact key 6 h6 h
  · exact key 7 h7 h

@[expose] def TwinBCase (p f m : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), CoreAssembly.RouteDSetup p f K z →
      LocalShapeT p f 2 .POmegaOdd m (conjClass K) z →
      ∀ β ∈ conjClass K, ∀ t : G, IsClassicalMember p f β t →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W K β) →
        HasFixedMember (conjClass K) K β z → PartnerPatternBPair p f m (conjClass K) K β t

theorem twinBSmallRest_of_cases (h3 : TwinBCase p f 3) (h4 : TwinBCase p f 4)
    (h6 : TwinBCase p f 6) : TwinBSmallRest p f := by
  intro G _ _ _ hnab K z S m hm hshape β hβ t ht hKβ hfix
  rcases hm with rfl | rfl | rfl
  · exact h3 G hnab K z S hshape β hβ t ht hKβ hfix
  · exact h4 G hnab K z S hshape β hβ t ht hKβ hfix
  · exact h6 G hnab K z S hshape β hβ t ht hKβ hfix

end CFSG.ClassicalInvolution.RouteD
