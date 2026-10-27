module

public import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoDefs
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoUThree
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoU
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoSp
import CFSG.LocalAnalysis.AGLEmbedding.ThreeCentLieTwoO
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem threeAutFixedTwoThree_lie_twistedD_two (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ d.1 = .twistedD r q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp2, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_two hq
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp2
    (MulEquiv.refl _)
  rw [hp2, hf] at h
  exact threeAutFixedTwoThree_of_model_pomegaMinus_two h

theorem threeAutFixedTwoThree_lie_D_two_of (hD4 : KFactThreeCentTrialityTwo)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ (r : ℕ) (q : TauCeti.PrimePower), q.card = 2 ∧ d.1 = .D r q) :
    ThreeAutFixedTwoThree (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  obtain ⟨r, q, hq, hd⟩ := hd
  simp only at hd
  subst hd
  obtain ⟨hp2, hf⟩ := ParabHub.primePower_eq_of_card_eq Nat.prime_two hq
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp2
    (MulEquiv.refl _)
  rw [hp2, hf] at h
  have hr4 : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
  · obtain ⟨hZ, hkey⟩ := center_eq_bot_and_innerKey_of_model_pomegaPlus_two h
    exact threeAutFixedTwoThree_of_inner_and_outer hZ hkey
      (hD4 ⟨.D 4 q, hv⟩ ⟨q, hq, rfl⟩)
  · exact threeAutFixedTwoThree_of_model_pomegaPlus_two h hr5

theorem kFactThreeCentLieTwo_of (hD4 : KFactThreeCentTrialityTwo) : KFactThreeCentLieTwo := by
  intro d hd
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    rcases hd with hq | ⟨rfl, hq⟩
    · exact threeAutFixedTwoThree_lie_twistedA_two ⟨.twistedA r q, hv⟩ ⟨r, q, hq, rfl⟩
    · exact threeAutFixedTwoThree_lie_twistedA_three ⟨.twistedA 2 q, hv⟩ ⟨q, hq, rfl⟩
  | B r q => exact threeAutFixedTwoThree_lie_B_two ⟨.B r q, hv⟩ ⟨r, q, hd, rfl⟩
  | D r q => exact threeAutFixedTwoThree_lie_D_two_of hD4 ⟨.D r q, hv⟩ ⟨r, q, hd, rfl⟩
  | twistedD r q => exact threeAutFixedTwoThree_lie_twistedD_two ⟨.twistedD r q, hv⟩ ⟨r, q, hd, rfl⟩
  | _ => exact hd.elim

end CFSG.AGLEmbedding
