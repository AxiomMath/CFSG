module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Stage3Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.BRowFinal
public import CFSG.Sporadic.GLQ.BTwoRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMData
public import CFSG.Sporadic.NativeFinite

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

section Proved

@[expose] def BTwoAPair : Prop :=
  ∃ (u : Carrier .B) (K : Subgroup (Carrier .B)), BPair (Carrier .B) ⊤ K u

theorem bPair_eq : BPair = PairShape (· = 2 * ordTwistedE6 2) := rfl

theorem bPinnedFacts (hf : BabyCoverFacts) :
    PinnedFacts .B (· = 2 * ordTwistedE6 2) (ordTwistedE6 2) monsterBabyOrder where
  finite := CFSG.Sporadic.finite_carrier_of_ne_M .B (by decide)
  simple := b_isSimpleGroup_of_isSporadic (Y := Carrier .B) ⟨MulEquiv.refl _⟩
  nonabelian := b_exists_not_commute (Y := Carrier .B) ⟨MulEquiv.refl _⟩
  card := b_card_of_isSporadic (Y := Carrier .B) ⟨MulEquiv.refl _⟩
  even_card := by unfold monsterBabyOrder; decide
  rank := fun X _ _ h => by
    have := (CFSG.Sporadic.GLQ.b_two_rank_at_least_five X h).2
    omega
  outTwo := outTwo_of_allInner (b_data_of_simple (MulEquiv.refl (Carrier .B))).1
  pair := fun u K hQ => by
    have : Finite (Carrier .B) := CFSG.Sporadic.finite_carrier_of_ne_M .B (by decide)
    obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
    have hcov := hf.cover (Carrier .B) ⊤ K u ⟨Subgroup.topEquiv⟩ ⟨huL, hu2, hKL, hKu, hcard⟩
    have hKC : K ≤ ⊤ ⊓ centralizer ({u} : Set (Carrier .B)) := fun k hk =>
      ⟨mem_top _, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
    refine ⟨?_, hcard⟩
    rw [← card_center_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKC)]
    exact hcov.card_center
  two_le := by unfold ordTwistedE6; norm_num
  even_N := by unfold ordTwistedE6; decide
  lt := by unfold ordTwistedE6 monsterBabyOrder; norm_num
  cube := ⟨53492380, by unfold ordTwistedE6; norm_num, by unfold ordTwistedE6; norm_num⟩
  ne_a7 := by unfold ordTwistedE6; norm_num

end Proved

end CFSG.EvenSporadicStandard.Induction
