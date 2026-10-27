module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.Assembly.OpenBridges
public import CFSG.Open.GLBDefs
public import CFSG.Open.UniquenessExclusionRankFourMilestoneDefs

public section

namespace CFSG.Assembly.LargeEven

theorem largeEvenBeta_four_eq_glbBetaFour (G : Type*) [Group G] [Finite G] :
    LargeEvenBeta 4 G = CFSG.Open.GLBBetaFour G :=
  rfl

theorem largeEvenWeakCoreLocal_iff_glbWeakCoreLocal (G : Type*) [Group G] [Finite G] (p : ℕ) :
    LargeEvenWeakCoreLocal G p ↔ CFSG.Open.GLBWeakCoreLocal G p :=
  Iff.rfl

theorem glbUniqueFour_iff_uniqueFourUnique (G : Type*) [Group G] [Finite G] :
    CFSG.Open.GLBUniqueFour G ↔ CFSG.Open.uniqueFourUnique G :=
  Iff.rfl

theorem preuniqueness_exclusion_rank_four_of_theorem_c_of_uniqueness_exclusion
    (hC : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → CFSG.Open.GLBPreuniqueness G → CFSG.Open.GLBUniqueFour G)
    (hUE : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        4 ≤ CFSG.Open.evenRank G → ¬ CFSG.Open.uniqueFourUnique G)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he : 4 ≤ evenRank G) :
    ∃ p ∈ LargeEvenBeta 4 G, ¬ LargeEvenWeakCoreLocal G p := by
  have hK' := (kProper_inCatalog_iff_isKProper G).1 hK
  have hchar' := (isCharTwoType_iff_open G).1 hchar
  have he' : 4 ≤ CFSG.Open.evenRank G := he.trans_eq (evenRank_eq_open G)
  by_contra! hall
  refine hUE G hnonab hK' hchar' he' ((glbUniqueFour_iff_uniqueFourUnique G).1
    (hC G hnonab hK' hchar' he' fun p hp => ?_))
  rw [← largeEvenBeta_four_eq_glbBetaFour] at hp
  exact (largeEvenWeakCoreLocal_iff_glbWeakCoreLocal G p).1 (hall p hp)

end CFSG.Assembly.LargeEven
