module

public import CFSG.Assembly.OpenBridges
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Open.RankThreeDefs
public import CFSG.Open.UniquenessCaseRankThreeMilestoneDefs

public section

namespace CFSG.Assembly.RankThreeEven

theorem aschCoreLocal_iff_rankThreeAschCoreLocal (G : Type*) [Group G] [Finite G] (k : ℕ) :
    AschCoreLocal G k ↔ CFSG.Open.rankThreeAschCoreLocal G k :=
  Iff.rfl

theorem rankThreeUC_iff_uniqueThreeUC (G : Type*) [Group G] [Finite G] :
    CFSG.Open.rankThreeUC G ↔ CFSG.Open.uniqueThreeUC G :=
  Iff.rfl

theorem core_uniqueness_exclusion_of_theorem_c_of_uniqueness_case
    (hC : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        CFSG.Open.evenRank G = 3 → CFSG.Open.rankThreeAschCoreLocal G 2 →
          CFSG.Open.rankThreeUC G)
    (hUC : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G],
      (∃ a b : G, a * b ≠ b * a) → CFSG.Open.IsKProper G → CFSG.Open.IsCharTwoType G →
        CFSG.Open.evenRank G = 3 → ¬ CFSG.Open.uniqueThreeUC G)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (he : CFSG.Assembly.evenRank G = 3) :
    ¬ AschCoreLocal G 2 := by
  intro hpre
  have hK' := (kProper_inCatalog_iff_isKProper G).1 hK
  have hchar' := (isCharTwoType_iff_open G).1 hchar
  have he' : CFSG.Open.evenRank G = 3 := (evenRank_eq_open G).symm.trans he
  exact hUC G hnonab hK' hchar' he' ((rankThreeUC_iff_uniqueThreeUC G).1
    (hC G hnonab hK' hchar' he' ((aschCoreLocal_iff_rankThreeAschCoreLocal G 2).1 hpre)))

end CFSG.Assembly.RankThreeEven
