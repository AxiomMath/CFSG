module

public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.RankThreeUC.SubgroupCentralizerQuotientRank

variable {G : Type} [Group G]

theorem pRank_quotient_le {X M V : Subgroup G} (hXM : X ≤ M)
    [(centralizerInSubgroup X V).Normal] [(centralizerInSubgroup M V).Normal] {p : ℕ}
    (hp : 1 < p) [Finite G] :
    CFSG.pRank p (X ⧸ centralizerInSubgroup X V) ≤
      CFSG.pRank p (M ⧸ centralizerInSubgroup M V) := by
  have centralizerInSubgroup_le_comap {X M V : Subgroup G} (hXM : X ≤ M) :
      centralizerInSubgroup X V ≤ (centralizerInSubgroup M V).comap (Subgroup.inclusion hXM) := by
    intro x hx
    exact hx
  let quotientMap {X M V : Subgroup G} (hXM : X ≤ M) [(centralizerInSubgroup X V).Normal]
      [(centralizerInSubgroup M V).Normal] :
      X ⧸ centralizerInSubgroup X V →* M ⧸ centralizerInSubgroup M V :=
    QuotientGroup.map _ _ (Subgroup.inclusion hXM) (centralizerInSubgroup_le_comap hXM)
  have quotientMap_injective {X M V : Subgroup G} (hXM : X ≤ M)
      [(centralizerInSubgroup X V).Normal] [(centralizerInSubgroup M V).Normal] :
      Function.Injective (quotientMap (V := V) hXM) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [QuotientGroup.eq_one_iff]
      have : (Subgroup.inclusion hXM x) ∈ centralizerInSubgroup M V := by
        have := hq
        simpa [quotientMap, QuotientGroup.eq_one_iff] using this
      exact this
  have := CFSG.SectionRank.pRank_top_le_of_injective hp (quotientMap (V := V) hXM)
    (quotientMap_injective hXM)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact this

end CFSG.LocalAnalysis.RankThreeUC.SubgroupCentralizerQuotientRank
