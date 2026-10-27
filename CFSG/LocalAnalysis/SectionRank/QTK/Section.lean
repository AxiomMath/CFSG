module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.LocalAnalysis.SectionRank.QTK.SectionLiftB
import CFSG.RankThree.PartTwo.Setup
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.SectionRank.QTK

open Subgroup

@[expose] def QTCentreFact : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → CFSG.SectionRank.IsKGroupCat K →
    CFSG.Open.evenRank K ≤ 2 → ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ Nat.card (center K) →
      ∀ R : Subgroup (K ⧸ center K), R ≠ ⊥ → IsPGroup 2 R →
        CFSG.Open.pRank r (normalizer (R : Set (K ⧸ center K))) ≤ 2

variable {G : Type} [Group G] [Finite G]

theorem evenRank_subgroup_le_evenRank (K : Subgroup G) :
    CFSG.Open.evenRank K ≤ CFSG.Open.evenRank G :=
  CFSG.RankThree.PartTwo.evenRank_subgroup_le K

theorem evenRank_center_quotient_le_two (hC : QTCentreFact) (he : CFSG.Open.evenRank G ≤ 2)
    {K : Subgroup G} (hq : CFSG.IsQuasisimple K) (hK : CFSG.SectionRank.IsKGroupCat K) :
    CFSG.Open.evenRank (↥K ⧸ center ↥K) ≤ 2 := by
  refine csSup_le' ?_
  rintro _ ⟨p, H, hp, hp2, ⟨R, hR, hR2, rfl⟩, rfl⟩
  by_cases hpZ : p ∣ Nat.card (center ↥K)
  · exact hC K hq hK ((evenRank_subgroup_le_evenRank K).trans he) p hp hp2 hpZ R hR hR2
  · exact pRank_normalizer_le_two_of_not_dvd he hp hp2 hpZ hR hR2

end CFSG.SectionRank.QTK
