module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeLie
public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoKill
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKill

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def IsChevTwoInnerIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧
    (d.1 = .B 4 q ∨ d.1 = .twistedA 4 q ∨ d.1 = .twistedA 5 q ∨ d.1 = .D 4 q ∨ d.1 = .F4 q ∨
      d.1 = .E6 q)

@[expose] def IsChevTwoOuterIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .trialityD4 q) ∨
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧
      (d.1 = .trialityD4 q ∨ d.1 = .twistedA 2 q)

@[expose] def KFactChevTwoInnerGen : Prop :=
  ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoInnerIndex d →
    ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
      Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
      ∀ T : Sylow 3 K, GLBWeakCore 3 (T : Subgroup K) = ⊤

@[expose] def KFactChevTwoOuterGen : Prop :=
  (∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoOuterIndex d →
      ∀ S : Sylow 3 (Outer (TauCeti.CFSGIndex.lie d).Group),
        (S : Subgroup (Outer (TauCeti.CFSGIndex.lie d).Group)).Normal) ∧
    ∀ d : TauCeti.ValidLieTypeIndex, IsChevTwoOuterIndex d →
      ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), K.Normal → Open.IsQuasisimple K →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        IsPGroup 3 (Subgroup.centralizer (K : Set X)) →
        (∀ c ∈ Subgroup.centralizer (K : Set X), orderOf c = 3 →
          c ∈ (Subgroup.center K).map K.subtype) →
        ∀ R : Sylow 3 X, 3 ≤ Open.pRank 3 (R : Subgroup X) →
          K ≤ GLBWeakCore 3 (R : Subgroup X)

@[expose] def D1CaseThreeSp62 : Prop :=
  D1CaseThreeLieAt fun p d =>
    p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q

@[expose] def D1CaseThreeSp48 : Prop :=
  D1CaseThreeLieAt fun p d =>
    p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q

@[expose] def D1CaseThreeG28 : Prop :=
  D1CaseThreeLieAt fun p d =>
    p = 3 ∧ ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .G2 q

@[expose] def D1CaseThreeReeF4 : Prop :=
  D1CaseThreeLieAt fun p d => p = 5 ∧ d.1 = .reeF4 2

theorem d1CaseThreeChevTwo_of (hin : KFactChevTwoInnerGen) (hout : KFactChevTwoOuterGen)
    (h62 : D1CaseThreeSp62) (h48 : D1CaseThreeSp48) (hG28 : D1CaseThreeG28)
    (hF4 : D1CaseThreeReeF4) : D1CaseThreeLieAt IsP1ChevTwoIndex := by
  intro G _ _ p _ P M H R Rbar hcfg K hK huniq hnc hcent hKD d hd e
  have hinner : p = 3 → IsChevTwoInnerIndex d → False := by
    rintro rfl hdi
    exact hcfg.false_of_weakCore_eq_top hK huniq (hin d hdi K hK.2.2 e
      (hcfg.isPGroup_center hK) (isCyclic_center_of_config hcfg hK huniq))
  have houter : p = 3 → IsChevTwoOuterIndex d → False := by
    rintro rfl hdo
    obtain ⟨e'⟩ := e
    exact hcfg.false_of_le_weakCore hK huniq hcent e' (hout.1 d hdo)
      (hout.2 d hdo _ K (normal_of_forall_isComponentOf_eq hK huniq) hK.2.2 ⟨e'⟩
        (hcfg.isPGroup_centralizer hK huniq hcent)
        (hcfg.mem_center_of_mem_centralizer hK huniq hcent) Rbar hcfg.red.three_le_pRank)
  rcases hd with ⟨hp, q, hq, hq1, h | h | h | h | h | h | h | h⟩ |
    ⟨hp, q, hq, hq3, h | h | h | h⟩ | ⟨hp, h⟩
  · exact h62 G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq1, h⟩ e
  · exact hinner hp ⟨q, hq, hq1, Or.inl h⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inl h)⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inl h))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
  · exact hinner hp ⟨q, hq, hq1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
  · exact houter hp (Or.inl ⟨q, hq, hq1, h⟩)
  · exact h48 G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq3, h⟩ e
  · exact hG28 G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, q, hq, hq3, h⟩ e
  · exact houter hp (Or.inr ⟨q, hq, hq3, Or.inl h⟩)
  · exact houter hp (Or.inr ⟨q, hq, hq3, Or.inr h⟩)
  · exact hF4 G p P M H R Rbar hcfg K hK huniq hnc hcent hKD d ⟨hp, h⟩ e

end CFSG.AGLEmbedding
