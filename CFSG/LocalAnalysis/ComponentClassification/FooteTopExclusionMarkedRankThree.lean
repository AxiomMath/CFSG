module

public import CFSG.LocalAnalysis.ComponentClassification.FooteTopExclusionMarkedFactorCover
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedRankThreeStar
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedRankThreeStandard
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedRankThreeOddLie
import CFSG.LocalAnalysis.ComponentClassification.FooteMarkedSemisimpleTools
import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7KProper

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

section Core

variable {B : Type} [Group B] [Finite B]

private theorem standardComponentOddCore_eq_bot (hO : pPrimeCore 2 B = ⊥) :
    Open.standardComponentOddCore B = ⊥ := by
  rw [← hO]
  unfold Open.standardComponentOddCore pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

private theorem open_pRank_eq (H : Subgroup B) : Open.pRank 2 H = CFSG.pRank 2 ↥H := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_eq_open_pRank_top]

theorem isComponent_of_rankThree (h5 : GSThmB.AschbacherTheorem5Input)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hAS : ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X),
      Open.standardComponentIsStandard A → Open.standardComponentOddCore X = ⊥ →
      2 ≤ Open.pRank 2 (centralizer (A : Set X)) →
      RankTwoStandard.RankTwoOddLieType (RankTwoStandard.rankTwoQuot A) → A.Normal)
    (hAlt : ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X),
      Assembly.KProper Blueprint.Catalog X → Open.standardComponentIsStandard A →
      Open.standardComponentOddCore X = ⊥ → ¬ A.Normal →
      2 ≤ Open.pRank 2 (centralizer (A : Set X)) → ∀ n : ℕ, 5 ≤ n → n ≤ 7 →
      (↥A ⧸ center ↥A ≃* alternatingGroup (Fin n)) → Odd (Nat.card (center ↥A)) →
      Open.pRank 2 (centralizer (A : Set X)) ≤ 2)
    (hKB : Assembly.KProper Blueprint.Catalog B) (hO : pPrimeCore 2 B = ⊥) {A : Subgroup B}
    (hRI : ∀ (a b : B) (K : Subgroup B), orderOf a = 2 → A ≤ centralizer ({a} : Set B) →
      IsComponent (A.subgroupOf (centralizer ({a} : Set B))) → GrSLit.GSWeakCorr a A b K →
        K = A)
    {a : B} (ha : orderOf a = 2) (hAa : A ≤ centralizer ({a} : Set B))
    (hA : IsComponent (A.subgroupOf (centralizer ({a} : Set B))))
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : FooteFamilyType L)
    (e : ↥A ⧸ center ↥A ≃* L ⧸ Open.fusionZStar L) (hZ : Odd (Nat.card (center ↥A)))
    (h3 : 3 ≤ CFSG.pRank 2 ↥(centralizer (A : Set B))) : IsComponent A := by
  have hAq : CFSG.IsQuasisimple ↥A :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hAa) hA.1
  have hstar : ∀ v : B, orderOf v = 2 → A ≤ centralizer ({v} : Set B) →
      IsComponent (A.subgroupOf (centralizer ({v} : Set B))) := fun v hv hvA =>
    FooteMarked.isComponent_centralizer_of_relativeIdentity hRI ha hAa hA hv hvA
  have hA2 : 2 ≤ CFSG.pRank 2 ↥A :=
    FooteMarked.two_le_pRank_of_quotient_center e hZ
      (FooteMarked.exists_isKleinFour_of_footeFamilyType hL)
  rcases FooteMarked.isSubnormal_or_standard_of_star h5 hK hAq hstar ha hAa hA2 with hsub | hstd
  · exact ⟨hAq, hsub⟩
  refine ⟨hAq, ?_⟩
  by_contra hsub
  have hN : ¬ A.Normal := fun hN => hsub hN.isSubnormal
  have h3' : 3 ≤ Open.pRank 2 (centralizer (A : Set B)) := by
    rw [open_pRank_eq]
    exact h3
  rcases FooteMarked.normal_or_alternating_of_standard hAS hO hstd (le_trans (by norm_num) h3) e
      hL with hN' | ⟨n, hn5, hn7, ⟨eA⟩⟩
  · exact hN hN'
  have hle := hAlt B A hKB hstd (standardComponentOddCore_eq_bot hO) hN
    (le_trans (by norm_num) h3') n hn5 hn7 eA hZ
  omega

end Core

theorem footeMarkedRankThreeAbsorption_of_relativeIdentity (hId : FooteMarkedRelativeIdentity)
    (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hAS : ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X),
      Open.standardComponentIsStandard A → Open.standardComponentOddCore X = ⊥ →
      2 ≤ Open.pRank 2 (centralizer (A : Set X)) →
      RankTwoStandard.RankTwoOddLieType (RankTwoStandard.rankTwoQuot A) → A.Normal)
    (hAlt : ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X),
      Assembly.KProper Blueprint.Catalog X → Open.standardComponentIsStandard A →
      Open.standardComponentOddCore X = ⊥ → ¬ A.Normal →
      2 ≤ Open.pRank 2 (centralizer (A : Set X)) → ∀ n : ℕ, 5 ≤ n → n ≤ 7 →
      (↥A ⧸ center ↥A ≃* alternatingGroup (Fin n)) → Odd (Nat.card (center ↥A)) →
      Open.pRank 2 (centralizer (A : Set X)) ≤ 2) :
    FooteMarkedRankThreeAbsorption := by
  intro G _ _ t L 𝓢 hset H hH a A ha hAa hA hM ⟨e⟩ hZ h3
  exact isComponent_of_rankThree h5 hK hAS hAlt
    (HSFLit.HS7.kProper_quotient_catalog (HSFLit.HS7.kProper_subgroup_catalog hset.2.1.1.1 H) _)
    (pPrimeCore_quotient_eq_bot Nat.prime_two)
    (fun a' b K _ hAa' hA' hCorr => hId G t L 𝓢 hset H hH a' A hAa' hA' hM b K hCorr)
    ha hAa hA hset.2.1.1.2.2.2.2.1 e hZ h3

end CFSG.ComponentClassification.FooteLit
