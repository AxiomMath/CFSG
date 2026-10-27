module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Thm46FS.ChildrenHered
public import CFSG.LocalAnalysis.OddStandard.L34EvenSylowBal
public import CFSG.LocalAnalysis.OddStandard.OddLieFaithful
import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Sec
import CFSG.LocalAnalysis.ComponentClassification.GrSLitBalance
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.OddStandard

theorem uOutcome_of_uhered {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hU : Balance.UHered G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (hz : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥) :
    CFSG.ComponentClassification.OutcomeLocal.UOutcome G := by
  obtain ⟨z, hz2, hu⟩ := hz
  rcases hU G (CFSG.SignalizerFunctorTheorem.IsSectionOf.refl G) hnonab hK z hz2 hu with
    hlie | ⟨n, h7, h3, ⟨e⟩⟩
  · exact CFSG.ComponentClassification.GSThmB.Eight2.uOutcome_of_oddLieType hlie
  · exact CFSG.ComponentClassification.GrSLit.uOutcome_of_mulEquiv_alternating
      (Nat.odd_iff.2 (by omega)) h7 h3 e

theorem childL34WAt_of_casesBal
    (hRank : RankTwoL3FourStandard)
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hOdd : L34CyclicOddCenter) (hEven : L34CyclicEvenCenterBal)
    {G : Type} [Group G] [Finite G] (hU : Balance.UHered G) : ChildL34WAt G := by
  intro L hS h34
  have := hS.simple
  have hstd := hS.standard
  by_cases hub : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥
  ·
    have hUo := uOutcome_of_uhered hU hS.nonab hS.kProper hub
    have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
      ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
    let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
      ComponentClassification.GSLit.generalizedFittingEquivOfSimple
    rcases hUo with h | ⟨n, -, -, ⟨eA⟩, -⟩ | ⟨-, hlt⟩
    · exact Or.inl ((ClassicalInvolution.oddLieType_congr e).1 h)
    ·
      obtain ⟨m, hm, ⟨eL⟩⟩ := exists_mulEquiv_alternatingGroup_of_standard (e.symm.trans eA) hstd
      exact (ComponentClassification.CatLeaf.not_isL34Type_of_isAltType
        ⟨Fin m, inferInstance, inferInstance, by simpa using hm, ⟨eL⟩⟩ h34).elim
    · exact absurd htop hlt.ne
  ·
    have hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := by
      intro z hz
      by_contra hne
      exact hub ⟨z, hz, hne⟩
    obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
    rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split hstd S with
      hrank | ⟨hcyc, -⟩ | ⟨n, hn, hSq, -⟩
    ·
      have hX : Subgroup.normalClosure (L : Set G) ≃* G :=
        (MulEquiv.subgroupCongr (GlueL34.normalClosure_eq_top hS)).trans Subgroup.topEquiv
      rcases hRank G L (GlueL34.rankTwoHyp hS hrank)
        (GlueL34.statedClassicalModel_of_lieModel_psl34 h34) (GlueL34.oddCore_eq_bot hS) with
        hSuz | ⟨-, hHe⟩
      · exact Or.inr (Or.inl (GlueL34.isSporadic_of_mulEquiv hX.symm hSuz))
      · exact Or.inr (Or.inr (Or.inl (GlueL34.isSporadic_of_mulEquiv hX.symm hHe)))
    ·
      rcases Nat.even_or_odd (Nat.card (center L)) with hev | hodd
      · exact Or.inr (Or.inr (Or.inr (hEven G L hS hbal h34 hev S hcyc)))
      · exact (hOdd G L hS h34 hodd S hcyc).elim
    ·
      have hdvd : 20160 ∣ Nat.card G := by
        have h := GlueL34.card_quotient_center_dvd L
        rwa [GlueL34.card_eq_of_lieModel_psl34 h34] at h
      rcases ComponentClassification.StandardRecognition.quaternion_standard_recognition hCIT
        hS.nonab hstd S hn hSq with hlie | hM11 | hM12
      · exact Or.inl hlie
      ·
        obtain ⟨e⟩ : Nonempty (G ≃* NativeSporadic.M11) := hM11
        have hG : Nat.card G = 7920 :=
          (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11
        rw [hG] at hdvd
        omega
      ·
        obtain ⟨e⟩ : Nonempty (G ≃* NativeSporadic.M12) := hM12
        have hG : Nat.card G = 95040 :=
          (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12
        rw [hG] at hdvd
        omega

theorem childHeWAt_of_casesO
    (hMult : CFSG.ComponentClassification.TBLit.HeldTrivialMultiplier)
    (hRank : RankTwoHeStandardO) (hBal : HeStandardBalanced)
    {G : Type} [Group G] [Finite G] (hU : Balance.UHered G) : ChildHeWAt G := by
  intro L hS hHe
  have := hS.simple
  have hstd := hS.standard
  by_cases hUo : ComponentClassification.OutcomeLocal.UOutcome G
  ·
    have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
      ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
    let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
      ComponentClassification.GSLit.generalizedFittingEquivOfSimple
    rcases hUo with h | ⟨n, hodd, h7, ⟨eA⟩, h1⟩ | ⟨-, hlt⟩
    · exact (ClassicalInvolution.oddLieType_congr e).1 h
    · exact (altNoStandardHe G hS.nonab n hodd h7 (fun h4 => (h1 h4).ne htop)
        ⟨e.symm.trans eA⟩ L hstd hHe).elim
    · exact absurd htop hlt.ne
  ·
    have hbal : ∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥ := by
      intro z hz
      by_contra hne
      exact hUo (uOutcome_of_uhered hU hS.nonab hS.kProper ⟨z, hz, hne⟩)
    have hrank : ¬ 2 ≤ Open.pRank 2 (centralizer (L : Set G)) := fun h2 =>
      hRank G L (GlueL34.rankTwoHyp hS h2) (GlueL34.oddCore_eq_bot hS) hHe
    have hq : CFSG.IsQuasisimple L :=
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hstd.1
    have hZ : center L = ⊥ := hMult L hq hHe
    exact (hBal G hS.nonab hS.kProper hUo hbal L hstd hHe hZ hrank).elim

end CFSG.EvenSporadicStandard.Induction
