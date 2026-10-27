module

public import CFSG.LocalAnalysis.OddStandard.RouteWChildren
public import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.LocalAnalysis.OddStandard.ChildHe
import CFSG.LocalAnalysis.OddStandard.AltNoHe
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Mathieu.M11

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def L34EvenSylowStepBal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
    LieModel (L ⧸ center L) .PSL 3 2 2 → Even (Nat.card (center L)) →
    ∀ R : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (R : Subgroup (centralizer (L : Set G))) →
        ∃ (S : Sylow 2 G) (T : Sylow 2 NativeSporadic.ON),
          Nonempty ((S : Subgroup G) ≃* (T : Subgroup NativeSporadic.ON))

@[expose] def L34CyclicEvenCenterBal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    (∀ z : G, orderOf z = 2 → CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) →
    LieModel (L ⧸ center L) .PSL 3 2 2 → Even (Nat.card (center L)) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) → IsSporadic G .ONan

theorem childL34W_of_casesBal
    (hRank : RankTwoL3FourStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hOdd : L34CyclicOddCenter) (hEven : L34CyclicEvenCenterBal)
    (hU : KProperSimpleUnbalancedUOutcome) : ChildL34W := by
  intro G _ _ L hS h34
  have := hS.simple
  have hstd := hS.standard
  by_cases hub : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥
  ·
    have hUo := hU G hS.nonab hS.kProper hub
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

end CFSG.OddStandard
