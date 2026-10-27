module

public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
import CFSG.Sporadic.Mathieu.M11
import CFSG.Sporadic.Mathieu.M12
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def OddLieNoStandardL34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], OddLieType G →
    ∀ L : Subgroup G, standardComponentIsStandard L → ¬ LieModel (L ⧸ center L) .PSL 3 2 2

@[expose] def L34CyclicOddCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    LieModel (L ⧸ center L) .PSL 3 2 2 → Odd (Nat.card (center L)) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) → False

@[expose] def L34CyclicEvenCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    LieModel (L ⧸ center L) .PSL 3 2 2 → Even (Nat.card (center L)) →
    ∀ S : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (S : Subgroup (centralizer (L : Set G))) → IsSporadic G .ONan

@[expose] def RankTwoL3FourStandard : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G),
    ComponentClassification.RankTwoStandard.RankTwoHyp G A →
    Assembly.LowTwoRank.StatedClassicalModel (ComponentClassification.RankTwoStandard.rankTwoQuot A)
      .PSL 3 2 2 →
    Open.standardComponentOddCore G = ⊥ →
    IsSporadic (ComponentClassification.RankTwoStandard.rankTwoX A) .Suz ∨
      (Nonempty (center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
        IsSporadic (ComponentClassification.RankTwoStandard.rankTwoX A) .He)

theorem rankTwoL3FourStandard_of_rankTwoL3EvenStandard
    (h : ComponentClassification.RankTwoStandard.RankTwoL3EvenStandard) :
    RankTwoL3FourStandard :=
  fun G _ _ A hA h34 hO => (h G A hA 2 le_rfl h34).2.2 hO

theorem childL34_of_cases
    (hRank : RankTwoL3FourStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hOddLie : OddLieNoStandardL34) (hOdd : L34CyclicOddCenter)
    (hEven : L34CyclicEvenCenter) : ChildL34 := by
  intro G _ _ L hS h34
  have := hS.simple
  have hstd := hS.standard
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split hstd S with
    hrank | ⟨hcyc, -⟩ | ⟨n, hn, hSq, -⟩
  ·
    have hX : Subgroup.normalClosure (L : Set G) ≃* G :=
      (MulEquiv.subgroupCongr (GlueL34.normalClosure_eq_top hS)).trans Subgroup.topEquiv
    rcases hRank G L (GlueL34.rankTwoHyp hS hrank)
      (GlueL34.statedClassicalModel_of_lieModel_psl34 h34) (GlueL34.oddCore_eq_bot hS) with
      hSuz | ⟨-, hHe⟩
    · exact Or.inl (GlueL34.isSporadic_of_mulEquiv hX.symm hSuz)
    · exact Or.inr (Or.inl (GlueL34.isSporadic_of_mulEquiv hX.symm hHe))
  ·
    rcases Nat.even_or_odd (Nat.card (center L)) with hev | hodd
    · exact Or.inr (Or.inr (hEven G L hS h34 hev S hcyc))
    · exact (hOdd G L hS h34 hodd S hcyc).elim
  ·
    have hdvd : 20160 ∣ Nat.card G := by
      have h := GlueL34.card_quotient_center_dvd L
      rwa [GlueL34.card_eq_of_lieModel_psl34 h34] at h
    rcases ComponentClassification.StandardRecognition.quaternion_standard_recognition hCIT
      hS.nonab hstd S hn hSq with hlie | hM11 | hM12
    · exact (hOddLie G hlie L hstd h34).elim
    ·
      obtain ⟨e⟩ : Nonempty (G ≃* NativeSporadic.M11) := hM11
      have hG : Nat.card G = 7920 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M11
      rw [hG] at hdvd
      omega
    ·
      obtain ⟨e⟩ : Nonempty (G ≃* NativeSporadic.M12) := hM12
      have hG : Nat.card G = 95040 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12
      rw [hG] at hdvd
      omega

theorem standardComponentIsStandard_of_cfsgStandard {G : Type} [Group G] {L : Subgroup G}
    (h : CFSG.IsStandardSubgroup L) : standardComponentIsStandard L :=
  CFSG.isStandardSubgroup_iff_standardComponentIsStandard.1 h

theorem l34StandardInput_of_childL34 (h : ChildL34) :
    ComponentClassification.GSThmB.L34StandardInput := by
  intro G _ _ _ hnonab hK L hL h34
  exact h G L ⟨inferInstance, hnonab, hK, standardComponentIsStandard_of_cfsgStandard hL⟩ h34

end CFSG.OddStandard
