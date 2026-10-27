module

public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LocalAnalysis.OddStandard.RouteWBalanced
public import CFSG.LocalAnalysis.OddStandard.Solomon75StdDefs

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def AltStdCyclicWAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (L : Set G)),
        IsCyclic (S : Subgroup (centralizer (L : Set G))) →
          Nonempty (G ≃* alternatingGroup (Fin (n + 4))) ∨ OddLieType G

theorem altStdCyclicWAt_of_balancedFalse {G : Type} [Group G] [Finite G]
    (hU : SmallF3Interfaces.UImplication G) (hB : AltStdCyclicBalancedFalse) :
    AltStdCyclicWAt G := by
  intro L hS n hn hθ S hcyc
  obtain ⟨θ⟩ := hθ
  have := hS.simple
  by_cases hz : ∃ z : G, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set G)) ≠ ⊥
  · have hUO := hU hz
    have htop : ComponentClassification.GeneralizedFitting.subgroup G = ⊤ :=
      ComponentClassification.GSLit.generalizedFitting_eq_top_of_simple
    let e : ComponentClassification.GeneralizedFitting.subgroup G ≃* G :=
      ComponentClassification.GSLit.generalizedFittingEquivOfSimple
    rcases hUO with hlie | ⟨m, -, -, ⟨θ'⟩, -⟩ | ⟨-, hlt⟩
    · exact Or.inr ((CFSG.ClassicalInvolution.oddLieType_congr e).1 hlie)
    · exact (altStandard_in_alternating (e.symm.trans θ') hS.standard hn θ S hcyc).elim
    · exact absurd htop hlt.ne
  · push Not at hz
    exact (hB G L hS n hn ⟨θ⟩ S hcyc hz).elim

@[expose] def AltStdRankOneWAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ¬ 2 ≤ Open.pRank 2 (centralizer (L : Set G)) →
        Nonempty (G ≃* alternatingGroup (Fin (n + 4))) ∨ OddLieType G

theorem altStdRankOneWAt_of_cyclicWAt
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] (hCyc : AltStdCyclicWAt G) : AltStdRankOneWAt G := by
  intro L hS n hn e hrank
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S with h2 | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · exact absurd h2 hrank
  · exact hCyc L hS n hn e S hcyc
  · obtain ⟨e'⟩ := e
    exact Or.inr (altStd_quaternionW hCIT hS hn e' S hr hq)

@[expose] def AlternatingStandardFormInputWAt (G : Type) [Group G] [Finite G] : Prop :=
  IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → Assembly.KProper Blueprint.Catalog G →
    ∀ (L : Subgroup G) (n : ℕ), CFSG.IsStandardSubgroup L →
      8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      Nonempty (G ≃* alternatingGroup (Fin (n + 4))) ∨ OddLieType G

theorem alternatingStandardFormInputWAt_of_rankOneAt
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    {G : Type} [Group G] [Finite G] (h1 : AltStdRankOneWAt G) :
    AlternatingStandardFormInputWAt G := by
  intro hsimple hnonab hK L n hL hn e
  have hS : StandardSetting G L :=
    ⟨hsimple, hnonab, hK, standardComponentIsStandard_of_cfsgStandard hL⟩
  by_cases hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))
  · obtain ⟨e'⟩ := e
    exact Or.inl (altStd_rankTwo hRank2 hS hn e' hrank)
  · exact h1 L hS n hn e hrank

@[expose] def ChildLargeAltWAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (L : Subgroup G), StandardSetting G L →
    (∃ n : ℕ, 8 ≤ n ∧ Nonempty (L ⧸ center L ≃* alternatingGroup (Fin n))) →
    AltOutcome G ∨ OddLieType G ∨ IsSporadic G .McL ∨ IsSporadic G .Ly

theorem childLargeAltWAt_of_inputsStd {G : Type} [Group G] [Finite G]
    (hStd : AlternatingStandardFormInputWAt G) (hW : Solomon75.Solomon2AnStdW) :
    ChildLargeAltWAt G := by
  intro L hS hn
  obtain ⟨n, hn8, ⟨e⟩⟩ := hn
  have hq : CFSG.IsQuasisimple L :=
    (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hS.standard.1
  have : Group.IsPerfect L := hq.1
  have hZ : Nat.card (center L) ≤ 2 := GlueAlt.card_center_le_two_of_alt hn8 e
  have hpos : 0 < Nat.card (center L) := Nat.card_pos
  rcases (show Nat.card (center L) = 1 ∨ Nat.card (center L) = 2 by omega) with h1 | h2
  ·
    have hbot : center L = ⊥ := Subgroup.card_eq_one.1 h1
    let eL : L ≃* L ⧸ center L :=
      MulEquiv.ofBijective (QuotientGroup.mk' (center L))
        ⟨(MonoidHom.ker_eq_bot_iff _).1 (by rw [QuotientGroup.ker_mk']; exact hbot),
          QuotientGroup.mk'_surjective _⟩
    have := hS.simple
    rcases hStd hS.simple hS.nonab hS.kProper L n
      (GlueAlt.isStandardSubgroup_of_standardComponentIsStandard hS.standard) hn8
      ⟨eL.trans e⟩ with ⟨⟨eG⟩⟩ | hlie
    · exact Or.inl ⟨n + 4, by omega, ⟨eG⟩⟩
    · exact Or.inr (Or.inl hlie)
  ·
    exact hW G L hS n hn8 ⟨e⟩ h2

end CFSG.OddStandard
