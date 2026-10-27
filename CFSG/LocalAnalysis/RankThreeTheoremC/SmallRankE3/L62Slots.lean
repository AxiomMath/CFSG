module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630HH
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Evasion630
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fitting628
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wResDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Fail614Reduce
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.U0

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem prop614_failing_three_of_core_of_d1 (hS : Setting G) (hD1 : TheoremD1 G)
    (hK : KFactBlockFactorThreePrime)
    (hdich : ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z →
        HasPrimeConstraint (G := M) 3 ∨ SmallRankCaseDelta3 P M)
    (hnrδ : ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z → SmallRankCaseDelta3 P M →
        Fail614NormalizerRank P M (zpowers x ⊔ zpowers z))
    (hcore : Prop614FailCore G) :
    ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 3 P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M :=
  fun P M x z T hf => prop614_failing_three_of_core hS
    (fullCoreLocal_of_theoremD1_situation_three hS hD1 hf.situation) hD1 hK hdich hnrδ hcore
    P M x z T hf

theorem lemma630Res_of_five_of_d1 (hS : Setting G) (hD1 : TheoremD1 G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hL62 : GL83SmallRankLemma62At3 G) (hOut : KFactOutQ8Quaternion)
    (hP614 : ∀ (P : Sylow 3 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 3 P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M)
    (h5 : ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G) (T : Subgroup G) (f : ℕ),
      Lemma630Hyp G 5 P M x z T f →
        (∀ E : Subgroup G, SmallRankSBSylow 5 f x z T E → E ⊓ M = ⊥) ∧ Lemma630Iii 5 f x) :
    GL83SmallRankLemma630Res G where
  evasion := by
    intro p P M x z T f hyp _
    obtain hp | hp := hyp.lemma628.1
    · subst hp
      exact evasion_three hS (fullCoreLocal_of_theoremD1_situation_three hS hD1 hyp.failure.situation)
        hK1 hK2 hL62 hyp
    · subst hp
      exact (h5 P M x z T f hyp).1
  iii := by
    intro p P M x z T f hyp
    obtain hp | hp := hyp.lemma628.1
    · subst hp
      exact lemma630_iii_three hS (fullCoreLocal_of_theoremD1_situation_three hS hD1 hyp.failure.situation)
        hK1 hK2 hL62 hOut kFactHallHigmanOdd_holds hyp (hP614 P M x z T hyp.failure)
    · subst hp
      exact (h5 P M x z T f hyp).2

theorem interfaceW_of_five_of_d1 (hS : Setting G) (hD1 : TheoremD1 G)
    (hK1 : KFactRankTwoUniqueness) (hK2 : KFactRankThreeStructure)
    (hL62 : GL83SmallRankLemma62At3 G)
    (hP614 : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G p P M x z T → ∀ S₀ : Subgroup G, S₀ ≤ smallRankS x T → S₀ ≠ ⊥ →
        zpowers z ≤ normalizer (S₀ : Set G) → normalizer (S₀ : Set G) ≤ M)
    (h5 : ∀ (P : Sylow 5 G) (M : Subgroup G) (x z : G) (T : Subgroup G),
      Prop627Failure G 5 P M x z T → SmallRankCover 5 M x →
        smallRankIsQ8D8 (smallRankR x z T) →
          CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD 5 x)) ⊓ M = ⊥) :
    GL83SmallRankInterfaceW G where
  prop614 := hP614
  fitting628 := by
    intro p P M x z T hf hcov hp h3 h5' _
    obtain hp | hp := hp
    · subst hp
      exact fitting628_three hS (fullCoreLocal_of_theoremD1_situation_three hS hD1 hf.situation)
        hK1 hK2 hL62 hf (h3 rfl)
    · subst hp
      exact h5 P M x z T hf hcov (h5' rfl)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
