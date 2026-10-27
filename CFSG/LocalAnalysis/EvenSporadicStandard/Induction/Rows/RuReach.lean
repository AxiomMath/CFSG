module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuThm54
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuOrders
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ReachGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuStage3
public import CFSG.LieType.Catalog.Realization
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LieType.Multipliers.Sz8Matrix
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuConfig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuInputsHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuStage2
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.StdKGroup
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.Max3.Relations
public import CFSG.Walter.J1
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp
  CFSG.Assembly.LowTwoRank

abbrev IsKRu : GroupClass := IsKPinned .Ru (fun n => n = 29120)

abbrev RuKnown : GroupClass := fun X _ =>
  IsSporadic X .Ru ∨ (Sol78Thm54Types X ∧ ¬ 29 ∣ Nat.card X)

section Types

theorem suzukiModel_of_mulEquiv' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {p f : ℕ}
    (h : SuzukiModel X p f) : SuzukiModel Y p f := by
  obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.symm.trans e'⟩⟩

theorem thm54Types_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Sol78Thm54Types X) : Sol78Thm54Types Y := by
  rcases h with ⟨n, hn, h⟩ | ⟨m, hm, h⟩
  · exact Or.inl ⟨n, hn, suzukiModel_of_mulEquiv' e h⟩
  · refine Or.inr ⟨m, hm, ?_⟩
    rcases h with h | h | h | h | h
    · exact Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)
    · exact Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h))
    · exact Or.inr (Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h))))

end Types

section Cases

@[expose] def LieFam (X : Type) [Group X] (m : ℕ) : Prop :=
  LieModel X .PSp 2 2 m ∨ LieModel X .PSU 4 2 m ∨ LieModel X .PSL 4 2 m ∨
    LieModel X .PSU 5 2 m ∨ LieModel X .PSL 5 2 m

theorem center_eq_bot_of_simple_isQuasisimple_row {X : Type} [Group X] [IsSimpleGroup X]
    (hq : CFSG.IsQuasisimple X) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b') a'

theorem card_quotient_center_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hq : CFSG.IsQuasisimple X) : Nat.card (X ⧸ center X) = Nat.card X := by
  have hZ := center_eq_bot_of_simple_isQuasisimple_row hq
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv

end Cases

end CFSG.EvenSporadicStandard.Induction
