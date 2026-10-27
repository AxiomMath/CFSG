module

import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpTChainTable
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Foundations.SteinbergCADefinitionNodes
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.UHered
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.HSStd CFSG.Open
  CFSG.Assembly.LowTwoRank

@[expose] def L4CentralTwoTrivial : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → IsPGroup 2 (center K) →
    ∀ i : ℕ, 1 ≤ i → LieModel (K ⧸ center K) .PSL 4 2 (2 ^ i) → center K = ⊥

theorem two_pow_twelve_dvd_card_psl_four {Y : Type} [Group Y] {i : ℕ} (hi : 1 ≤ i)
    (h : LieModel Y .PSL 4 2 (2 ^ i)) : 2 ^ 12 ∣ Nat.card Y :=
  CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer.two_pow_twelve_dvd_card_lieModel_T hi h

section Cases

variable {G : Type} [Group G] [Finite G] {M : Subgroup G}

theorem isQuasisimple_of_stdHyp (h : StdHyp G M) : CFSG.IsQuasisimple ↥M :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥M).2.2.1.2 h.standard.1

@[expose] def HNStdExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → ¬ IsSporadic ↥L .HN

@[expose] def HNStdExclusionOn (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L : Subgroup G, StdHyp G L → ¬ IsSporadic ↥L .HN

@[expose] def HNStdExclusionHered : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Balance.UHered G → HNStdExclusionOn G

theorem HNStdExclusion.hered (h : HNStdExclusion) : HNStdExclusionHered :=
  fun G _ _ _ => h G

@[expose] def McLStdExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → ¬ IsSporadic ↥L .McL

theorem hnStdExclusion_of_largeExclusion (hLE : LargeExclusion) : HNStdExclusion :=
  fun G _ _ L h => (hLE G L h).1.2.2.2.2.2.2.2.1

theorem false_of_standard_mcl (hCTB : CentralTwoBound) (hX : McLStdExclusion) (h : StdHyp G M)
    (e : IsSporadic (↥M ⧸ center ↥M) .McL) : False := by
  have hb := (hCTB ↥M h.standard.1 h.centerTwo .McL e).1
  have h1 : Nat.card (center ↥M) = 1 := Nat.dvd_one.1 (by simpa [twoPartBound] using hb)
  exact hX G M h (isSporadic_of_center_eq_bot (Subgroup.eq_bot_of_card_eq _ h1) e)

end Cases

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
