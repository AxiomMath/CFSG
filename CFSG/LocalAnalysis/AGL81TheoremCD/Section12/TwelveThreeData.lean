module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveThreeConclusion
public import CFSG.GH74.GLS.Stage2.Signalizer.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)

variable {G : Type} [Group G] [Finite G]

structure TwelveThreeCommon (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop where
  xSub_le_M : xSub p M H ≤ M
  xSub_normal : ((xSub p M H).subgroupOf H).Normal
  xSub_dPrime : ¬ d ∣ Nat.card (xSub p M H)
  rank_le_one : CFSG.Open.pRank d (H ⊓ M) ≤ 1
  y_simple : IsSimpleGroup (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))
  y_nonsolvable : ¬ Group.IsSolvable (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))
  three_dvd : 3 ∣ Nat.card (modPrimeComplement d (oPPrimeHull d (H ⊓ M)))

@[expose] def TwelveThreeCaseTwo (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  pLayerIn p H = ⊥ ∧ TwelveThreeAltTwo M p H d ∧
    ∀ W : Subgroup G, W ≤ xSub p M H → ¬ p ∣ Nat.card W → W ≤ relPPrimeCore p H

@[expose] def TwelveThreeCaseSix (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  ¬ pLayerIn p H ≤ M ∧ ((kSub p M H).subgroupOf H).Normal ∧ TwelveThreeAltSix M p H d ∧
    IsMaxParabolicP p (kStar p M H) (starImg p H (M ⊓ kSub p M H))

@[expose] def TwelveThreeCaseSpor (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop :=
  ¬ pLayerIn p H ≤ M ∧ ((kSub p M H).subgroupOf H).Normal ∧
    (TwelveThreeAltThree M p H d ∨ TwelveThreeAltFour M p H d ∨ TwelveThreeAltFive M p H d) ∧
    (CFSG.RankThreeEvenClassification.Helpers.primeComplementCore
        (G := ↥(oPPrimeHull d (H ⊓ M))) d).map (oPPrimeHull d (H ⊓ M)).subtype ≤ xSub p M H ∧
    (∀ h ∈ H ⊓ M ⊓ (kSub p M H ⊔ xSub p M H),
      (∀ y ∈ oPPrimeHull d (H ⊓ M), h * y * h⁻¹ * y⁻¹ ∈ xSub p M H) → h ∈ xSub p M H) ∧
    ∀ g ∈ H, Odd (orderOf g) → g ∈ kSub p M H ⊔ xSub p M H

structure TwelveThreeData (M : Subgroup G) (p : ℕ) (H : Subgroup G) (d : ℕ) : Prop where
  common : TwelveThreeCommon M p H d
  cases : TwelveThreeCaseTwo M p H d ∨ TwelveThreeCaseSix M p H d ∨ TwelveThreeCaseSpor M p H d

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
