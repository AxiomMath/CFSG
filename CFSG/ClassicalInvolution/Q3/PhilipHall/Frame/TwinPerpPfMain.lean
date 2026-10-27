module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPfCore
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpMain

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

set_option linter.unusedSectionVars false


@[expose] def TwinPerpSmallE (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → TwoSubgroupsFourGenerated (genFittingFStar Y) → LongFundSetE3 R t

@[expose] def TwinPerpV3E (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → ¬ TwoTwins R → TwinE4 Y ∨ LongFundSetE3 R t

@[expose] def TwinPerp233E (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W →
          ¬ WCentralNontrivial W ∨ TwinE4 Y ∨ LongFundSetE3 R t

@[expose] def TwinPerp24S (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W → ¬ WCentralNontrivial W →
          TwoSubgroupsFourGenerated (genFittingFStar Y)

@[expose] def TwinPerp25A (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypS n Y R S t → TwoTwins R →
      (∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W) →
          TwoSubgroupsFourGenerated (genFittingFStar Y)

theorem twinCorePerpSE'_of_inputsA {n : ℕ} (hS : TwinPerpSmallE n) (hV3 : TwinPerpV3E n)
    (h233 : TwinPerp233E n) (h24 : TwinPerp24S n) (h25 : TwinPerp25A n) :
    TwinCorePerpSE' n := by
  refine twinCorePerpSE'_iff.mpr ?_
  intro Y _ _ R S t hP
  have hC := CoreData.of_S hP.core
  by_cases hF : TwoSubgroupsFourGenerated (genFittingFStar Y)
  · exact Or.inr (hS Y R S t hP hF)
  by_cases h2 : TwoTwins R
  · by_cases hall : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W
    · exact absurd (h25 Y R S t hP h2 hall) hF
    · push Not at hall
      obtain ⟨W, hW, htW, hnE4⟩ := hall
      have hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W :=
        (hC.perpMu hP.perp h2 hW).resolve_left hnE4
      rcases h233 Y R S t hP h2 W hW htW hS4 with hc | hout
      · exact absurd (h24 Y R S t hP h2 W hW htW hS4 hc) hF
      · exact hout
  · exact hV3 Y R S t hP h2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
