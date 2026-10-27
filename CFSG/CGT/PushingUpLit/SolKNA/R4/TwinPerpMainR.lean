module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpMain
public import CFSG.ClassicalInvolution.Q3.Q3T7C231Final

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Inner

section Assembly


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem PerpHypR.perpMu (h : PerpHypR r n Y R S t) (h2 : TwinPerp.TwoTwins R) {W : Subgroup Y}
    (hW : W ∈ WSet (CoreAssembly.conjClass (tightCore R))) :
    MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W ∨
      MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W := by
  obtain ⟨K', hK', hne⟩ := h.core.twin
  have hP := h.partIHypG
  have hperp : KPerp (CoreAssembly.conjClass (tightCore R)) (tightCore R) = {tightCore R, K'} :=
    h.perp.trans (TwinPerp.twinSet_eq_pair h2 hK' hne)
  exact Q3T7.c231_mu_iso_of_clique hP hW
    (Q3T7.c231_clique hP (CoreAssembly.mem_conjClass_self _)
      (fun J ⟨g, hg⟩ => ⟨g, hg⟩) (Inner.isUniqueInvolution_core h.core.datum) hK' hne hperp hW)

@[expose] def TwinPerpSmallR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwoSubgroupsFourGenerated ↥(genFittingFStar Y) → False

@[expose] def TwinPerpV3R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → ¬ TwinPerp.TwoTwins R → False

@[expose] def TwinPerp233R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W → ¬ TwinPerp.WCentralNontrivial W

@[expose] def TwinPerp24R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    PerpHypR r n Y R S t → TwinPerp.TwoTwins R →
      ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W → ¬ TwinPerp.WCentralNontrivial W →
          TwoSubgroupsFourGenerated ↥(genFittingFStar Y)

theorem twinCorePerpR_of_inputs (hS : TwinPerpSmallR r n) (hV3 : TwinPerpV3R r n)
    (h233 : TwinPerp233R r n) (h24 : TwinPerp24R r n) (h25 : TwinPerp25AR r n) :
    TwinCorePerpR r n := by
  refine twinCorePerpR_iff.mpr ?_
  intro Y _ _ R S t hP
  by_cases hF : TwoSubgroupsFourGenerated ↥(genFittingFStar Y)
  · exact hS Y R S t hP hF
  by_cases h2 : TwinPerp.TwoTwins R
  · by_cases hall : ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore R)), t ∈ W →
        MuIsoE4 (CoreAssembly.conjClass (tightCore R)) W
    · exact hF (h25 Y R S t hP h2 hall)
    · push Not at hall
      obtain ⟨W, hW, htW, hnE4⟩ := hall
      have hS4 : MuIsoS4 (CoreAssembly.conjClass (tightCore R)) W :=
        (hP.perpMu h2 hW).resolve_left hnE4
      exact hF (h24 Y R S t hP h2 W hW htW hS4 (h233 Y R S t hP h2 W hW htW hS4))
  · exact hV3 Y R S t hP h2

end Assembly

end CFSG.CGT.PushingUpLit.SolKNA.R4
