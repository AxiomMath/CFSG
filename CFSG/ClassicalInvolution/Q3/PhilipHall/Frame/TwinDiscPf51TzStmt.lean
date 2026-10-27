module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf43Disc15Z

public section

set_option linter.unusedSectionVars false

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame
  CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace TwinDisc

section Statements

@[expose] def DiscUTzCentT (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t₀ : Y)
    (K K' : Subgroup Y) (z u : Y) (J : Subgroup Y) (t : Y) (W : Subgroup Y),
    Setting n R S t₀ K K' z u J t W →
      TwinMu.ThompsonWitness (CoreAssembly.conjClass (tightCore R)) K K' z u J →
      alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥ →
        dComp (CoreAssembly.conjClass (tightCore R)) K ≠
            dstarComp (CoreAssembly.conjClass (tightCore R)) K →
          SecConnU (CoreAssembly.conjClass (tightCore R)) u →
            ¬ rLayer (CoreAssembly.conjClass (tightCore R)) u ≤
                sigmaGen (CoreAssembly.conjClass (tightCore R)) K →
              ∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
                (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈
                  oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u)

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem rLayer_le_centralizer_tz_of_tz
    (hs : AlphaSteps (CoreAssembly.conjClass (tightCore R)))
    (s : Setting n R S t₀ K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set Y)) = ⊥)
    (hZ : ∀ y ∈ coreLayer (CoreAssembly.conjClass (tightCore R)) u,
      (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈
        oddCoreOf (coreLayer (CoreAssembly.conjClass (tightCore R)) u)) :
    rLayer (CoreAssembly.conjClass (tightCore R)) u ≤ Subgroup.centralizer ({t * z} : Set Y) := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  have hrY : rLayer Ω u ≤ coreLayer Ω u := rLayer_le_coreLayer hΩ h2 hc2
  exact hrY.trans (coreLayer_le_centralizer_of_trivial hs hf hc2 hα (Or.inr rfl) hZ)

theorem disc14YConnStar_of_tzCent (I : TwinDiscBase n) (h : DiscUTzCentT n) : Disc14YConnStar n :=
  fun Y _ _ R S t₀ K K' z u J t W s hw hα hne hconn hYS =>
    rLayer_le_centralizer_tz_of_tz (alphaStepsBase I s) s hα
      (h Y R S t₀ K K' z u J t W s hw hα hne hconn hYS)

end Statements

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
