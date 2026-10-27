module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedRange

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.EvenSmallLie
open CFSG.LieType.CurtisTits (IsCompatible rankOne levi)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup twistedDatum twistedRootGroup nd)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut)

set_option linter.unusedSectionVars false

local instance f4PilotQ2TwistedE6RowMainNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section SigmaFixed

variable {k : Type} [Field k] (θ : k →+* k)

theorem sigmaHat_eq_of_mem_twLevi_one {x : fixedGroup k θ} (hx : x ∈ twLevi k θ {1}) :
    sigmaHat θ x = x := by
  have hfix : ∀ γ : Fin (Tag.rank .E6) → ℤ, (γ = Pi.single (nd 3) 1 ∨ γ = -Pi.single (nd 3) 1) →
      CFSG.LieType.Steinberg.TwistedE6.rho γ = γ := by
    rintro γ (rfl | rfl)
    · rw [CFSG.LieType.Steinberg.TwistedE6.rho_single]
      rfl
    · rw [CFSG.LieType.Steinberg.TwistedE6.rho_neg_single]
      rfl
  have key : ∀ γ : Fin (Tag.rank .E6) → ℤ, IsRoot .E6 γ →
      (γ = Pi.single (nd 3) 1 ∨ γ = -Pi.single (nd 3) 1) →
      twistedRootGroup k θ (CFSG.LieType.Steinberg.TwistedE6.proj γ) ≤
        MonoidHom.eqLocus (sigmaHat θ) (MonoidHom.id _) := by
    intro γ hγ hγ' y hy
    obtain ⟨c, -, hyc⟩ := (CFSG.LieType.Steinberg.TwistedE6.mem_twistedRootGroup_iff_of_fixed θ
      hγ rfl (hfix γ hγ') y).1 hy
    apply Subtype.ext
    change CFSG.LieType.Steinberg.TwistedE6.sigma k (RingHom.id k) (y : e6Data_valid.minGroup k) =
      (y : e6Data_valid.minGroup k)
    rw [hyc, CFSG.LieType.Steinberg.TwistedE6.sigma_xm (RingHom.id k) hγ, hfix γ hγ',
      CFSG.LieType.Steinberg.TwistedE6.twistSign_of_rho_eq hγ (hfix γ hγ'), Int.cast_one, one_mul,
      RingHom.id_apply]
  have hle : twLevi k θ {1} ≤ MonoidHom.eqLocus (sigmaHat θ) (MonoidHom.id _) := by
    rw [twLevi, CFSG.LieType.CurtisTits.levi_singleton]
    refine sup_le ?_ ?_
    · have h := key _ (isRoot_single _ (nd 3)) (.inl rfl)
      rwa [CFSG.LieType.Steinberg.TwistedE6.proj_single] at h
    · have h := key _ (isRoot_neg_single _ (nd 3)) (.inr rfl)
      rwa [CFSG.LieType.Steinberg.TwistedE6.proj_neg_single] at h
  exact hle hx

theorem sigmaHat_eq_of_mem_twLevi_zero_one {x : fixedGroup k θ} (hx : x ∈ twLevi k θ {0, 1}) :
    sigmaHat θ x = x := by
  have hle : twLevi k θ {0, 1} ≤ MonoidHom.eqLocus (sigmaHat θ) (MonoidHom.id _) := by
    dsimp only [twLevi]
    rw [levi_pair]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact sigmaHat_eq_of_mem_twLevi_zero θ hy
    · exact sigmaHat_eq_of_mem_twLevi_one θ hy
  exact hle hx

end SigmaFixed

end CFSG.SeitzReduction.F4Pilot
