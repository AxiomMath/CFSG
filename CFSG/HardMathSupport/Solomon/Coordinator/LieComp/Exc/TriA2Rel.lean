module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Forms
public import CFSG.GH74.GLS.Stage4.HexD4Comm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk
open CFSG.GH74.GLS.Stage4.Hex (xOrbit_R0 xOrbit_R5 xOrbit_R15 d4g_comm02 d4g_comm24 d4g_comm04)
open CFSG.Timmesfeld.RankTwo (d43Tr d43Sharp d43Cross coe_d43Tr)
open scoped commutatorElement

set_option linter.unusedSectionVars false

section CubeRoot

variable {K : Type} [Field K] {σ : K →+* K} {F : Subfield K} {d μ : Kˣ}

private theorem rel_cube (H : FrameHyp σ F d μ) : (d : K) ^ 3 = 1 := by
  simpa using congrArg Units.val H.d3

private theorem rel_quad (H : FrameHyp σ F d μ) : (d : K) ^ 2 + d + 1 = 0 := by
  have h1 : ((d : K) - 1) * ((d : K) ^ 2 + d + 1) = 0 := by
    linear_combination rel_cube H
  have h2 : (d : K) - 1 ≠ 0 := fun h => H.d_ne (Units.ext (sub_eq_zero.mp h))
  exact (mul_eq_zero.mp h1).resolve_left h2

private theorem rel_sigma_mu (H : FrameHyp σ F d μ) : σ (μ : K) = (d : K) ^ 2 * μ := by
  linear_combination ((d : K) ^ 2) * H.sm - (σ (μ : K)) * rel_cube H

private theorem rel_sig1 (H : FrameHyp σ F d μ) {z : K} (hz : σ z = z) :
    σ ((μ : K) * z) = (d : K) ^ 2 * ((μ : K) * z) := by
  rw [map_mul, hz, rel_sigma_mu H]
  ring

private theorem rel_sig2 (H : FrameHyp σ F d μ) {z : K} (hz : σ z = z) :
    σ (σ ((μ : K) * z)) = (d : K) * ((μ : K) * z) := by
  rw [rel_sig1 H hz, map_mul, map_pow, H.sd, rel_sig1 H hz]
  linear_combination ((d : K) * ((μ : K) * z)) * rel_cube H

private theorem rel_tr_d1 (H : FrameHyp σ F d μ) {c : K} (hc : σ c = (d : K) * c) :
    c + σ c + σ (σ c) = 0 := by
  rw [hc, map_mul, H.sd, hc]
  linear_combination c * rel_quad H

private theorem rel_tr_d2 (H : FrameHyp σ F d μ) {c : K} (hc : σ c = (d : K) ^ 2 * c) :
    c + σ c + σ (σ c) = 0 := by
  rw [hc, map_mul, map_pow, H.sd, hc]
  linear_combination c * rel_quad H + (c * d) * rel_cube H

end CubeRoot


variable {K : Type} [Field K] {σ : K →+* K} {F : Subfield K} {d μ : Kˣ} (H : FrameHyp σ F d μ)

private theorem fP1_orbit (c : K) : fP1 σ H.sigma3 c = xOrbit σ (d4Root 0) c := by
  rw [fP1_eq H.sigma3 c, xOrbit_R0 σ]

private theorem fP2_orbit (c : K) :
    fP2 σ H.sigma3 μ c = xOrbit σ (d4Root 5) ((μ : K) * c) := by
  rw [fP2_eq H.sigma3 μ c, xOrbit_R5 σ]

private theorem fP3_orbit (c : K) :
    fP3 σ H.sigma3 μ c = xOrbit σ (d4Root 15) (-((μ : K) * c)) := by
  rw [fP3_eq H.sigma3 μ c, xOrbit_R15 σ H.sigma3]
  simp only [map_neg]

theorem rel12 (u w : K) (hu : σ u = u) (hw : σ w = w) :
    fP1 σ H.sigma3 u * fP2 σ H.sigma3 μ w * (fP1 σ H.sigma3 u)⁻¹ * (fP2 σ H.sigma3 μ w)⁻¹ =
      fP3 σ H.sigma3 μ (u * w) := by
  have hsh : d43Sharp σ u = u * u := by simp only [d43Sharp, hu]
  have h1 : ((d43Tr H.sigma3 (d43Sharp σ u * ((μ : K) * w)) : fixedField σ) : K) = 0 := by
    rw [coe_d43Tr]
    refine rel_tr_d2 H ?_
    rw [hsh, map_mul, map_mul, hu, rel_sig1 H hw]
    ring
  have hs : d43Sharp σ ((μ : K) * w) = (μ : K) ^ 2 * w ^ 2 := by
    rw [d43Sharp, rel_sig2 H hw, rel_sig1 H hw]
    linear_combination ((μ : K) ^ 2 * w ^ 2) * rel_cube H
  have h2 : ((d43Tr H.sigma3 (u * d43Sharp σ ((μ : K) * w)) : fixedField σ) : K) = 0 := by
    rw [coe_d43Tr]
    refine rel_tr_d1 H ?_
    rw [hs, map_mul, map_mul, map_pow, map_pow, hu, hw, rel_sigma_mu H]
    linear_combination (u * (μ : K) ^ 2 * w ^ 2 * d) * rel_cube H
  have h3 : d43Cross σ u ((μ : K) * w) = -((μ : K) * (u * w)) := by
    rw [d43Cross, rel_sig2 H hw, rel_sig1 H hw]
    simp only [hu]
    linear_combination (u * ((μ : K) * w)) * rel_quad H
  rw [fP1_orbit H, fP2_orbit H, fP3_orbit H, ← commutatorElement_def,
    d4g_comm04 σ H.sigma3 u ((μ : K) * w), h1, h2, h3, xPar_zero, xPar_zero, one_mul, mul_one]

theorem comm13 (u w : K) (hu : σ u = u) (hw : σ w = w) :
    fP1 σ H.sigma3 u * fP3 σ H.sigma3 μ w = fP3 σ H.sigma3 μ w * fP1 σ H.sigma3 u := by
  have h0 : ((d43Tr H.sigma3 (u * -((μ : K) * w)) : fixedField σ) : K) = 0 := by
    rw [coe_d43Tr]
    refine rel_tr_d2 H ?_
    rw [map_mul, map_neg, hu, rel_sig1 H hw]
    ring
  have h := d4g_comm02 σ H.sigma3 u (-((μ : K) * w))
  rw [h0, xPar_zero] at h
  rw [fP1_orbit H, fP3_orbit H]
  exact commutatorElement_eq_one_iff_mul_comm.mp h

theorem comm23 (u w : K) (hu : σ u = u) (hw : σ w = w) :
    fP2 σ H.sigma3 μ u * fP3 σ H.sigma3 μ w = fP3 σ H.sigma3 μ w * fP2 σ H.sigma3 μ u := by
  have h0 : ((d43Tr H.sigma3 (-((μ : K) * w) * ((μ : K) * u)) : fixedField σ) : K) = 0 := by
    rw [coe_d43Tr]
    refine rel_tr_d1 H ?_
    rw [map_mul, map_neg, rel_sig1 H hw, rel_sig1 H hu]
    linear_combination (-((μ : K) ^ 2 * w * u) * d) * rel_cube H
  have h := d4g_comm24 σ H.sigma3 (-((μ : K) * w)) ((μ : K) * u)
  rw [h0, neg_zero, xPar_zero] at h
  rw [fP2_orbit H, fP3_orbit H]
  exact (commutatorElement_eq_one_iff_mul_comm.mp h).symm

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
