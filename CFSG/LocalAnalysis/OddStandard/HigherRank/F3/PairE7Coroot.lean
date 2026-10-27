module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3E7Theta
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Data

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG Subgroup Assembly.LowTwoRank
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Q3.Q3W

theorem iform_parity_e7 : ∀ i : Fin (Tag.rank .E7),
    (iform (τ := .E7) (Pi.single (e7Idx 2) 1) (Pi.single i 1) +
      iform (τ := .E7) (Pi.single (e7Idx 4) 1) (Pi.single i 1) +
      iform (τ := .E7) (Pi.single (e7Idx 6) 1) (Pi.single i 1) -
      (if i.val = 0 then 1 else 0)) % 2 = 0 := by
  decide +kernel

theorem thetaDiag_mul_nodes {K : Type} [Field K] :
    thetaDiag (τ := .E7) (Pi.single (e7Idx 2) 1) (-1 : Kˣ) *
      thetaDiag (τ := .E7) (Pi.single (e7Idx 4) 1) (-1 : Kˣ) *
      thetaDiag (τ := .E7) (Pi.single (e7Idx 6) 1) (-1 : Kˣ) =
    thetaDiag thetaE7 (-1 : Kˣ) := by
  funext i
  simp only [Pi.mul_apply, thetaDiag]
  rw [← zpow_add, ← zpow_add, iform_thetaE7_single i]
  have he := Int.even_iff.2 (iform_parity_e7 i)
  generalize iform (τ := .E7) (Pi.single (e7Idx 2) 1) (Pi.single i 1) = a at he ⊢
  generalize iform (τ := .E7) (Pi.single (e7Idx 4) 1) (Pi.single i 1) = b at he ⊢
  generalize iform (τ := .E7) (Pi.single (e7Idx 6) 1) (Pi.single i 1) = c at he ⊢
  generalize (if i.val = 0 then (1 : ℤ) else 0) = d at he ⊢
  calc (-1 : Kˣ) ^ (a + b + c) = (-1) ^ (d + (a + b + c - d)) := by congr 1; ring
    _ = (-1) ^ d * (-1) ^ (a + b + c - d) := zpow_add _ _ _
    _ = (-1) ^ d := by rw [he.neg_one_zpow, mul_one]


theorem involution_theta_mem_HJ {u : E7sc 3 1}
    (hu : u ∈ stdRankOne (e7Datum (GaloisField 3 1)) thetaE7) (hu2 : orderOf u = 2) :
    u ∈ HJ 3 1 := by
  obtain ⟨a, ha, ha2⟩ := exists_involution_std3 (isRoot_single .E7 (e7Idx 2))
  obtain ⟨b, hb, hb2⟩ := exists_involution_std3 (isRoot_single .E7 (e7Idx 4))
  obtain ⟨c, hc, hc2⟩ := exists_involution_std3 (isRoot_single .E7 (e7Idx 6))
  have hmem : a * b * c ∈ HJ 3 1 :=
    mul_mem (mul_mem (rankOne_le_HJ_of_ne_zero (p := 3) (f := 1) (by decide) ha)
      (rankOne_le_HJ_of_ne_zero (p := 3) (f := 1) (by decide) hb))
      (rankOne_le_HJ_of_ne_zero (p := 3) (f := 1) (by decide) hc)
  have hε : εm (GaloisField 3 1) (a * b * c) = εm (GaloisField 3 1) u := by
    rw [map_mul, map_mul, εm_involution_std3 (isRoot_single .E7 (e7Idx 2)) ha ha2,
      εm_involution_std3 (isRoot_single .E7 (e7Idx 4)) hb hb2,
      εm_involution_std3 (isRoot_single .E7 (e7Idx 6)) hc hc2,
      εm_involution_std3 isRoot_thetaE7 hu hu2, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
      thetaDiag_mul_nodes]
  have hker : (a * b * c)⁻¹ * u ∈ (εm (GaloisField 3 1)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hε, inv_mul_cancel]
  have hz : (a * b * c)⁻¹ * u ∈ HJ 3 1 :=
    ComponentClassification.HarrisLit.T1.P54.E7Row.center_le_HJ (εm_ker_le_center hker)
  have h := mul_mem hmem hz
  rwa [mul_inv_cancel_left] at h

end CFSG.OddStandard.HigherRank.F3
