module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eichler_sub_smul_left {u s y : V} (θ : K) (hu : Q u = 0) (hs : Q s = 0)
    (hus : polar Q u s = 0) (huy : polar Q u y = 0) (hsy : polar Q s y = 0) :
    eichler Q (u - θ • s) y = eichler Q u y * eichler Q s (-(θ • (y + Q y • u))) := by
  have hsu : polar Q s u = 0 := by rw [polar_comm, hus]
  have hyu : polar Q y u = 0 := by rw [polar_comm, huy]
  have hys : polar Q y s = 0 := by rw [polar_comm, hsy]
  have hQ1 : Q (u - θ • s) = 0 := by
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, map_smul_eq_sq, hu, hs,
      polar_smul_right_eq, hus]
    ring
  have hp1 : polar Q (u - θ • s) y = 0 := by
    rw [polar_sub_left, polar_smul_left_eq, huy, hsy]
    ring
  have hw₀ : polar Q s (-(θ • (y + Q y • u))) = 0 := by
    rw [polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq, hsy, hsu]
    ring
  have hQw₀ : Q (-(θ • (y + Q y • u))) = θ ^ 2 * Q y := by
    rw [QuadraticMap.map_neg, map_smul_eq_sq, QuadraticMap.map_add Q, map_smul_eq_sq, hu,
      polar_smul_right_eq, hyu]
    ring
  have huw₀ : polar Q u (-(θ • (y + Q y • u))) = 0 := by
    rw [polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq, huy,
      polar_self_eq_zero hu]
    ring
  have hyw₀ : polar Q y (-(θ • (y + Q y • u))) = -(2 * θ * Q y) := by
    rw [polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq, hyu,
      polar_self_eq_two_mul]
    ring
  have hw₀u : polar Q (-(θ • (y + Q y • u))) u = 0 := by rw [polar_comm]; exact huw₀
  have hw₀y : polar Q (-(θ • (y + Q y • u))) y = -(2 * θ * Q y) := by
    rw [polar_comm]; exact hyw₀
  refine LinearEquiv.ext fun x => ?_
  have hPx : polar Q x (-(θ • (y + Q y • u))) =
      -(θ * (polar Q x y + Q y * polar Q x u)) := by
    rw [polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq]
  have hxu : polar Q (eichler Q s (-(θ • (y + Q y • u))) x) u = polar Q x u := by
    rw [eichler_apply hs hw₀, polar_sub_left, polar_add_left, polar_smul_left_eq,
      polar_smul_left_eq, hw₀u, hsu]
    ring
  have hxy : polar Q (eichler Q s (-(θ • (y + Q y • u))) x) y =
      polar Q x y - 2 * θ * Q y * polar Q x s := by
    rw [eichler_apply hs hw₀, polar_sub_left, polar_add_left, polar_smul_left_eq,
      polar_smul_left_eq, hw₀y, hsy]
    ring
  rw [LinearEquiv.mul_apply, eichler_apply hQ1 hp1, eichler_apply hu huy, hxu, hxy,
    eichler_apply hs hw₀, hPx, hQw₀, polar_sub_right, polar_smul_right_eq]
  module

theorem eichler_conj_pivot_gen {u s y t : V} (hu : Q u = 0) (hs : Q s = 0)
    (hus : polar Q u s = 0) (huy : polar Q u y = 0) (hsy : polar Q s y = 0)
    (hst : polar Q s t = 0) (hyt : polar Q y t = 0) :
    eichler Q s t * eichler Q u y * (eichler Q s t)⁻¹ =
      eichler Q u y * eichler Q s (-(polar Q u t • (y + Q y • u))) := by
  have hY := eichler_mem_orthogonalGroup Q s t
  rw [eichler_conj hY]
  have hys : polar Q y s = 0 := by rw [polar_comm, hsy]
  have h1 : eichler Q s t u = u - polar Q u t • s := by
    rw [eichler_apply hs hst, hus]
    simp [sub_eq_add_neg]
  have h2 : eichler Q s t y = y := by
    rw [eichler_apply hs hst, hys, hyt]
    simp
  rw [h1, h2, eichler_sub_smul_left (polar Q u t) hu hs hus huy hsy]

theorem eichler_pivot_mem {H : Subgroup (V ≃ₗ[K] V)} {u s y t : V} (hu : Q u = 0) (hs : Q s = 0)
    (hus : polar Q u s = 0) (huy : polar Q u y = 0) (hsy : polar Q s y = 0)
    (hst : polar Q s t = 0) (hyt : polar Q y t = 0) (hC : eichler Q s t ∈ H)
    (hE : eichler Q u y ∈ H) : eichler Q s (-(polar Q u t • (y + Q y • u))) ∈ H := by
  have h := eichler_conj_pivot_gen hu hs hus huy hsy hst hyt
  have h2 : eichler Q s (-(polar Q u t • (y + Q y • u))) =
      (eichler Q u y)⁻¹ * (eichler Q s t * eichler Q u y * (eichler Q s t)⁻¹) := by
    rw [h]
    group
  rw [h2]
  exact H.mul_mem (H.inv_mem hE) (H.mul_mem (H.mul_mem hC hE) (H.inv_mem hC))

end CFSG.LieType.SeitzGeneration.OrthBlk
