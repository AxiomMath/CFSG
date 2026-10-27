module

public import CFSG.GH74.Generic.S45.LUniVec

public section

namespace CFSG.GH74.Generic.BProg.B3.L2CompU3Vec

open Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.GH74.Generic.S45.Uni

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem mem_ker_iff {x y : Fin 3 → K} (u : Fin 3 → K) :
    u ∈ LinearMap.ker (LinearMap.pi ![stdHermForm h 3 x, stdHermForm h 3 y] :
      (Fin 3 → K) →ₗ[K] (Fin 2 → K)) ↔ stdHermForm h 3 x u = 0 ∧ stdHermForm h 3 y u = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hu
    exact ⟨by simpa using congrFun hu 0, by simpa using congrFun hu 1⟩
  · rintro ⟨h1, h2⟩
    funext i
    fin_cases i <;> simp [h1, h2]

theorem exists_third_vec {x y : Fin 3 → K} (hx : stdHermForm h 3 x x = 1)
    (hy : stdHermForm h 3 y y = 1) (hxy : stdHermForm h 3 x y = 0) :
    ∃ z : Fin 3 → K, stdHermForm h 3 z z = 1 ∧ stdHermForm h 3 x z = 0 ∧
      stdHermForm h 3 y z = 0 ∧ ∀ u : Fin 3 → K, stdHermForm h 3 x u = 0 →
        stdHermForm h 3 y u = 0 → ∃ μ : K, u = μ • z := by
  have hyx : stdHermForm h 3 y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  let F : (Fin 3 → K) →ₗ[K] (Fin 2 → K) := LinearMap.pi ![stdHermForm h 3 x, stdHermForm h 3 y]
  have hFsurj : Function.Surjective F := by
    intro v
    refine ⟨v 0 • x + v 1 • y, ?_⟩
    funext i
    fin_cases i
    · simp [F, hx, hxy]
    · simp [F, hy, hyx]
  have hker : Module.finrank K (LinearMap.ker F) = 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker F
    rw [LinearMap.range_eq_top.2 hFsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    omega
  obtain ⟨z₀, hz₀0, hz₀⟩ := finrank_eq_one_iff'.1 hker
  have hz₀mem := (mem_ker_iff h (x := x) (y := y) (z₀ : Fin 3 → K)).1 z₀.2
  have hz₀0' : (z₀ : Fin 3 → K) ≠ 0 := fun h0 => hz₀0 (Subtype.ext h0)
  have hline : ∀ u : Fin 3 → K, stdHermForm h 3 x u = 0 → stdHermForm h 3 y u = 0 →
      ∃ μ : K, u = μ • (z₀ : Fin 3 → K) := by
    intro u hxu hyu
    obtain ⟨c, hc⟩ := hz₀ ⟨u, (mem_ker_iff h u).2 ⟨hxu, hyu⟩⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  have hz₀x : stdHermForm h 3 (z₀ : Fin 3 → K) x = 0 := by
    rw [hh_comm h x (z₀ : Fin 3 → K), hz₀mem.1, map_zero]
  have hz₀y : stdHermForm h 3 (z₀ : Fin 3 → K) y = 0 := by
    rw [hh_comm h y (z₀ : Fin 3 → K), hz₀mem.2, map_zero]
  set a := stdHermForm h 3 (z₀ : Fin 3 → K) (z₀ : Fin 3 → K) with ha
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hz₀0'
    apply eq_zero_of_hh_zero h
    intro v
    set v₁ : Fin 3 → K := v - stdHermForm h 3 x v • x - stdHermForm h 3 y v • y with hv₁
    have hxv₁ : stdHermForm h 3 x v₁ = 0 := by
      simp only [hv₁, map_sub, map_smul, smul_eq_mul, hx, hxy]
      ring
    have hyv₁ : stdHermForm h 3 y v₁ = 0 := by
      simp only [hv₁, map_sub, map_smul, smul_eq_mul, hy, hyx]
      ring
    obtain ⟨c, hc⟩ := hline v₁ hxv₁ hyv₁
    have hv : v = c • (z₀ : Fin 3 → K) + stdHermForm h 3 x v • x + stdHermForm h 3 y v • y := by
      rw [← hc, hv₁]
      abel
    have hzv : stdHermForm h 3 (z₀ : Fin 3 → K) v = 0 := by
      conv_lhs => rw [hv]
      simp only [map_add, map_smul, smul_eq_mul, hz₀x, hz₀y, ← ha, ha0]
      ring
    rw [hh_comm h (z₀ : Fin 3 → K) v, hzv, map_zero]
  have hba : h.bar a = a := by
    rw [ha, ← hh_comm h (z₀ : Fin 3 → K) (z₀ : Fin 3 → K)]
  obtain ⟨s, hs⟩ := exists_norm_eq h (a := a⁻¹) (by rw [map_inv₀, hba]) (inv_ne_zero ha0)
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    exact ha0 hs.symm
  refine ⟨s • (z₀ : Fin 3 → K), ?_, ?_, ?_, ?_⟩
  · simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, ← ha]
    calc s * (h.bar s * a) = (h.bar s * s) * a := by ring
      _ = 1 := by rw [hs, inv_mul_cancel₀ ha0]
  · simp only [map_smul, smul_eq_mul, hz₀mem.1, mul_zero]
  · simp only [map_smul, smul_eq_mul, hz₀mem.2, mul_zero]
  · intro u hxu hyu
    obtain ⟨c, hc⟩ := hline u hxu hyu
    refine ⟨c * s⁻¹, ?_⟩
    rw [hc, smul_smul, mul_assoc, inv_mul_cancel₀ hs0, mul_one]

theorem exists_inner_d {T : Matrix (Fin 3) (Fin 3) K} {ε : K} (hε : h.bar ε = ε)
    (hTa : ∀ z w, stdHermForm h 3 (T *ᵥ z) w = stdHermForm h 3 z (T *ᵥ w))
    {x y : Fin 3 → K} (hx : stdHermForm h 3 x x = 1) (hy : stdHermForm h 3 y y = 1)
    (hxy : stdHermForm h 3 x y = 0) (hTx : T *ᵥ x = ε • x) (hTy : T *ᵥ y = ε • y) :
    ∃ d : Matrix (Fin 3) (Fin 3) K, (d.map h.bar)ᵀ * d = 1 ∧ d.det = 1 ∧ d * d = 1 ∧
      d * pairRot h x y * d = pairRot h x y * pairRot h x y * pairRot h x y ∧ d * T = T * d := by
  obtain ⟨z, hz, hxz, hyz, hu⟩ := exists_third_vec h hx hy hxy
  have hyx : stdHermForm h 3 y x = 0 := by rw [hh_comm h x y, hxy, map_zero]
  have hzx : stdHermForm h 3 z x = 0 := by rw [hh_comm h x z, hxz, map_zero]
  have hzy : stdHermForm h 3 z y = 0 := by rw [hh_comm h y z, hyz, map_zero]
  have hTzx : stdHermForm h 3 x (T *ᵥ z) = 0 := by
    rw [← hTa x z, hTx, map_smulₛₗ, LinearMap.smul_apply, hxz, smul_zero]
  have hTzy : stdHermForm h 3 y (T *ᵥ z) = 0 := by
    rw [← hTa y z, hTy, map_smulₛₗ, LinearMap.smul_apply, hyz, smul_zero]
  obtain ⟨μ, hμ⟩ := hu (T *ᵥ z) hTzx hTzy
  have hμb : h.bar μ = μ := by
    have h1 := hTa z z
    rw [hμ, map_smulₛₗ, LinearMap.smul_apply, map_smul, hz, smul_eq_mul, smul_eq_mul] at h1
    simpa using h1
  have hxTw : ∀ w, stdHermForm h 3 x (T *ᵥ w) = ε * stdHermForm h 3 x w := by
    intro w
    rw [← hTa x w, hTx, map_smulₛₗ, hε, LinearMap.smul_apply, smul_eq_mul]
  have hzTw : ∀ w, stdHermForm h 3 z (T *ᵥ w) = μ * stdHermForm h 3 z w := by
    intro w
    rw [← hTa z w, hμ, map_smulₛₗ, hμb, LinearMap.smul_apply, smul_eq_mul]
  have hd : ∀ v, pairRot h x z *ᵥ (pairRot h x z *ᵥ v) =
      v - (2 * stdHermForm h 3 x v) • x - (2 * stdHermForm h 3 z v) • z :=
    pairRot_sq_apply h hx hz hxz
  have hc : ∀ v, pairRot h x y *ᵥ v =
      v + stdHermForm h 3 x v • (y - x) - stdHermForm h 3 y v • (x + y) := pairRot_mulVec h x y
  refine ⟨pairRot h x z * pairRot h x z, ?_, ?_, pairRot_pow_four h hx hz hxz, ?_, ?_⟩
  · apply unitary_of_isometry
    intro a b
    rw [← mulVec_mulVec, ← mulVec_mulVec, pairRot_isometry h hx hz hxz,
      pairRot_isometry h hx hz hxz]
  · rw [det_mul, pairRot_det h hx hz hxz, one_mul]
  · apply matrix_ext_mulVec
    intro w
    simp only [← mulVec_mulVec]
    rw [hd (pairRot h x y *ᵥ (pairRot h x z *ᵥ (pairRot h x z *ᵥ w))), hd w]
    simp only [hc, map_sub, map_add, map_smul, smul_eq_mul, hx, hy, hz, hxy, hxz, hyz, hyx, hzx,
      hzy]
    module
  · apply matrix_ext_mulVec
    intro w
    simp only [← mulVec_mulVec]
    rw [hd (T *ᵥ w), hd w]
    simp only [mulVec_sub, mulVec_smul, hTx, hμ, hxTw, hzTw]
    module

end CFSG.GH74.Generic.BProg.B3.L2CompU3Vec
