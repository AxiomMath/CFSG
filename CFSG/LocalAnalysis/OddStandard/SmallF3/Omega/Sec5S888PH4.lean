module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH1

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

theorem ker_le_Q8 (hS : PlaneSetup z K α) : α.ker ≤ Sec5B517Q8 hS.quad := by
  rw [hS.ker]
  exact Subgroup.zpowers_le.mpr (z_mem_Q8 hS.quad)

theorem mem_planeV_iff (hS : PlaneSetup z K α) {x : H} :
    α x ∈ planeV hS.quad α ↔ x ∈ Sec5B517Q8 hS.quad := by
  constructor
  · intro hx
    rw [planeV, Subgroup.mem_map] at hx
    obtain ⟨q, hq, hqx⟩ := hx
    have hk : q⁻¹ * x ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqx, inv_mul_cancel]
    have hkQ : q⁻¹ * x ∈ Sec5B517Q8 hS.quad := ker_le_Q8 hS hk
    have hmul := (Sec5B517Q8 hS.quad).mul_mem hq hkQ
    rwa [show q * (q⁻¹ * x) = x by group] at hmul
  · intro hx
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

private theorem s888_conj_mem_Q_of_mem_normalizer (hS : PlaneSetup z K α) {y : H}
    (hy : α y ∈ normalizer (planeV hS.quad α : Set X)) {q : H}
    (hq : q ∈ Sec5B517Q8 hS.quad) : y * q * y⁻¹ ∈ Sec5B517Q8 hS.quad := by
  have h1 : α y * α q * (α y)⁻¹ ∈ planeV hS.quad α := by
    rw [Subgroup.mem_set_normalizer_iff] at hy
    exact (hy (α q)).mp ((mem_planeV_iff hS).mpr hq)
  have hEq : α (y * q * y⁻¹) = α y * α q * (α y)⁻¹ := by
    simp only [map_mul, map_inv]
  have h2 : α (y * q * y⁻¹) ∈ planeV hS.quad α := by
    rw [hEq]
    exact h1
  exact (mem_planeV_iff hS).mp h2

theorem mem_normalizer_planeV_iff (hS : PlaneSetup z K α) {x : H} :
    α x ∈ normalizer (planeV hS.quad α : Set X) ↔
      x ∈ normalizer (Sec5B517Q8 hS.quad : Set H) := by
  constructor
  · intro hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact s888_conj_mem_Q_of_mem_normalizer hS hx hq
    · intro hxq
      have hxinv : α x⁻¹ ∈ normalizer (planeV hS.quad α : Set X) := by
        have hmem : (α x)⁻¹ ∈ normalizer (planeV hS.quad α : Set X) := inv_mem hx
        simpa only [map_inv] using hmem
      have hconj := s888_conj_mem_Q_of_mem_normalizer hS hxinv hxq
      rwa [show x⁻¹ * (x * q * x⁻¹) * (x⁻¹)⁻¹ = q by group] at hconj
  · intro hx
    rw [Subgroup.mem_set_normalizer_iff] at hx
    rw [Subgroup.mem_set_normalizer_iff]
    intro v
    constructor
    · intro hv
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
      have hEq : α x * α q * (α x)⁻¹ = α (x * q * x⁻¹) := by
        simp only [map_mul, map_inv]
      rw [hEq]
      exact (mem_planeV_iff hS).mpr ((hx q).mp hq)
    · intro hv
      obtain ⟨q, rfl⟩ := hS.surj v
      have hEq : α x * α q * (α x)⁻¹ = α (x * q * x⁻¹) := by
        simp only [map_mul, map_inv]
      rw [hEq] at hv
      exact (mem_planeV_iff hS).mpr ((hx q).mpr ((mem_planeV_iff hS).mp hv))

theorem planeW_trans [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) (i j : Fin 4) :
    ∃ g ∈ normalizer (planeV hS.quad α : Set X),
      ∀ w ∈ planeW hS.quad α i, g * w * g⁻¹ ∈ planeW hS.quad α j := by
  obtain ⟨x, hxN, hxconj⟩ := hP.trans i j
  refine ⟨α x⁻¹, (mem_normalizer_planeV_iff hS).mpr (inv_mem hxN), ?_⟩
  intro w hw
  rw [planeW, Subgroup.mem_map] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨huQ, huK⟩ := Subgroup.mem_inf.mp hu
  refine Subgroup.mem_map.mpr ⟨x⁻¹ * u * x, ?_, ?_⟩
  · rw [Subgroup.mem_inf]
    constructor
    · have ht := (Subgroup.mem_set_normalizer_iff.mp (inv_mem hxN) u).mp huQ
      rw [inv_inv] at ht
      exact ht
    · have hmem : x⁻¹ * u * x ∈ CFSG.conjugate (K i) x := by
        rw [CFSG.conjugate, Subgroup.mem_map]
        exact ⟨u, huK, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      rwa [hxconj] at hmem
  · simp only [map_mul, map_inv, inv_inv]

theorem planeW_perm [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) :
    ∀ g ∈ normalizer (planeV hS.quad α : Set X), ∀ i : Fin 4,
      ∃ j, ∀ w ∈ planeW hS.quad α i, g * w * g⁻¹ ∈ planeW hS.quad α j := by
  intro g hg i
  obtain ⟨x, rfl⟩ := hS.surj g
  have hxN : x ∈ normalizer (Sec5B517Q8 hS.quad : Set H) :=
    (mem_normalizer_planeV_iff hS).mp hg
  obtain ⟨j, hj⟩ := hP.perm x⁻¹ (inv_mem hxN) i
  refine ⟨j, ?_⟩
  intro w hw
  rw [planeW, Subgroup.mem_map] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨huQ, huK⟩ := Subgroup.mem_inf.mp hu
  refine Subgroup.mem_map.mpr ⟨x * u * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_inf]
    constructor
    · exact (Subgroup.mem_set_normalizer_iff.mp hxN u).mp huQ
    · have hmem : x * u * x⁻¹ ∈ CFSG.conjugate (K i) x⁻¹ := by
        rw [CFSG.conjugate, Subgroup.mem_map]
        exact ⟨u, huK, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      rwa [hj] at hmem
  · simp only [map_mul, map_inv, inv_inv]

theorem planeV_le_map [Finite H] {T : Subgroup H} (hP : PocketHyp z K T) (α : H →* X) :
    planeV hP.quad α ≤ T.map α :=
  Subgroup.map_mono hP.le_T

theorem planeV_normS [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) :
    ∀ s ∈ T.map α, ∀ v ∈ planeV hS.quad α, s * v * s⁻¹ ∈ planeV hS.quad α := by
  intro s hs v hv
  rw [Subgroup.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have htN : t ∈ normalizer (Sec5B517Q8 hS.quad : Set H) := hP.T_le_N ht
  have hxt : α t ∈ normalizer (planeV hS.quad α : Set X) :=
    (mem_normalizer_planeV_iff hS).mpr htN
  rw [Subgroup.mem_set_normalizer_iff] at hxt
  exact (hxt v).mp hv

theorem planeV_closed [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) :
    ∀ a ∈ planeV hS.quad α, ∀ g : X, g⁻¹ * a * g ∈ T.map α →
      g⁻¹ * a * g ∈ planeV hS.quad α := by
  intro a ha g hg
  rw [planeV, Subgroup.mem_map] at ha
  obtain ⟨q, hq, rfl⟩ := ha
  obtain ⟨x, rfl⟩ := hS.surj g
  rw [Subgroup.mem_map] at hg
  obtain ⟨t, ht, htq⟩ := hg
  have hmap : α (x⁻¹ * q * x) = (α x)⁻¹ * α q * α x := by
    simp only [map_mul, map_inv]
  have hker : t⁻¹ * (x⁻¹ * q * x) ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, htq.trans hmap.symm, inv_mul_cancel]
  have hcQ : t⁻¹ * (x⁻¹ * q * x) ∈ Sec5B517Q8 hS.quad := ker_le_Q8 hS hker
  have hxqT : x⁻¹ * q * x ∈ T := by
    have heq : x⁻¹ * q * x = t * (t⁻¹ * (x⁻¹ * q * x)) := by group
    rw [heq]
    exact T.mul_mem ht (hP.le_T hcQ)
  have hxqN : x⁻¹ * q * x ∈ normalizer (Sec5B517Q8 hS.quad : Set H) := hP.T_le_N hxqT
  have hxqQ : x⁻¹ * q * x ∈ Sec5B517Q8 hS.quad := hP.closed q hq x hxqN
  have hV := (mem_planeV_iff hS).mpr hxqQ
  rwa [hmap] at hV

theorem planeV_centS [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) :
    ∀ s ∈ T.map α, (∀ v ∈ planeV hS.quad α, s * v = v * s) → s ∈ planeV hS.quad α := by
  intro s hs hcomm
  rw [Subgroup.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have htQ : t ∈ Sec5B517Q8 hP.quad := by
    apply hP.centS t ht
    intro q hq
    have hqV : α q ∈ planeV hS.quad α := (mem_planeV_iff hS).mpr hq
    have hcv := hcomm (α q) hqV
    rw [← hS.ker, MonoidHom.mem_ker]
    have hEq : α (t * q * t⁻¹ * q⁻¹) = α t * α q * (α t)⁻¹ * (α q)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [hEq, hcv]
    group
  exact (mem_planeV_iff hS).mpr htQ

end CFSG.OddStandard.SmallF3.Omega
