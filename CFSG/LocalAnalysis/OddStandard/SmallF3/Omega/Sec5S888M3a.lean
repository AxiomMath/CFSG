module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Q

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] {z : G} {K : Fin 4 → Subgroup G}

private lemma sec5s888m3a_sl23_inv (y : SL23) (hy4 : y ^ 4 = 1) (hy1 : y ≠ 1)
    (hyn : y ≠ -1) : ∃ r : SL23, r ^ 4 = 1 ∧ r * y * r⁻¹ = y * (-1) := by
  revert y
  decide +kernel

private lemma sec5s888m3a_map_pow_eq_one {K : Subgroup G} (e : ↥K ≃* SL23) {u : G} (hu : u ∈ K)
    (n : ℕ) : (e ⟨u, hu⟩) ^ n = 1 ↔ u ^ n = 1 := by
  constructor
  · intro h
    have hsub : (⟨u, hu⟩ : ↥K) ^ n = 1 := e.injective (by rw [map_pow, h, map_one])
    simpa using congrArg Subtype.val hsub
  · intro h
    rw [← map_pow, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using h

theorem Sec5B517Quad.exists_inverting (hq : Sec5B517Quad K z) {i : Fin 4} {x : G}
    (hx : x ∈ K i) (hx4 : x ^ 4 = 1) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    ∃ r ∈ K i, r ^ 4 = 1 ∧ r * x * r⁻¹ = x * z := by
  obtain ⟨e⟩ := hq.iso i
  let x' : SL23 := e ⟨x, hx⟩
  let ζ : SL23 := e ⟨z, hq.z_mem i⟩
  have hζsq : ζ * ζ = 1 := by
    dsimp only [ζ]
    rw [← map_mul, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using hq.z_sq
  have hζ1 : ζ ≠ 1 := by
    intro hc
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := by
      apply e.injective
      rw [map_one]
      exact hc
    exact hq.z_ne (congrArg Subtype.val hsub)
  have hζneg : ζ = -1 := (sl23_unique_involution ζ hζsq).resolve_left hζ1
  have hx4' : x' ^ 4 = 1 := (sec5s888m3a_map_pow_eq_one e hx 4).2 hx4
  have hx1' : x' ≠ 1 := by
    intro hc
    have hsub : (⟨x, hx⟩ : ↥(K i)) = 1 := by
      apply e.injective
      rw [map_one]
      exact hc
    exact hx1 (congrArg Subtype.val hsub)
  have hxζ : x' ≠ ζ := by
    intro hc
    have hsub : (⟨x, hx⟩ : ↥(K i)) = ⟨z, hq.z_mem i⟩ := e.injective hc
    exact hxz (congrArg Subtype.val hsub)
  obtain ⟨s, hs4, hsx⟩ :=
    sec5s888m3a_sl23_inv x' hx4' hx1' (by rw [← hζneg]; exact hxζ)
  let rsub : ↥(K i) := e.symm s
  let r : G := rsub
  have hr : r ∈ K i := rsub.2
  have he_r : e ⟨r, hr⟩ = s := by
    have h1 : (⟨r, hr⟩ : ↥(K i)) = rsub := Subtype.ext rfl
    rw [h1]
    exact e.apply_symm_apply s
  have hr4 : r ^ 4 = 1 := by
    have h : rsub ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, e.apply_symm_apply, hs4, map_one]
    simpa [r] using congrArg Subtype.val h
  refine ⟨r, hr, hr4, ?_⟩
  have hmem_l : r * x * r⁻¹ ∈ K i :=
    (K i).mul_mem ((K i).mul_mem hr hx) ((K i).inv_mem hr)
  have hmem_r : x * z ∈ K i := (K i).mul_mem hx (hq.z_mem i)
  have hsub : (⟨r * x * r⁻¹, hmem_l⟩ : ↥(K i)) = ⟨x * z, hmem_r⟩ := by
    apply e.injective
    have hL : (⟨r * x * r⁻¹, hmem_l⟩ : ↥(K i)) =
        ⟨r, hr⟩ * ⟨x, hx⟩ * (⟨r, hr⟩)⁻¹ := Subtype.ext rfl
    have hR : (⟨x * z, hmem_r⟩ : ↥(K i)) = ⟨x, hx⟩ * ⟨z, hq.z_mem i⟩ := Subtype.ext rfl
    rw [hL, hR]
    simp only [map_mul, map_inv, he_r]
    change s * x' * s⁻¹ = x' * ζ
    rw [hsx, hζneg]
  exact congrArg Subtype.val hsub

end CFSG.OddStandard.SmallF3.Omega
