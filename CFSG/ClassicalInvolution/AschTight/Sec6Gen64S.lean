module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64R

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

local notation "𝕏(" K ", " J ")" =>
  (J ⊓ Subgroup.normalizer (SetLike.coe K)) ⊔ (K ⊓ Subgroup.normalizer (SetLike.coe J))

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J R T : Subgroup G}
  {z j u v : G}

namespace Cfg64D

variable {N₀K N₀J : Subgroup G} {r t : G} (d : Cfg64D Ω K J z j u v R T N₀K N₀J r t)
include d

omit [Finite G] in
theorem rho_mem_normalizer : r * t ∈ Subgroup.normalizer
    ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) : Set G) :=
  Subgroup.mul_mem _ (d.c.hRN d.hr) (d.c.hTN d.ht)

omit [Finite G] in
theorem Ustar_le_UV : conjSub (r * t)⁻¹ (Subgroup.zpowers v) ≤
    Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  intro w hw
  rw [mem_conjSub_iff] at hw
  have h := (Subgroup.mem_normalizer_iff.mp
    ((Subgroup.normalizer _).inv_mem d.rho_mem_normalizer) _).mp (Subgroup.mem_sup_right hw)
  have e : (r * t)⁻¹ * ((r * t)⁻¹⁻¹ * w * (r * t)⁻¹) * (r * t)⁻¹⁻¹ = w := by group
  rwa [e] at h

omit [Finite G] in
theorem Kstar_mem : conjSub (r * t)⁻¹ J ∈ Ω := d.c.hΩ.conjInvariant _ J d.c.hJ

theorem Kstar_ne (hA : ∀ y ∈ pairNormalizers K J z j, conjSub y K ≠ J) :
    conjSub (r * t)⁻¹ J ≠ K := by
  intro h
  apply hA (r * t) d.rho_mem_Y
  rw [← h, ← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conj_rho_zj : (r * t) * (z * j) * (r * t)⁻¹ = z := by
  have h1 := d.c.conj_rho_z d.hr d.hru d.ht d.htv
  have h2 := d.c.conj_rho_j d.hr d.hru d.ht
  calc (r * t) * (z * j) * (r * t)⁻¹ =
        ((r * t) * z * (r * t)⁻¹) * ((r * t) * j * (r * t)⁻¹) := by group
    _ = j * (z * j) := by rw [h1, h2]
    _ = z := by rw [← mul_assoc, ← d.c.zj_comm, mul_assoc, d.c.hj.sq, mul_one]

theorem conj_rho_inv_z : (r * t)⁻¹ * z * (r * t)⁻¹⁻¹ = z * j := by
  calc (r * t)⁻¹ * z * (r * t)⁻¹⁻¹ =
        (r * t)⁻¹ * ((r * t) * (z * j) * (r * t)⁻¹) * (r * t)⁻¹⁻¹ := by rw [d.conj_rho_zj]
    _ = z * j := by group

theorem Kstar_inf_centralizer : conjSub (r * t)⁻¹ J ⊓ Subgroup.centralizer ({j} : Set G) =
    conjSub (r * t)⁻¹ (J ⊓ Subgroup.centralizer ({z} : Set G)) := by
  rw [conjSub_inf, conjSub_centralizer_singleton]
  have hz := d.conj_rho_inv_z
  rw [hz]
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, hxj⟩
    exact ⟨hx, mem_centralizer_mul (le_centralizer_of_isUniqueInvolution d.isUniqueInvolution_J' hx)
      hxj⟩
  · rintro ⟨hx, hxzj⟩
    refine ⟨hx, ?_⟩
    have hxz := le_centralizer_of_isUniqueInvolution d.isUniqueInvolution_J' hx
    have := mem_centralizer_mul hxz hxzj
    rwa [← mul_assoc, d.c.hz.sq, one_mul] at this

theorem Ustar_sylow : IsSylow2In (conjSub (r * t)⁻¹ (Subgroup.zpowers v))
    (conjSub (r * t)⁻¹ J ⊓ Subgroup.centralizer ({j} : Set G)) := by
  rw [d.Kstar_inf_centralizer]
  exact IsSylow2In.conj d.c.sylow_V _

theorem UV_le_centralizer_j : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤
    Subgroup.centralizer ({j} : Set G) := fun w hw =>
  Subgroup.mem_centralizer_singleton_iff.mpr (d.c.UV_comm w hw j d.c.j_mem_UV)

theorem Kstar_inf_UV : conjSub (r * t)⁻¹ J ⊓ (Subgroup.zpowers u ⊔ Subgroup.zpowers v) =
    conjSub (r * t)⁻¹ (Subgroup.zpowers v) :=
  d.Ustar_sylow.eq_of_le (d.c.UV_isPGroup.to_le inf_le_right)
    (inf_le_inf_left _ d.UV_le_centralizer_j)
    (le_inf (conjSub_mono d.c.hVJ) d.Ustar_le_UV)

theorem Kstar_inf_normalizer_le_Y : conjSub (r * t)⁻¹ J ⊓
    Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) ≤
    pairNormalizers K J z j := by
  intro w hw
  obtain ⟨hwJ, hwN⟩ := Subgroup.mem_inf.mp hw
  rw [mem_conjSub_iff] at hwJ
  have hρN := d.c.normalizer_UV_le d.rho_mem_normalizer
  have h1 : (r * t)⁻¹⁻¹ * w * (r * t)⁻¹ ∈ pairNormalizers K J z j := by
    refine Subgroup.mem_sup_right ⟨hwJ, ?_⟩
    rw [inv_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hρN hwN) (Subgroup.inv_mem _ hρN)
  have hρiY : (r * t)⁻¹ ∈ pairNormalizers K J z j := Subgroup.inv_mem _ d.rho_mem_Y
  have := Subgroup.mul_mem _ (Subgroup.mul_mem _ hρiY h1) (Subgroup.inv_mem _ hρiY)
  have e : (r * t)⁻¹ * ((r * t)⁻¹⁻¹ * w * (r * t)⁻¹) * (r * t)⁻¹⁻¹ = w := by group
  rwa [e] at this

theorem mem_X_or_of_mem_XT {w : G} (hw : w ∈ 𝕏(K, J) ⊔ Subgroup.zpowers t) :
    w ∈ 𝕏(K, J) ∨ t⁻¹ * w ∈ 𝕏(K, J) := by
  have hYN := d.c.Y_le_normalizer_X d.hK0 d.hJ0
  have htN : Subgroup.zpowers t ≤ Subgroup.normalizer ((𝕏(K, J) : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (hYN d.t_mem_Y)
  obtain ⟨x, hx, s, hs, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer htN hw
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  have htt : t * t ∈ 𝕏(K, J) := by
    rw [d.c.symm.sq_of_not_mem d.ht d.htv]
    exact d.V_le_X d.c.j_mem_V
  have hev : ∀ m : ℤ, t ^ (2 * m) ∈ 𝕏(K, J) := fun m => by
    rw [zpow_mul, zpow_two]
    exact Subgroup.zpow_mem _ htt m
  rcases Int.even_or_odd' i with ⟨m, rfl | rfl⟩
  · exact Or.inl (Subgroup.mul_mem _ hx (hev m))
  · right
    have e : t⁻¹ * (x * t ^ (2 * m + 1)) = (t⁻¹ * x * t⁻¹⁻¹) * t ^ (2 * m) := by
      rw [zpow_add, zpow_one]
      group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
      (hYN (Subgroup.inv_mem _ d.t_mem_Y)) x).mp hx) (hev m)

end Cfg64D

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
