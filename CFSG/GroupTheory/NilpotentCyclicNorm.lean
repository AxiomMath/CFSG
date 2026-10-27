module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def cyclicNormThreePow (α : G →* G) (m : ℤ) (g : G) : G :=
  (g * α g * α (α g)) ^ m

theorem map_cyclicNormThreePow (α : G →* G) (m : ℤ)
    (hα : ∀ g, α (α (α g)) = g) (g : G) :
    α (cyclicNormThreePow α m g) = g⁻¹ * cyclicNormThreePow α m g * g := by
  have hcyc : α g * α (α g) * g =
      MulAut.conj g⁻¹ (g * α g * α (α g)) := by
    simp only [MulAut.conj_apply, inv_inv]
    group
  calc
    α (cyclicNormThreePow α m g) = (α g * α (α g) * g) ^ m := by
      simp only [cyclicNormThreePow, map_zpow, map_mul, hα g]
    _ = (MulAut.conj g⁻¹ (g * α g * α (α g))) ^ m := by rw [hcyc]
    _ = MulAut.conj g⁻¹ ((g * α g * α (α g)) ^ m) := (map_zpow _ _ _).symm
    _ = g⁻¹ * cyclicNormThreePow α m g * g := by
      simp only [MulAut.conj_apply, inv_inv, cyclicNormThreePow]

theorem cyclicNormThreePow_eq_self_of_fixed (α : G →* G) (m : ℤ)
    (hpow : ∀ g : G, (g ^ (3 : ℕ)) ^ m = g) {g : G} (hg : α g = g) :
    cyclicNormThreePow α m g = g := by
  simpa only [cyclicNormThreePow, hg, pow_succ, pow_zero, one_mul] using hpow g

theorem defect_cyclicNormThreePow_mem_lowerCentralSeries_succ
    (α : G →* G) (m : ℤ) (hα : ∀ g, α (α (α g)) = g)
    (hpow : ∀ g : G, (g ^ (3 : ℕ)) ^ m = g) {n : ℕ} {g : G}
    (hg : g⁻¹ * α g ∈ (⊤ : Subgroup G).lowerCentralSeries n) :
    (cyclicNormThreePow α m g)⁻¹ * α (cyclicNormThreePow α m g) ∈
      (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
  let L := (⊤ : Subgroup G).lowerCentralSeries n
  let q : G →* G ⧸ L := QuotientGroup.mk' L
  have hker : q.ker = L := QuotientGroup.ker_mk' L
  have hquot {x y : G} (h : x⁻¹ * y ∈ L) : q y = q x := by
    have hmem : x⁻¹ * y ∈ q.ker := hker.symm ▸ h
    have hh := MonoidHom.mem_ker.mp hmem
    have hxy : q x = q y := by
      simpa only [map_mul, map_inv, inv_mul_eq_one] using hh
    exact hxy.symm
  have hmap : L.map α ≤ L := by
    dsimp only [L]
    rw [Subgroup.map_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono n le_top
  have hαg : (α g)⁻¹ * α (α g) ∈ L := by
    have hmem : α (g⁻¹ * α g) ∈ L :=
      hmap (Subgroup.mem_map.mpr ⟨g⁻¹ * α g, hg, rfl⟩)
    simpa only [map_mul, map_inv] using hmem
  have hqa : q (α g) = q g := hquot hg
  have hqa2 : q (α (α g)) = q g := (hquot hαg).trans hqa
  have hqN : q (cyclicNormThreePow α m g) = q g := by
    dsimp only [cyclicNormThreePow]
    rw [map_zpow, map_mul, map_mul, hqa, hqa2]
    simpa only [map_zpow, map_pow, map_mul, pow_succ, pow_zero, one_mul] using
      congrArg q (hpow g)
  have hu : (cyclicNormThreePow α m g)⁻¹ * g ∈ L := by
    have hh : q ((cyclicNormThreePow α m g)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hqN, inv_mul_cancel]
    exact hker ▸ MonoidHom.mem_ker.mpr hh
  have hc : ⁅(cyclicNormThreePow α m g)⁻¹ * g, g⁻¹⁆ ∈
      (⊤ : Subgroup G).lowerCentralSeries (n + 1) := by
    rw [Subgroup.mem_lowerCentralSeries_succ_iff]
    exact Subgroup.subset_closure
      ⟨(cyclicNormThreePow α m g)⁻¹ * g, hu, g⁻¹, Subgroup.mem_top _, rfl⟩
  have he : (cyclicNormThreePow α m g)⁻¹ * α (cyclicNormThreePow α m g) =
      ⁅(cyclicNormThreePow α m g)⁻¹ * g, g⁻¹⁆ := by
    rw [map_cyclicNormThreePow α m hα]
    simp only [commutatorElement_def]
    group
  rw [he]
  exact hc

theorem defect_iterate_cyclicNormThreePow_mem_lowerCentralSeries
    (α : G →* G) (m : ℤ) (hα : ∀ g, α (α (α g)) = g)
    (hpow : ∀ g : G, (g ^ (3 : ℕ)) ^ m = g) (n : ℕ) (g : G) :
    ((cyclicNormThreePow α m)^[n] g)⁻¹ * α ((cyclicNormThreePow α m)^[n] g) ∈
      (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => simp only [Function.iterate_zero_apply, Subgroup.lowerCentralSeries_zero,
      Subgroup.mem_top]
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using
      defect_cyclicNormThreePow_mem_lowerCentralSeries_succ α m hα hpow ih

theorem iterate_cyclicNormThreePow_fixed [Group.IsNilpotent G]
    (α : G →* G) (m : ℤ) (hα : ∀ g, α (α (α g)) = g)
    (hpow : ∀ g : G, (g ^ (3 : ℕ)) ^ m = g) (g : G) :
    α ((cyclicNormThreePow α m)^[Group.nilpotencyClass G] g) =
      (cyclicNormThreePow α m)^[Group.nilpotencyClass G] g := by
  have h := defect_iterate_cyclicNormThreePow_mem_lowerCentralSeries
    α m hα hpow (Group.nilpotencyClass G) g
  rw [Subgroup.lowerCentralSeries_nilpotencyClass, Subgroup.mem_bot, inv_mul_eq_one] at h
  exact h.symm

end CFSG.GroupTheory
