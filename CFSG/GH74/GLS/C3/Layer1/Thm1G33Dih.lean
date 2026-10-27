module

public import CFSG.GH74.GLS.IVK.L2.DihedralAux
public import CFSG.GH74.GLS.IVK.Defs

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

open Subgroup DihedralGroup

theorem exists_conj_not_mem_of_dihedral {G : Type} [Group G] {P : Subgroup G} {n : ℕ} (hn : 4 ≤ n)
    (hP : IVK.IsDihedralTwoGroup ↥P n) {z u : G} (hzP : z ∈ P) (hz1 : z ≠ 1)
    (hzc : ∀ q ∈ P, z * q = q * z) (huP : u ∈ P) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ c ∈ P, c * u * c⁻¹ ≠ u ∧ c * u * c⁻¹ ≠ z * u := by
  obtain ⟨-, k, hk2n, hk2, ⟨φ⟩⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h16 : 2 ^ (m + 4) = 16 * 2 ^ m := by ring
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨t, rfl⟩ : ∃ t, k = 8 * t := ⟨2 ^ m, by omega⟩
  have ht : 1 ≤ t := by omega
  have : NeZero (8 * t) := ⟨by omega⟩
  have hkeven : Even (8 * t) := ⟨4 * t, by ring⟩
  have hk2' : 8 * t ≠ 2 := by omega
  have hZc : φ ⟨z, hzP⟩ ∈ Subgroup.center (DihedralGroup (8 * t)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc q q.2).symm
  have hZ1 : φ ⟨z, hzP⟩ ≠ 1 := by
    intro h
    apply hz1
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  have hZ := IVK.DihedralAux.eq_r_half_of_central hkeven hk2' hZc hZ1
  have hU2 : φ ⟨u, huP⟩ * φ ⟨u, huP⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, huP⟩ : ↥P) * ⟨u, huP⟩ = 1 := Subtype.ext hu2
    rw [this, map_one]
  have hU1 : φ ⟨u, huP⟩ ≠ 1 := by
    intro h
    apply hu1
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  have hUZ : φ ⟨u, huP⟩ ≠ φ ⟨z, hzP⟩ := by
    intro h
    apply huz
    exact congrArg Subtype.val (φ.injective h)
  obtain ⟨j, hj⟩ : ∃ j, φ ⟨u, huP⟩ = sr j := by
    rcases hUu : φ ⟨u, huP⟩ with i | j
    · exfalso
      rw [hUu, r_mul_r] at hU2
      have h2 : i + i = 0 := by simpa using r.inj hU2
      rcases IVK.DihedralAux.two_mul_eq_zero_iff i h2 with h | h
      · apply hU1; rw [hUu, h]; rfl
      · apply hUZ; rw [hUu, hZ, h]
    · exact ⟨j, rfl⟩
  refine ⟨((φ.symm (r 1) : ↥P) : G), (φ.symm (r 1)).2, ?_, ?_⟩
  · intro h
    have h1 : φ.symm (r 1) * ⟨u, huP⟩ * (φ.symm (r 1))⁻¹ = ⟨u, huP⟩ := Subtype.ext h
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hj, r_mul_sr, inv_r, sr_mul_r] at h2
    have h3 := sr.inj h2
    have h4 : ((2 : ℕ) : ZMod (8 * t)) = 0 := by
      push_cast
      linear_combination -h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · intro h
    have h1 : φ.symm (r 1) * ⟨u, huP⟩ * (φ.symm (r 1))⁻¹ = ⟨z, hzP⟩ * ⟨u, huP⟩ := Subtype.ext h
    have h2 := congrArg φ h1
    rw [map_mul, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hj, hZ, r_mul_sr, inv_r,
      sr_mul_r, r_mul_sr] at h2
    have h3 := sr.inj h2
    have h4 : ((2 : ℕ) : ZMod (8 * t)) = ((4 * t : ℕ) : ZMod (8 * t)) := by
      have : (8 * t) / 2 = 4 * t := by omega
      rw [this] at h3
      push_cast at h3 ⊢
      linear_combination -h3
    rw [ZMod.natCast_eq_natCast_iff'] at h4
    have h5 : (2 : ℕ) % (8 * t) = 2 := Nat.mod_eq_of_lt (by omega)
    have h6 : (4 * t) % (8 * t) = 4 * t := Nat.mod_eq_of_lt (by omega)
    rw [h5, h6] at h4
    omega

theorem exists_sq_eq_of_dihedral {G : Type} [Group G] {P : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hP : IVK.IsDihedralTwoGroup ↥P n) {z : G} (hzP : z ∈ P) (hz1 : z ≠ 1)
    (hzc : ∀ q ∈ P, z * q = q * z) : ∃ c ∈ P, c * c = z := by
  obtain ⟨-, k, hk2n, hk2, ⟨φ⟩⟩ := hP
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have hm1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨s, rfl⟩ : ∃ s, k = 4 * s := ⟨2 ^ m, by omega⟩
  have hs : 1 ≤ s := by omega
  have : NeZero (4 * s) := ⟨by omega⟩
  have hkeven : Even (4 * s) := ⟨2 * s, by ring⟩
  have hk2' : 4 * s ≠ 2 := by omega
  have hZc : φ ⟨z, hzP⟩ ∈ Subgroup.center (DihedralGroup (4 * s)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨q, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc q q.2).symm
  have hZ1 : φ ⟨z, hzP⟩ ≠ 1 := by
    intro h
    apply hz1
    have := φ.injective (h.trans (map_one φ).symm)
    exact congrArg Subtype.val this
  have hZ := IVK.DihedralAux.eq_r_half_of_central hkeven hk2' hZc hZ1
  refine ⟨((φ.symm (r (s : ZMod (4 * s))) : ↥P) : G), (φ.symm (r (s : ZMod (4 * s)))).2, ?_⟩
  have h1 : φ.symm (r (s : ZMod (4 * s))) * φ.symm (r (s : ZMod (4 * s))) = ⟨z, hzP⟩ := by
    apply φ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, r_mul_r, hZ]
    congr 1
    have : (4 * s) / 2 = s + s := by omega
    rw [this]
    push_cast
    rfl
  exact congrArg Subtype.val h1

end CFSG.GH74.GLS.C3.Layer1.Thm1G33
