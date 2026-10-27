module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup DihedralGroup

@[expose] def rotations (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {d | ∃ i : ZMod n, d = r i}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, r_mul_r i j⟩
  one_mem' := ⟨0, one_def⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, inv_r i⟩

theorem mem_rotations {n : ℕ} {d : DihedralGroup n} : d ∈ rotations n ↔ ∃ i : ZMod n, d = r i :=
  Iff.rfl

section

variable {S : Type} [Group S] {n : ℕ} {φ : S →* DihedralGroup n}

theorem mem_comap_rotations_or {s : S} (hs : φ s = sr 0) (x : S) :
    x ∈ (rotations n).comap φ ∨ s⁻¹ * x ∈ (rotations n).comap φ := by
  cases hx : φ x with
  | r i => exact Or.inl ⟨i, hx⟩
  | sr i =>
    right
    show φ (s⁻¹ * x) ∈ rotations n
    rw [map_mul, map_inv, hs, hx, inv_sr, sr_mul_sr]
    exact ⟨i - 0, rfl⟩

theorem pow_mem_ker {r : S} (hr : φ r = DihedralGroup.r 1) : r ^ n ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_pow, hr]
  exact r_one_pow_n

theorem conj_mul_mem_ker {r s : S} (hr : φ r = DihedralGroup.r 1) (hs : φ s = sr 0) :
    s * r * s⁻¹ * r ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hs, hr, inv_sr, sr_mul_r, sr_mul_sr]
  simp

variable [NeZero n]

theorem exists_pow_mul_mem_ker {r : S} (hr : φ r = DihedralGroup.r 1) {c : S}
    (hc : c ∈ (rotations n).comap φ) : ∃ k : ℕ, (r ^ k)⁻¹ * c ∈ φ.ker := by
  obtain ⟨i, hi⟩ := hc
  refine ⟨i.val, ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hr, hi, r_one_pow, ZMod.natCast_zmod_val,
    inv_r, r_mul_r, neg_add_cancel, ← one_def]

end

end CFSG.EvenSporadicStandard.Induction.Junction
