module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.HardMathSupport.Lang.Proving

open CFSG

theorem mem_range_pow_iff_of_card_eq_mul {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    {d m : ℕ} (hdm : Nat.card G = d * m) (hd : 0 < d) (x : G) :
    x ∈ (powMonoidHom d : G →* G).range ↔ x ^ m = 1 := by
  have hddvd : d ∣ Nat.card G := Dvd.intro m hdm.symm
  have hmdvd : m ∣ Nat.card G := Dvd.intro_left d hdm.symm
  have hidx : (powMonoidHom d : G →* G).range.index = d := by
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hddvd]
  have hcard_range : Nat.card (powMonoidHom d : G →* G).range = m := by
    have h := Subgroup.card_mul_index (powMonoidHom d : G →* G).range
    rw [hidx, hdm] at h
    have h2 : d * Nat.card (powMonoidHom d : G →* G).range = d * m := by
      rw [mul_comm]
      exact h
    exact Nat.eq_of_mul_eq_mul_left hd h2
  have hker : Nat.card (powMonoidHom m : G →* G).ker = m := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hmdvd]
  have hle : (powMonoidHom d : G →* G).range ≤ (powMonoidHom m : G →* G).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, powMonoidHom_apply, ← pow_mul, ← hdm]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard y)
  have heq : (powMonoidHom d : G →* G).range = (powMonoidHom m : G →* G).ker := by
    apply Subgroup.eq_of_le_of_card_ge hle
    omega
  constructor
  · intro hx
    rw [heq] at hx
    simpa [powMonoidHom_apply] using hx
  · intro hx
    rw [heq]
    exact MonoidHom.mem_ker.mpr (by simpa [powMonoidHom_apply] using hx)

theorem exists_pow_eq_of_pow_eq_one {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    {d m : ℕ} (hdm : Nat.card G = d * m) (hd : 0 < d) (y : G) (hy : y ^ m = 1) :
    ∃ x : G, x ^ d = y := by
  have h := (mem_range_pow_iff_of_card_eq_mul hdm hd y).mpr hy
  obtain ⟨x, hx⟩ := h
  exact ⟨x, by simpa [powMonoidHom_apply] using hx⟩

theorem mem_range_pow_three_iff {G : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    (h3 : 3 ∣ Nat.card G) (x : G) :
    x ∈ (powMonoidHom 3 : G →* G).range ↔ x ^ (Nat.card G / 3) = 1 :=
  mem_range_pow_iff_of_card_eq_mul (Nat.mul_div_cancel' h3).symm (by norm_num) x

end CFSG.HardMathSupport.Lang.Proving

end
