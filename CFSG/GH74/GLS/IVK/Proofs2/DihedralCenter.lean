module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith.Frontend

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open DihedralGroup

theorem dihedral_central_rot {k : ℕ} (hk : 3 ≤ k) {c : DihedralGroup k} (hc : ∀ h : DihedralGroup k, h * c = c * h) :
    ∃ a : ZMod k, c = r a ∧ 2 * a = 0 := by
  have : NeZero k := ⟨by omega⟩
  rcases c with a | a
  · refine ⟨a, rfl, ?_⟩
    have h := hc (sr 0)
    rw [sr_mul_r, r_mul_sr] at h
    have h1 : (0 : ZMod k) + a = 0 - a := sr.inj h
    linear_combination h1
  · exfalso
    have h := hc (r 1)
    rw [r_mul_sr, sr_mul_r] at h
    have h1 : a - 1 = a + 1 := sr.inj h
    have h2 : (2 : ZMod k) = 0 := by linear_combination -h1
    have h3 : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h2
    have h4 := (ZMod.natCast_eq_zero_iff 2 k).mp h3
    have := Nat.le_of_dvd (by norm_num) h4
    omega

theorem zmod_two_mul_eq_zero_unique {k : ℕ} [NeZero k] {a b : ZMod k} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha2 : 2 * a = 0) (hb2 : 2 * b = 0) : a = b := by
  have key : ∀ c : ZMod k, c ≠ 0 → 2 * c = 0 → 2 * c.val = k := by
    intro c hc0 hc2
    have h1 : ((2 * c.val : ℕ) : ZMod k) = 0 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact hc2
    have h2 := (ZMod.natCast_eq_zero_iff (2 * c.val) k).mp h1
    have hpos : 0 < c.val := by
      rcases Nat.eq_zero_or_pos c.val with h | h
      · exact absurd ((ZMod.val_eq_zero c).mp h) hc0
      · exact h
    have hlt : c.val < k := ZMod.val_lt c
    obtain ⟨m, hm⟩ := h2
    have hm1 : m = 1 := by
      rcases m with _ | _ | m
      · omega
      · rfl
      · nlinarith
    rw [hm1, mul_one] at hm
    exact hm
  apply ZMod.val_injective
  have := key a ha ha2
  have := key b hb hb2
  omega

theorem dihedral_central_unique {P : Type*} [Group P] {k : ℕ} (hk : 3 ≤ k) (θ : P ≃* DihedralGroup k)
    {z z' : P} (hz1 : z ≠ 1) (hzc : ∀ h : P, h * z = z * h) (hz1' : z' ≠ 1)
    (hzc' : ∀ h : P, h * z' = z' * h) : z = z' := by
  have : NeZero k := ⟨by omega⟩
  have hcen : ∀ (w : P), (∀ h : P, h * w = w * h) → ∀ h : DihedralGroup k, h * θ w = θ w * h := by
    intro w hw h
    have := congrArg θ (hw (θ.symm h))
    simpa using this
  obtain ⟨a, ha, ha2⟩ := dihedral_central_rot hk (hcen z hzc)
  obtain ⟨b, hb, hb2⟩ := dihedral_central_rot hk (hcen z' hzc')
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hz1
    apply θ.injective
    rw [ha, map_one]
    rfl
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hz1'
    apply θ.injective
    rw [hb, map_one]
    rfl
  have hab : a = b := zmod_two_mul_eq_zero_unique ha0 hb0 ha2 hb2
  apply θ.injective
  rw [ha, hb, hab]

end CFSG.GH74.GLS.IVK.Proofs2
