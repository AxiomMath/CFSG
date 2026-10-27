module

public import CFSG.CGT.Foote81L6.Dihedral

public section

namespace CFSG.CGT.Foote81L6.Bridge

open DihedralGroup

variable {G : Type*} [Group G]

section Lift

variable (m : ℕ) [NeZero m] (u w : G) (hu : u ^ m = 1) (hw : w * w = 1) (hwu : w * u * w⁻¹ = u⁻¹)

@[expose] def dihedralLift : DihedralGroup m →* G where
  toFun x := match x with
    | DihedralGroup.r i => u ^ i.val
    | DihedralGroup.sr i => w * u ^ i.val
  map_one' := by
    change u ^ (0 : ZMod m).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' := by
    have hA : ∀ a b : ZMod m, u ^ a.val * u ^ b.val = u ^ (a + b).val := fun a b => by
      rw [← pow_add, pow_eq_pow_mod (a.val + b.val) hu, ← ZMod.val_add]
    have hB : ∀ i j : ZMod m, u ^ (j - i).val = (u ^ i.val)⁻¹ * u ^ j.val := fun i j => by
      apply eq_inv_mul_of_mul_eq
      rw [hA, add_sub_cancel]
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
    have hC : ∀ k : ℕ, u ^ k * w = w * (u ^ k)⁻¹ := fun k => by
      have h1 : w * u ^ k * w⁻¹ = (u ^ k)⁻¹ := by rw [← conj_pow, hwu, inv_pow]
      calc u ^ k * w = w * (w⁻¹ * u ^ k * w) := by group
        _ = w * (w * u ^ k * w⁻¹) := by rw [hwinv]
        _ = w * (u ^ k)⁻¹ := by rw [h1]
    rintro (i | i) (j | j)
    · change u ^ (i + j).val = u ^ i.val * u ^ j.val
      rw [hA]
    · change w * u ^ (j - i).val = u ^ i.val * (w * u ^ j.val)
      rw [← mul_assoc, hC, hB, mul_assoc]
    · change w * u ^ (i + j).val = w * u ^ i.val * u ^ j.val
      rw [mul_assoc, hA]
    · change u ^ (j - i).val = w * u ^ i.val * (w * u ^ j.val)
      rw [hB, mul_assoc w, ← mul_assoc (u ^ i.val), hC, ← mul_assoc, ← mul_assoc, hw, one_mul]

@[simp] theorem dihedralLift_r (i : ZMod m) : dihedralLift m u w hu hw hwu (r i) = u ^ i.val := rfl

@[simp] theorem dihedralLift_sr (i : ZMod m) :
    dihedralLift m u w hu hw hwu (sr i) = w * u ^ i.val := rfl

theorem dihedralLift_injective (hord : orderOf u = m) (hw1 : ∀ k : ℕ, w * u ^ k ≠ 1) :
    Function.Injective (dihedralLift m u w hu hw hwu) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [dihedralLift_r] at h
    have h1 : orderOf u ∣ i.val := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [(ZMod.val_eq_zero i).1 h2, r_zero]
  · exact absurd h (hw1 _)

theorem dihedralLift_range_le {H : Subgroup G} (huH : u ∈ H) (hwH : w ∈ H) :
    (dihedralLift m u w hu hw hwu).range ≤ H := by
  rintro _ ⟨i | i, rfl⟩
  · exact H.pow_mem huH _
  · exact H.mul_mem hwH (H.pow_mem huH _)

theorem mem_dihedralLift_range_iff {x : G} :
    x ∈ (dihedralLift m u w hu hw hwu).range ↔
      ∃ i : ZMod m, x = u ^ i.val ∨ x = w * u ^ i.val := by
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr rfl⟩
  · rintro ⟨i, rfl | rfl⟩
    · exact ⟨r i, rfl⟩
    · exact ⟨sr i, rfl⟩

theorem u_mem_dihedralLift_range : u ∈ (dihedralLift m u w hu hw hwu).range :=
  ⟨r 1, by rw [dihedralLift_r, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hu, pow_one]⟩

theorem w_mem_dihedralLift_range : w ∈ (dihedralLift m u w hu hw hwu).range :=
  ⟨sr 0, by rw [dihedralLift_sr, ZMod.val_zero, pow_zero, mul_one]⟩

theorem map_conj_dihedralLift_range_le (g : G) {H : Subgroup G} (huH : g * u * g⁻¹ ∈ H)
    (hwH : g * w * g⁻¹ ∈ H) :
    (dihedralLift m u w hu hw hwu).range.map (MulAut.conj g).toMonoidHom ≤ H := by
  rintro _ ⟨_, ⟨i | i, rfl⟩, rfl⟩
  · change g * u ^ i.val * g⁻¹ ∈ H
    rw [← conj_pow]
    exact H.pow_mem huH _
  · change g * (w * u ^ i.val) * g⁻¹ ∈ H
    have : g * (w * u ^ i.val) * g⁻¹ = (g * w * g⁻¹) * (g * u * g⁻¹) ^ i.val := by
      rw [conj_pow]
      group
    rw [this]
    exact H.mul_mem hwH (H.pow_mem huH _)

end Lift

theorem commute_of_mem_dihedralLift_range {m m' : ℕ} [NeZero m] [NeZero m'] {u w u' w' : G}
    (hu : u ^ m = 1) (hw : w * w = 1) (hwu : w * u * w⁻¹ = u⁻¹)
    (hu' : u' ^ m' = 1) (hw' : w' * w' = 1) (hwu' : w' * u' * w'⁻¹ = u'⁻¹)
    (h1 : Commute u u') (h2 : Commute u w') (h3 : Commute w u') (h4 : Commute w w')
    {x y : G} (hx : x ∈ (dihedralLift m u w hu hw hwu).range)
    (hy : y ∈ (dihedralLift m' u' w' hu' hw' hwu').range) : x * y = y * x := by
  obtain ⟨i, rfl | rfl⟩ := (mem_dihedralLift_range_iff m u w hu hw hwu).1 hx <;>
    obtain ⟨j, rfl | rfl⟩ := (mem_dihedralLift_range_iff m' u' w' hu' hw' hwu').1 hy
  · exact (h1.pow_pow _ _).eq
  · exact ((h2.pow_left _).mul_right (h1.pow_pow _ _)).eq
  · exact ((h3.pow_right _).mul_left (h1.pow_pow _ _)).eq
  · exact (((h4.mul_right (h3.pow_right _)).mul_left
      ((h2.pow_left _).mul_right (h1.pow_pow _ _)))).eq

theorem zc_eq {a : ℕ} (ha : 1 ≤ a) : zc a = r ((2 ^ (a - 1) : ℕ) : ZMod (2 ^ a)) := by
  rw [← rho_pow ha, r_one_pow]

theorem eq_zc_or_sr_of_orderOf_eq_two {a : ℕ} (ha : 1 ≤ a) {d : DihedralGroup (2 ^ a)}
    (hd : orderOf d = 2) : d = zc a ∨ ∃ i, d = sr i := by
  rcases d with i | i
  · left
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have h2 : (r i : DihedralGroup (2 ^ (b + 1))) ^ orderOf (r i) = 1 := pow_orderOf_eq_one _
    rw [hd, r_pow, ← r_zero] at h2
    have hii : i + i = 0 := by
      have := r.inj h2
      rw [← this]
      push_cast
      ring
    rcases eq_zero_or_half hii with h0 | h1
    · exfalso
      rw [h0, r_zero, orderOf_one] at hd
      exact absurd hd (by norm_num)
    · rw [h1, zc_eq ha, Nat.add_sub_cancel]
  · exact Or.inr ⟨i, rfl⟩

theorem orderOf_zc {a : ℕ} (ha : 1 ≤ a) : orderOf (zc a) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact zc_mul_self ha) (zc_ne_one ha)

end CFSG.CGT.Foote81L6.Bridge
