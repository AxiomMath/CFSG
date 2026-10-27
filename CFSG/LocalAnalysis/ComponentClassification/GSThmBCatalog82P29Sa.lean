module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open DihedralGroup

section Hom

variable {G : Type*} [Group G] {n : ℕ} [NeZero n]

@[expose] noncomputable def dihHom (a b : G) (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) : DihedralGroup n →* G where
  toFun x := match x with
    | r i => a ^ i.val
    | sr i => b * a ^ i.val
  map_one' := by
    show a ^ (0 : ZMod n).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' x y := by
    have hmod : ∀ m : ℕ, a ^ m = a ^ (m % n) := fun m => pow_eq_pow_mod m ha
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hconj : ∀ m : ℕ, b * a ^ m * b = (a ^ m)⁻¹ := by
      intro m
      have h1 : (b * a * b⁻¹) ^ m = b * a ^ m * b⁻¹ := conj_pow
      rw [hba, inv_pow, hb'] at h1
      exact h1.symm
    have hsub : ∀ i j : ZMod n, a ^ (j - i).val = a ^ j.val * (a ^ i.val)⁻¹ := by
      intro i j
      have h1 : a ^ (j - i).val * a ^ i.val = a ^ j.val := by
        rw [← pow_add, hmod, ← ZMod.val_add, sub_add_cancel]
      rw [← h1, mul_inv_cancel_right]
    have hcomm : ∀ i j : ℕ, (a ^ i)⁻¹ * a ^ j = a ^ j * (a ^ i)⁻¹ := fun i j =>
      (Commute.inv_left (Commute.pow_pow_self a i j)).eq
    have hkey : ∀ i : ℕ, a ^ i * b = b * (a ^ i)⁻¹ := by
      intro i
      calc a ^ i * b = b * (b * a ^ i * b) := by rw [← mul_assoc, ← mul_assoc, hb, one_mul]
        _ = b * (a ^ i)⁻¹ := by rw [hconj]
    rcases x with i | i <;> rcases y with j | j
    · rw [r_mul_r]
      show a ^ (i + j).val = a ^ i.val * a ^ j.val
      rw [ZMod.val_add, ← hmod, pow_add]
    · rw [r_mul_sr]
      show b * a ^ (j - i).val = a ^ i.val * (b * a ^ j.val)
      rw [hsub]
      calc b * (a ^ j.val * (a ^ i.val)⁻¹) = b * ((a ^ i.val)⁻¹ * a ^ j.val) := by
            rw [hcomm]
        _ = (a ^ i.val * b) * a ^ j.val := by rw [hkey, mul_assoc]
        _ = a ^ i.val * (b * a ^ j.val) := by rw [mul_assoc]
    · rw [sr_mul_r]
      show b * a ^ (i + j).val = b * a ^ i.val * a ^ j.val
      rw [ZMod.val_add, ← hmod, pow_add, mul_assoc]
    · rw [sr_mul_sr]
      show a ^ (j - i).val = b * a ^ i.val * (b * a ^ j.val)
      rw [hsub]
      calc a ^ j.val * (a ^ i.val)⁻¹ = (b * b) * ((a ^ i.val)⁻¹ * a ^ j.val) := by
            rw [hb, one_mul, hcomm]
        _ = b * (b * (a ^ i.val)⁻¹) * a ^ j.val := by simp only [mul_assoc]
        _ = b * (a ^ i.val * b) * a ^ j.val := by rw [hkey]
        _ = b * a ^ i.val * (b * a ^ j.val) := by simp only [mul_assoc]

theorem dihHom_r (a b : G) (ha : a ^ n = 1) (hb : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹)
    (i : ZMod n) : dihHom a b ha hb hba (r i) = a ^ i.val := rfl

theorem dihHom_sr (a b : G) (ha : a ^ n = 1) (hb : b * b = 1) (hba : b * a * b⁻¹ = a⁻¹)
    (i : ZMod n) : dihHom a b ha hb hba (sr i) = b * a ^ i.val := rfl

theorem dihHom_injective {a b : G} (ha : a ^ n = 1) (hb : b * b = 1)
    (hba : b * a * b⁻¹ = a⁻¹) (hao : orderOf a = n) (hb1 : ∀ m : ℕ, b * a ^ m ≠ 1) :
    Function.Injective (dihHom a b ha hb hba) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rcases x with i | i
  · rw [dihHom_r] at hx
    have h1 := orderOf_dvd_of_pow_eq_one hx
    rw [hao] at h1
    have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [ZMod.val_eq_zero] at h0
    rw [h0]
    rfl
  · rw [dihHom_sr] at hx
    exact absurd hx (hb1 _)

end Hom

section Center

variable {m : ℕ}

theorem two_pow_facts (hm : 2 ≤ m) : Even (2 ^ m) ∧ 2 ^ m ≠ 2 ∧ 2 ^ m / 2 = 2 ^ (m - 1) := by
  refine ⟨(Nat.even_pow' (by omega)).mpr even_two, ?_, ?_⟩
  · intro h
    have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
    omega
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]

theorem mem_center_dih (hm : 2 ≤ m) (x : DihedralGroup (2 ^ m)) :
    x ∈ Subgroup.center (DihedralGroup (2 ^ m)) ↔
      x = 1 ∨ x = r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
  obtain ⟨he, hn2, hdiv⟩ := two_pow_facts hm
  rw [DihedralGroup.center_eq_closure_of_even_ne_two he hn2, hdiv, Subgroup.mem_zpowers_iff]
  have hsq : (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) ^ 2 = 1 := by
    rw [r_pow, one_def]
    congr 1
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← Int.mul_ediv_add_emod k 2, h, add_zero, zpow_mul, zpow_ofNat, hsq, one_zpow]
    · right
      rw [← Int.mul_ediv_add_emod k 2, h, zpow_add, zpow_mul, zpow_ofNat, hsq, one_zpow, one_mul,
        zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

theorem val_two_zmod (hm : 2 ≤ m) : (2 : ZMod (2 ^ m)).val = 2 := by
  have : (2 : ℕ) < 2 ^ m := by
    have : 2 ^ m ≥ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have h := ZMod.val_natCast (n := 2 ^ m) 2
  rw [Nat.mod_eq_of_lt this] at h
  exact_mod_cast h

theorem card_zpowers_r_two (hm : 2 ≤ m) :
    Nat.card (Subgroup.zpowers (r 2 : DihedralGroup (2 ^ m))) = 2 ^ (m - 1) := by
  rw [Nat.card_zpowers, DihedralGroup.orderOf_r, val_two_zmod hm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by norm_num)]

theorem mem_zpowers_r_two (hm : 2 ≤ m) (x : DihedralGroup (2 ^ m)) :
    x ∈ Subgroup.zpowers (r 2) ↔ ∃ j : ZMod (2 ^ m), Even j.val ∧ x = r j := by
  rw [Subgroup.mem_zpowers_iff]
  have hval : ∀ j : ZMod (2 ^ m), (j.val : ZMod (2 ^ m)) = j := ZMod.natCast_zmod_val
  constructor
  · rintro ⟨k, rfl⟩
    rw [r_zpow]
    refine ⟨2 * (k : ZMod (2 ^ m)), ?_, by rw [mul_comm]⟩
    obtain ⟨c, rfl⟩ : ∃ c, m = c + 1 := ⟨m - 1, by omega⟩
    have hdvd : 2 ∣ 2 ^ (c + 1) := dvd_pow_self 2 (by omega)
    rw [ZMod.val_mul, Nat.even_iff, Nat.mod_mod_of_dvd _ hdvd, Nat.mul_mod, val_two_zmod hm]
    simp
  · rintro ⟨j, ⟨c, hc⟩, rfl⟩
    refine ⟨(c : ℤ), ?_⟩
    rw [r_zpow]
    congr 1
    rw [← hval j, hc, Int.cast_natCast, Nat.cast_add]
    ring

abbrev cc (m : ℕ) : ZMod (2 ^ m) := ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))

theorem r_cc_central (hm : 2 ≤ m) (x : DihedralGroup (2 ^ m)) : r (cc m) * x = x * r (cc m) := by
  have h := (mem_center_dih hm (r (cc m))).mpr (Or.inr rfl)
  exact ((Subgroup.mem_center_iff.mp h) x).symm

theorem r_cc_sq (hm : 2 ≤ m) : (r (cc m) : DihedralGroup (2 ^ m)) * r (cc m) = 1 := by
  rw [r_mul_r, one_def]
  congr 1
  rw [cc, ← Nat.cast_add, ZMod.natCast_eq_zero_iff, ← two_mul]
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ, mul_comm]

theorem r_cc_ne (hm : 2 ≤ m) : (r (cc m) : DihedralGroup (2 ^ m)) ≠ 1 := by
  rw [one_def]
  intro h
  have h1 := r.inj h
  rw [cc, ZMod.natCast_eq_zero_iff] at h1
  have h2 : 0 < 2 ^ (m - 1) := pow_pos two_pos _
  have h3 := Nat.le_of_dvd h2 h1
  have h4 : 2 ^ (m - 1) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem val_cc (hm : 2 ≤ m) : (cc m).val = 2 ^ (m - 1) := by
  rw [cc, ZMod.val_natCast, Nat.mod_eq_of_lt]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end Center

end CFSG.ComponentClassification.GSThmB.P29
