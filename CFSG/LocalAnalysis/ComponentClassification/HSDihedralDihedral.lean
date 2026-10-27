module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.ComponentClassification.HSDihedral

open DihedralGroup

variable {n : ℕ}

theorem sr_ne_r (i j : ZMod n) : (sr i : DihedralGroup n) ≠ r j := fun h => by cases h

theorem commute_r_r (i j : ZMod n) : (r i : DihedralGroup n) * r j = r j * r i := by
  rw [r_mul_r, r_mul_r, add_comm]

theorem commute_r_sr_iff (i j : ZMod n) :
    (r j : DihedralGroup n) * sr i = sr i * r j ↔ 2 * j = 0 := by
  rw [r_mul_sr, sr_mul_r]
  constructor
  · intro h
    have h' := sr.inj h
    have : i - j - (i + j) = 0 := by rw [h', sub_self]
    have h2 : -(2 * j) = 0 := by
      rw [show -(2 * j) = i - j - (i + j) by ring]
      exact this
    exact neg_eq_zero.mp h2
  · intro h
    congr 1
    have : i - j = i + j - 2 * j := by ring
    rw [this, h, sub_zero]

theorem commute_sr_sr_iff (i j : ZMod n) :
    (sr j : DihedralGroup n) * sr i = sr i * sr j ↔ 2 * (j - i) = 0 := by
  rw [sr_mul_sr, sr_mul_sr]
  constructor
  · intro h
    have h' := r.inj h
    have : i - j - (j - i) = 0 := by rw [h', sub_self]
    rw [show 2 * (j - i) = -(i - j - (j - i)) by ring, this, neg_zero]
  · intro h
    congr 1
    have : i - j = -(2 * (j - i)) + (j - i) := by ring
    rw [this, h, neg_zero, zero_add]

theorem sr_sq (i : ZMod n) : (sr i : DihedralGroup n) ^ 2 = 1 := by
  rw [pow_two, sr_mul_self]

theorem r_sq_eq_one_iff (i : ZMod n) : (r i : DihedralGroup n) ^ 2 = 1 ↔ 2 * i = 0 := by
  rw [pow_two, r_mul_r, one_def]
  constructor
  · intro h
    have := r.inj h
    rw [← this]
    ring
  · intro h
    congr 1
    rw [← h]
    ring

theorem two_mul_eq_zero_iff (hn : Even n) (hn0 : n ≠ 0) (j : ZMod n) :
    2 * j = 0 ↔ j = 0 ∨ j = ((n / 2 : ℕ) : ZMod n) := by
  have : NeZero n := ⟨hn0⟩
  have h2k : 2 * (n / 2) = n := Nat.two_mul_div_two_of_even hn
  constructor
  · intro h
    have hv : n ∣ 2 * j.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      exact h
    have hlt := j.val_lt
    obtain ⟨c, hc⟩ := hv
    have hc2 : c < 2 := by
      by_contra hc2
      push Not at hc2
      have : n * 2 ≤ n * c := Nat.mul_le_mul_left n hc2
      omega
    interval_cases c
    · left
      have : j.val = 0 := by omega
      exact (ZMod.val_eq_zero j).mp this
    · right
      have : j.val = n / 2 := by omega
      rw [← ZMod.natCast_zmod_val j, this]
  · rintro (rfl | rfl)
    · rw [mul_zero]
    · rw [show (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = ((2 * (n / 2) : ℕ) : ZMod n) by
        push_cast; ring, h2k, ZMod.natCast_self]

theorem commute_sr_iff (hn : Even n) (hn0 : n ≠ 0) (i : ZMod n) (g : DihedralGroup n) :
    g * sr i = sr i * g ↔ g = 1 ∨ g = r ((n / 2 : ℕ) : ZMod n) ∨ g = sr i ∨
      g = sr (i + ((n / 2 : ℕ) : ZMod n)) := by
  rcases g with j | j
  · rw [commute_r_sr_iff, two_mul_eq_zero_iff hn hn0, one_def]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rintro (h | h | h | h)
      · exact Or.inl (r.inj h)
      · exact Or.inr (r.inj h)
      · exact absurd h (fun h' => by cases h')
      · exact absurd h (fun h' => by cases h')
  · rw [commute_sr_sr_iff, two_mul_eq_zero_iff hn hn0]
    constructor
    · rintro (h | h)
      · right; right; left
        rw [sub_eq_zero.mp h]
      · right; right; right
        rw [← h, add_sub_cancel]
    · rintro (h | h | h | h)
      · exact absurd h (fun h' => by cases h')
      · exact absurd h (fun h' => by cases h')
      · left
        rw [sr.inj h, sub_self]
      · right
        rw [sr.inj h, add_sub_cancel_left]

theorem r_sq_eq_one_iff' (hn : Even n) (hn0 : n ≠ 0) (j : ZMod n) :
    (r j : DihedralGroup n) ^ 2 = 1 ↔ j = 0 ∨ j = ((n / 2 : ℕ) : ZMod n) := by
  rw [r_sq_eq_one_iff, two_mul_eq_zero_iff hn hn0]

theorem r_eq_sr_mul_sr (j : ZMod n) : (r j : DihedralGroup n) = sr 0 * sr j := by
  rw [sr_mul_sr, sub_zero]

theorem eq_of_comm_mod_center (hn : Even n) (h8 : 8 ≤ n) (x : DihedralGroup n) (hx : x ^ 2 = 1)
    (hc : ∀ y : DihedralGroup n, x * y * x⁻¹ * y⁻¹ = 1 ∨
      x * y * x⁻¹ * y⁻¹ = r ((n / 2 : ℕ) : ZMod n)) :
    x = 1 ∨ x = r ((n / 2 : ℕ) : ZMod n) := by
  have hn0 : n ≠ 0 := by omega
  have : NeZero n := ⟨hn0⟩
  rcases x with j | i
  · rw [r_sq_eq_one_iff' hn hn0] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exfalso
    have h1 := hc (r 1)
    rw [inv_sr, inv_r, sr_mul_r, sr_mul_sr, r_mul_r] at h1
    have h2 : i - (i + 1) + -1 = ((n - 2 : ℕ) : ZMod n) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]
      ring
    rw [h2] at h1
    rcases h1 with h1 | h1
    · rw [one_def] at h1
      have h3 := r.inj h1
      rw [ZMod.natCast_eq_zero_iff] at h3
      have := Nat.le_of_dvd (by omega) h3
      omega
    · have h3 := r.inj h1
      have h4 : (((n - 2 : ℕ) + (n - n / 2) : ℕ) : ZMod n) = 0 := by
        push_cast [Nat.cast_sub (by omega : n / 2 ≤ n)]
        rw [h3, ZMod.natCast_self]
        ring
      rw [ZMod.natCast_eq_zero_iff] at h4
      obtain ⟨c, hc⟩ := h4
      have hhalf : n / 2 + n / 2 = n := by obtain ⟨m, rfl⟩ := hn; omega
      rcases Nat.lt_or_ge c 2 with hc2 | hc2
      · interval_cases c <;> omega
      · have : n * 2 ≤ n * c := Nat.mul_le_mul_left n hc2
        omega

theorem r_quarter_sq (h4 : 4 ∣ n) :
    (r ((n / 4 : ℕ) : ZMod n) : DihedralGroup n) ^ 2 = r ((n / 2 : ℕ) : ZMod n) := by
  rw [r_pow]
  congr 1
  obtain ⟨c, rfl⟩ := h4
  rw [show 4 * c / 4 = c by omega, show 4 * c / 2 = 2 * c by omega]
  push_cast
  ring

theorem r_half_ne_one (hn : Even n) (hn0 : n ≠ 0) :
    (r ((n / 2 : ℕ) : ZMod n) : DihedralGroup n) ≠ 1 := by
  rw [one_def]
  intro h
  have h' := r.inj h
  rw [ZMod.natCast_eq_zero_iff] at h'
  obtain ⟨m, rfl⟩ := hn
  have := Nat.le_of_dvd (by omega) h'
  omega

theorem card_le_of_forall_mem_finset {G : Type*} [Group G] (E : Subgroup G) (s : Finset G)
    (h : ∀ x ∈ E, x ∈ s) : Nat.card E ≤ s.card := by
  calc Nat.card E = (E : Set G).ncard := (Nat.card_coe_set_eq _)
    _ ≤ (s : Set G).ncard := Set.ncard_le_ncard (fun x hx => h x hx) s.finite_toSet
    _ = s.card := Set.ncard_coe_finset s

theorem card_le_four_of_sq (hn : Even n) (hn0 : n ≠ 0) (E : Subgroup (DihedralGroup n))
    (hsq : ∀ x ∈ E, x ^ 2 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    Nat.card E ≤ 4 := by
  classical
  by_cases hs : ∃ i, (sr i : DihedralGroup n) ∈ E
  · obtain ⟨i, hi⟩ := hs
    refine (card_le_of_forall_mem_finset E {1, r ((n / 2 : ℕ) : ZMod n), sr i,
      sr (i + ((n / 2 : ℕ) : ZMod n))} fun x hx => ?_).trans (Finset.card_le_four)
    have := (commute_sr_iff hn hn0 i x).mp (hcomm x hx _ hi)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact this
  · push Not at hs
    refine (card_le_of_forall_mem_finset E {1, r ((n / 2 : ℕ) : ZMod n)} fun x hx => ?_).trans
      ((Finset.card_le_two).trans (by norm_num))
    rcases x with j | i
    · have := (r_sq_eq_one_iff' hn hn0 j).mp (hsq _ hx)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases this with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · exact absurd hx (hs i)

end CFSG.ComponentClassification.HSDihedral
