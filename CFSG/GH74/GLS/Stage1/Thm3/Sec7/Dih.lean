module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7.Dih

open DihedralGroup

variable {k : ℕ} [NeZero k]

theorem two_ne_zero_of_four_dvd (hk : 4 ∣ k) : (2 : ZMod k) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have hk0 : k ≠ 0 := NeZero.ne k
  have := Nat.le_of_dvd (by norm_num) h2
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hk
  omega

theorem eq_zero_or_half {i : ZMod k} (hk : 4 ∣ k) (h : 2 * i = 0) :
    i = 0 ∨ i = ((k / 2 : ℕ) : ZMod k) := by
  have hk0 : k ≠ 0 := NeZero.ne k
  have hv : i.val < k := ZMod.val_lt i
  have h1 : ((2 * i.val : ℕ) : ZMod k) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val]; exact h
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have hm2 : m = 0 ∨ m = 1 := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · omega
    · exfalso
      have : k * 2 ≤ k * m := Nat.mul_le_mul_left k hge
      omega
  rcases hm2 with rfl | rfl
  · left
    have : i.val = 0 := by omega
    rw [← ZMod.natCast_zmod_val i, this]; simp
  · right
    have : i.val = k / 2 := by omega
    rw [← ZMod.natCast_zmod_val i, this]

theorem half_add_half (hk : 4 ∣ k) :
    ((k / 2 : ℕ) : ZMod k) + ((k / 2 : ℕ) : ZMod k) = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [← Nat.cast_add, show 4 * m / 2 + 4 * m / 2 = 4 * m by omega, ZMod.natCast_self]

theorem quarter_add_quarter (hk : 4 ∣ k) :
    ((k / 4 : ℕ) : ZMod k) + ((k / 4 : ℕ) : ZMod k) = ((k / 2 : ℕ) : ZMod k) := by
  obtain ⟨m, rfl⟩ := hk
  rw [← Nat.cast_add]
  congr 1
  omega

theorem central_eq (hk : 4 ∣ k) {x : DihedralGroup k} (hx : ∀ y, y * x = x * y) (hx1 : x ≠ 1) :
    x = r ((k / 2 : ℕ) : ZMod k) := by
  cases x with
  | r i =>
    have h1 : i = -i := by
      have := hx (sr 0)
      simp at this
      exact this
    have h2 : 2 * i = 0 := by
      calc 2 * i = i - (-i) := by ring
        _ = 0 := by rw [← h1]; exact sub_self _
    rcases eq_zero_or_half hk h2 with h | h
    · exfalso
      apply hx1
      rw [h, DihedralGroup.one_def]
    · rw [h]
  | sr i =>
    exfalso
    have h1 : i - 1 = i + 1 := by
      have := hx (r 1)
      simp at this
      exact this
    apply two_ne_zero_of_four_dvd hk
    have h3 : (i + 1) - (i - 1) = 0 := by rw [← h1]; exact sub_self _
    calc (2 : ZMod k) = (i + 1) - (i - 1) := by ring
      _ = 0 := h3

theorem central_sq (hk : 4 ∣ k) : r ((k / 2 : ℕ) : ZMod k) = r ((k / 4 : ℕ) : ZMod k) * r ((k / 4 : ℕ) : ZMod k) := by
  rw [r_mul_r, quarter_add_quarter hk]

theorem half_central (hk : 4 ∣ k) (y : DihedralGroup k) :
    y * r ((k / 2 : ℕ) : ZMod k) = r ((k / 2 : ℕ) : ZMod k) * y := by
  have h := half_add_half hk
  cases y with
  | r j => simp [add_comm]
  | sr j =>
    simp only [sr_mul_r, r_mul_sr, sr.injEq]
    have : (((k / 2 : ℕ) : ZMod k)) = -((k / 2 : ℕ) : ZMod k) := by
      rw [eq_neg_iff_add_eq_zero]; exact h
    rw [sub_eq_add_neg, ← this]

theorem conj_noncentral (hk : 4 ∣ k) {a : DihedralGroup k} (ha : a * a = 1)
    (hnc : ∃ y, y * a ≠ a * y) :
    ∃ b, b * a * b⁻¹ = a * r ((k / 2 : ℕ) : ZMod k) := by
  cases a with
  | r i =>
    exfalso
    obtain ⟨y, hy⟩ := hnc
    have h1 : 2 * i = 0 := by
      have : r (i + i) = (1 : DihedralGroup k) := by rw [← r_mul_r]; exact ha
      rw [DihedralGroup.one_def] at this
      have h2 : i + i = 0 := DihedralGroup.r.inj this
      calc 2 * i = i + i := by ring
        _ = 0 := h2
    rcases eq_zero_or_half hk h1 with h | h
    · apply hy
      rw [h, ← DihedralGroup.one_def]; simp
    · apply hy
      rw [h]
      exact half_central hk y
  | sr j =>
    refine ⟨r ((k / 4 : ℕ) : ZMod k), ?_⟩
    have h := half_add_half hk
    have hq := quarter_add_quarter hk
    simp only [r_mul_sr, sr_mul_r, inv_r, sr.injEq]
    have e : ((k / 2 : ℕ) : ZMod k) = -((k / 2 : ℕ) : ZMod k) := by
      rw [eq_neg_iff_add_eq_zero]; exact h
    linear_combination (-1 : ZMod k) * hq - e

theorem dih_facts {G : Type*} [Group G] {V : Subgroup G} (hk : 4 ∣ k)
    (e : ↥V ≃* DihedralGroup k) {x : G} (hxV : x ∈ V) (hxc : ∀ a ∈ V, a * x = x * a)
    (hx1 : x ≠ 1) :
    (∃ a ∈ V, a * a = x) ∧
      (∀ a ∈ V, a * a = 1 → (∃ b ∈ V, b * a ≠ a * b) → ∃ h ∈ V, h * a * h⁻¹ = a * x) := by
  set x' : DihedralGroup k := e ⟨x, hxV⟩ with hx'
  have hxc' : ∀ y : DihedralGroup k, y * x' = x' * y := by
    intro y
    apply e.symm.injective
    rw [map_mul, map_mul, hx', MulEquiv.symm_apply_apply]
    exact Subtype.ext (hxc _ (e.symm y).2)
  have hx'1 : x' ≠ 1 := by
    intro h1
    apply hx1
    have := congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    simpa using this
  have hx'e : x' = r ((k / 2 : ℕ) : ZMod k) := central_eq hk hxc' hx'1
  refine ⟨⟨(e.symm (r ((k / 4 : ℕ) : ZMod k)) : G), (e.symm (r ((k / 4 : ℕ) : ZMod k))).2, ?_⟩, ?_⟩
  · have h1 : e.symm (r ((k / 4 : ℕ) : ZMod k)) * e.symm (r ((k / 4 : ℕ) : ZMod k)) =
        ⟨x, hxV⟩ := by
      rw [← map_mul, ← central_sq hk, ← hx'e, hx', MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h1
  · intro a haV ha hnc
    obtain ⟨b, hbV, hb⟩ := hnc
    set a' : DihedralGroup k := e ⟨a, haV⟩ with ha'
    have ha'2 : a' * a' = 1 := by
      rw [ha', ← map_mul]
      have : (⟨a, haV⟩ : ↥V) * ⟨a, haV⟩ = 1 := Subtype.ext (by simpa using ha)
      rw [this, map_one]
    have hnc' : ∃ y, y * a' ≠ a' * y := by
      refine ⟨e ⟨b, hbV⟩, fun hh => hb ?_⟩
      have h3 : (⟨b, hbV⟩ : ↥V) * ⟨a, haV⟩ = ⟨a, haV⟩ * ⟨b, hbV⟩ :=
        e.injective (by rw [map_mul, map_mul]; exact hh)
      exact congrArg Subtype.val h3
    obtain ⟨b', hb'⟩ := conj_noncentral hk ha'2 hnc'
    refine ⟨(e.symm b' : G), (e.symm b').2, ?_⟩
    have h2 : e.symm b' * ⟨a, haV⟩ * (e.symm b')⁻¹ = ⟨a, haV⟩ * ⟨x, hxV⟩ := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [← ha', ← hx', hb', hx'e]
    exact congrArg Subtype.val h2


theorem exists_invol_not_mem {G : Type*} [Group G] {D M : Subgroup G} {k : ℕ} (hk : 2 ≤ k)
    (e : ↥D ≃* DihedralGroup k) (hne : ¬ D ≤ M) : ∃ y ∈ D, y ∉ M ∧ orderOf y = 2 := by
  have : NeZero k := ⟨by omega⟩
  by_contra hcon
  push Not at hcon
  have hsr : ∀ i : ZMod k, ((e.symm (DihedralGroup.sr i) : ↥D) : G) ∈ M := by
    intro i
    by_contra hnot
    refine hcon _ (e.symm _).2 hnot ?_
    rw [Subgroup.orderOf_coe]
    simp [DihedralGroup.orderOf_sr]
  apply hne
  intro d hd
  rcases h : e ⟨d, hd⟩ with j | j
  · have h1 : (⟨d, hd⟩ : ↥D) = e.symm (DihedralGroup.sr 0) * e.symm (DihedralGroup.sr j) := by
      rw [← map_mul, DihedralGroup.sr_mul_sr, sub_zero, ← h, MulEquiv.symm_apply_apply]
    have h2 : d = ((e.symm (DihedralGroup.sr 0) : ↥D) : G) * ((e.symm (DihedralGroup.sr j) : ↥D) : G) :=
      congrArg Subtype.val h1
    rw [h2]
    exact M.mul_mem (hsr 0) (hsr j)
  · have h1 : (⟨d, hd⟩ : ↥D) = e.symm (DihedralGroup.sr j) := by
      rw [← h, MulEquiv.symm_apply_apply]
    have h2 : d = ((e.symm (DihedralGroup.sr j) : ↥D) : G) := congrArg Subtype.val h1
    rw [h2]
    exact hsr j

end CFSG.GH74.GLS.Stage1.Thm3.Sec7.Dih
