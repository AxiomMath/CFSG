module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.GH74.GLS.Stage4.Rest

section DihedralHom

variable {G : Type*} [Group G]

theorem t2H_dih_pow_val_add {c : G} {n : ℕ} [NeZero n] (hc : c ^ n = 1) (i j : ZMod n) :
    c ^ (i + j).val = c ^ i.val * c ^ j.val := by
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hc]

theorem t2H_dih_pow_val_zero {c : G} {n : ℕ} [NeZero n] : c ^ (0 : ZMod n).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

theorem t2H_dih_pow_val_neg {c : G} {n : ℕ} [NeZero n] (hc : c ^ n = 1) (i : ZMod n) :
    c ^ (-i).val = (c ^ i.val)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← t2H_dih_pow_val_add hc, neg_add_cancel, t2H_dih_pow_val_zero]

theorem t2H_dih_pow_val_sub {c : G} {n : ℕ} [NeZero n] (hc : c ^ n = 1) (i j : ZMod n) :
    c ^ (j - i).val = c ^ (-i).val * c ^ j.val := by
  rw [← t2H_dih_pow_val_add hc, neg_add_eq_sub]

theorem t2H_dih_conj_pow {c y : G} (hy : y * y = 1) (hyc : y * c * y = c⁻¹) (k : ℕ) :
    y * c ^ k * y = (c ^ k)⁻¹ := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h : (y * c * y⁻¹) ^ k = y * c ^ k * y⁻¹ := conj_pow
  rw [hyi, hyc, inv_pow] at h
  exact h.symm

@[expose] def t2H_dihHom {n : ℕ} [NeZero n] {c y : G} (hc : c ^ n = 1) (hy : y * y = 1)
    (hyc : y * c * y = c⁻¹) : DihedralGroup n →* G where
  toFun
    | .r i => c ^ i.val
    | .sr i => y * c ^ i.val
  map_one' := by
    rw [DihedralGroup.one_def]
    exact t2H_dih_pow_val_zero
  map_mul' := by
    have hcomm : ∀ i : ZMod n, c ^ i.val * y = y * c ^ (-i).val := by
      intro i
      rw [t2H_dih_pow_val_neg hc]
      calc c ^ i.val * y = y * (y * c ^ i.val * y) := by
            rw [← mul_assoc, ← mul_assoc, hy, one_mul]
        _ = y * (c ^ i.val)⁻¹ := by rw [t2H_dih_conj_pow hy hyc]
    rintro (i | i) (j | j)
    · simp only [DihedralGroup.r_mul_r]
      exact t2H_dih_pow_val_add hc i j
    · simp only [DihedralGroup.r_mul_sr]
      show y * c ^ (j - i).val = c ^ i.val * (y * c ^ j.val)
      rw [t2H_dih_pow_val_sub hc, ← mul_assoc (c ^ i.val), hcomm, mul_assoc]
    · simp only [DihedralGroup.sr_mul_r]
      show y * c ^ (i + j).val = y * c ^ i.val * c ^ j.val
      rw [t2H_dih_pow_val_add hc, mul_assoc]
    · simp only [DihedralGroup.sr_mul_sr]
      show c ^ (j - i).val = y * c ^ i.val * (y * c ^ j.val)
      rw [t2H_dih_pow_val_sub hc, t2H_dih_pow_val_neg hc, ← mul_assoc, t2H_dih_conj_pow hy hyc]

theorem t2H_dihHom_r {n : ℕ} [NeZero n] {c y : G} (hc : c ^ n = 1) (hy : y * y = 1)
    (hyc : y * c * y = c⁻¹) (i : ZMod n) :
    t2H_dihHom hc hy hyc (DihedralGroup.r i) = c ^ i.val := rfl

theorem t2H_dihHom_sr {n : ℕ} [NeZero n] {c y : G} (hc : c ^ n = 1) (hy : y * y = 1)
    (hyc : y * c * y = c⁻¹) (i : ZMod n) :
    t2H_dihHom hc hy hyc (DihedralGroup.sr i) = y * c ^ i.val := rfl

theorem t2H_dihHom_injective {n : ℕ} [NeZero n] {c y : G} (hc : c ^ n = 1) (hy : y * y = 1)
    (hyc : y * c * y = c⁻¹) (hord : orderOf c = n) (hyz : y ∉ Subgroup.zpowers c) :
    Function.Injective (t2H_dihHom hc hy hyc) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · rw [t2H_dihHom_r] at h
    have h1 : orderOf c ∣ i.val := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h1
    have h2 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt i)
    rw [DihedralGroup.one_def, (ZMod.val_eq_zero i).1 h2]
  · rw [t2H_dihHom_sr] at h
    exfalso
    apply hyz
    have h1 : y = (c ^ i.val)⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)

end DihedralHom

theorem t2H_dihedral_six {G : Type} [Group G] (a y w : G)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (hy2 : y ^ 2 = 1) (hw2 : w ^ 2 = 1) (hw1 : w ≠ 1)
    (hya : y * a * y⁻¹ = a⁻¹) (hwa : w * a = a * w) (hwy : w * y = y * w)
    (hyn : y ∉ Subgroup.closure ({a, w} : Set G)) :
    ∃ f : DihedralGroup 6 →* G, Function.Injective f ∧
      f.range = Subgroup.closure ({a, y, w} : Set G) ∧
      f (DihedralGroup.r 1) = a * w ∧ f (DihedralGroup.sr 0) = y := by
  have hy1 : y * y = 1 := by rw [← sq]; exact hy2
  have hw1' : w * w = 1 := by rw [← sq]; exact hw2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy1
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw1'
  have hac : Commute a w := hwa.symm
  have hwa' : Commute w a⁻¹ := Commute.inv_right hwa
  have hc6 : (a * w) ^ 6 = 1 := by
    rw [hac.mul_pow, show (6 : ℕ) = 3 * 2 from rfl, pow_mul, ha3, one_pow, pow_mul' w, hw2,
      one_pow, one_mul]
  have hord : orderOf (a * w) = 6 := by
    have h3 : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have h2 : orderOf w = 2 := orderOf_eq_prime hw2 hw1
    rw [hac.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [h3, h2]; decide), h3, h2]
  have hyc : y * (a * w) * y = (a * w)⁻¹ := by
    have h1 : y * a * y = a⁻¹ := by rw [hyi] at hya; exact hya
    calc y * (a * w) * y = y * a * (w * y) := by group
      _ = y * a * (y * w) := by rw [hwy]
      _ = (y * a * y) * w := by group
      _ = a⁻¹ * w := by rw [h1]
      _ = w * a⁻¹ := hwa'.symm.eq
      _ = (a * w)⁻¹ := by rw [mul_inv_rev, hwi]
  have hyz : y ∉ Subgroup.zpowers (a * w) := by
    intro h
    apply hyn
    have hle : Subgroup.zpowers (a * w) ≤ Subgroup.closure ({a, w} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    exact hle h
  refine ⟨t2H_dihHom hc6 hy1 hyc, t2H_dihHom_injective hc6 hy1 hyc hord hyz, ?_, ?_, ?_⟩
  · have ha4 : a ^ 4 = a := by rw [show 4 = 3 + 1 from rfl, pow_succ, ha3, one_mul]
    have hw4 : w ^ 4 = 1 := by rw [show 4 = 2 * 2 from rfl, pow_mul, hw2, one_pow]
    have hw3 : w ^ 3 = w := by rw [show 3 = 2 + 1 from rfl, pow_succ, hw2, one_mul]
    have hcmem : a * w ∈ Subgroup.closure ({a, y, w} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hymem : y ∈ Subgroup.closure ({a, y, w} : Set G) := Subgroup.subset_closure (by simp)
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rcases x with i | i
      · exact Subgroup.pow_mem _ hcmem _
      · exact Subgroup.mul_mem _ hymem (Subgroup.pow_mem _ hcmem _)
    · rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with h | h | h
      · rw [h]
        refine ⟨DihedralGroup.r 4, ?_⟩
        show (a * w) ^ (4 : ZMod 6).val = a
        rw [show (4 : ZMod 6).val = 4 from rfl, hac.mul_pow, ha4, hw4, mul_one]
      · rw [h]
        refine ⟨DihedralGroup.sr 0, ?_⟩
        show y * (a * w) ^ (0 : ZMod 6).val = y
        rw [ZMod.val_zero, pow_zero, mul_one]
      · rw [h]
        refine ⟨DihedralGroup.r 3, ?_⟩
        show (a * w) ^ (3 : ZMod 6).val = w
        rw [show (3 : ZMod 6).val = 3 from rfl, hac.mul_pow, ha3, hw3, one_mul]
  · show (a * w) ^ (1 : ZMod 6).val = a * w
    rw [show (1 : ZMod 6).val = 1 from rfl, pow_one]
  · show y * (a * w) ^ (0 : ZMod 6).val = y
    rw [ZMod.val_zero, pow_zero, mul_one]

end CFSG.GH74.GLS.Stage4.Rest
