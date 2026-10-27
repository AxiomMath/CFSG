module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Group

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem mem_inf_centralizer_iff_commute {H : Subgroup G} {g : G} :
    g ∈ H ⊓ Subgroup.centralizer (H : Set G) ↔ g ∈ H ∧ ∀ h ∈ H, Commute g h := by
  simp [Subgroup.mem_centralizer_iff, Commute, SemiconjBy, eq_comm]

theorem inf_centralizer_eq_map_center (H : Subgroup G) :
    H ⊓ Subgroup.centralizer (H : Set G) = (Subgroup.center H).map H.subtype := by
  ext g
  rw [mem_inf_centralizer_iff_commute]
  refine ⟨fun ⟨hg, hcomm⟩ => ⟨⟨g, hg⟩, Subgroup.mem_center_iff.mpr fun h =>
    Subtype.ext (hcomm h.1 h.2).symm, rfl⟩, ?_⟩
  rintro ⟨⟨z, hz⟩, hzc, rfl⟩
  exact ⟨hz, fun h hh => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨h, hh⟩)).symm⟩

theorem pow_mul_eq_mul_pow_mul_pow {a b z : G} (h : a * b = b * a * z) (hz : Commute z a)
    (k : ℕ) : a ^ k * b = b * a ^ k * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc a ^ (k + 1) * b = a * (a ^ k * b) := by group
      _ = a * (b * a ^ k * z ^ k) := by rw [ih]
      _ = (a * b) * (a ^ k * z ^ k) := by group
      _ = (b * a * z) * (a ^ k * z ^ k) := by rw [h]
      _ = b * a * (z * a ^ k) * z ^ k := by group
      _ = b * a * (a ^ k * z) * z ^ k := by rw [(hz.pow_right k).eq]
      _ = b * a ^ (k + 1) * z ^ (k + 1) := by group

theorem mul_pow_eq_pow_mul_mul_pow {a b z : G} (h : a * b = b * a * z) (hz : Commute z b)
    (k : ℕ) : a * b ^ k = b ^ k * a * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc a * b ^ (k + 1) = (a * b ^ k) * b := by group
      _ = (b ^ k * a * z ^ k) * b := by rw [ih]
      _ = b ^ k * a * (z ^ k * b) := by group
      _ = b ^ k * a * (b * z ^ k) := by rw [(hz.pow_left k).eq]
      _ = b ^ k * (a * b) * z ^ k := by group
      _ = b ^ k * (b * a * z) * z ^ k := by rw [h]
      _ = b ^ (k + 1) * a * z ^ (k + 1) := by group

theorem succ_choose_two (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ' n 1, Nat.choose_one_right]

theorem succ_choose_three (n : ℕ) : (n + 1).choose 3 = n.choose 2 + n.choose 3 := by
  rw [Nat.choose_succ_succ' n 2]

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 2
  rw [show n.descFactorial 2 = n * (n - 1) by simp [Nat.descFactorial, Nat.mul_comm]] at h
  simpa [Nat.factorial] using h.symm

theorem six_mul_choose_three (n : ℕ) : 6 * n.choose 3 = n * (n - 1) * (n - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose n 3
  rw [show n.descFactorial 3 = n * (n - 1) * (n - 2) by simp [Nat.descFactorial]; ring] at h
  simpa [Nat.factorial] using h.symm

theorem six_mul_two_mul_choose_three_add_choose_two (n : ℕ) :
    6 * (2 * n.choose 3 + n.choose 2) = n * (n - 1) * (2 * n - 1) := by
  calc 6 * (2 * n.choose 3 + n.choose 2) = 2 * (6 * n.choose 3) + 3 * (2 * n.choose 2) := by ring
    _ = 2 * (n * (n - 1) * (n - 2)) + 3 * (n * (n - 1)) := by
        rw [six_mul_choose_three, two_mul_choose_two]
    _ = n * (n - 1) * (2 * n - 1) := by
        match n with
        | 0 => simp
        | 1 => simp
        | (m + 2) =>
          rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
            show 2 * (m + 2) - 1 = 2 * m + 3 by omega]
          ring

theorem two_dvd_mul_sub_one (n : ℕ) : 2 ∣ n * (n - 1) :=
  ⟨n.choose 2, (two_mul_choose_two n).symm⟩

theorem six_dvd_mul_sub_one_mul_sub_two (n : ℕ) : 6 ∣ n * (n - 1) * (n - 2) :=
  ⟨n.choose 3, (six_mul_choose_three n).symm⟩

theorem six_dvd_mul_sub_one_mul_two_mul_sub_one (n : ℕ) : 6 ∣ n * (n - 1) * (2 * n - 1) :=
  ⟨2 * n.choose 3 + n.choose 2, (six_mul_two_mul_choose_three_add_choose_two n).symm⟩

theorem choose_two_eq_div (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by
  have h := two_mul_choose_two n; omega

theorem choose_three_eq_div (n : ℕ) : n.choose 3 = n * (n - 1) * (n - 2) / 6 := by
  have h := six_mul_choose_three n; omega

theorem two_mul_choose_three_add_choose_two_eq_div (n : ℕ) :
    2 * n.choose 3 + n.choose 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  have h := six_mul_two_mul_choose_three_add_choose_two n; omega

theorem pow_mul_of_relations {x y c e : G} (hyx : y * x = x * y * c)
    (hcy : c * y = y * c * e) (hey : Commute e y) (hec : Commute e c) (n : ℕ) :
    y ^ n * x = x * y ^ n * c ^ n * e ^ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc y ^ (n + 1) * x = y * (y ^ n * x) := by group
      _ = y * (x * y ^ n * c ^ n * e ^ n.choose 2) := by rw [ih]
      _ = (y * x) * (y ^ n * c ^ n * e ^ n.choose 2) := by group
      _ = (x * y * c) * (y ^ n * c ^ n * e ^ n.choose 2) := by rw [hyx]
      _ = x * y * (c * y ^ n) * (c ^ n * e ^ n.choose 2) := by group
      _ = x * y * (y ^ n * c * e ^ n) * (c ^ n * e ^ n.choose 2) := by
            rw [mul_pow_eq_pow_mul_mul_pow hcy hey n]
      _ = x * y ^ (n + 1) * c * (e ^ n * c ^ n) * e ^ n.choose 2 := by group
      _ = x * y ^ (n + 1) * c * (c ^ n * e ^ n) * e ^ n.choose 2 := by rw [(hec.pow_pow n n).eq]
      _ = x * y ^ (n + 1) * c ^ (n + 1) * e ^ (n + n.choose 2) := by group
      _ = x * y ^ (n + 1) * c ^ (n + 1) * e ^ ((n + 1).choose 2) := by rw [succ_choose_two]

theorem collection_step {x y c d e : G}
    (hyx : y * x = x * y * c) (hcx : c * x = x * c * d) (hcy : c * y = y * c * e)
    (hdy : Commute d y) (hdc : Commute d c) (hde : Commute d e)
    (hey : Commute e y) (hec : Commute e c) (n B : ℕ) :
    x ^ n * y ^ n * c ^ B * x * y
      = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + B) * d ^ B * e ^ (n + B + n.choose 2) := by
  calc x ^ n * y ^ n * c ^ B * x * y = x ^ n * y ^ n * (c ^ B * x) * y := by group
    _ = x ^ n * y ^ n * (x * c ^ B * d ^ B) * y := by rw [pow_mul_eq_mul_pow_mul_pow hcx hdc B]
    _ = x ^ n * (y ^ n * x) * c ^ B * (d ^ B * y) := by group
    _ = x ^ n * (x * y ^ n * c ^ n * e ^ n.choose 2) * c ^ B * (y * d ^ B) := by
          rw [pow_mul_of_relations hyx hcy hey hec n, (hdy.pow_left B).eq]
    _ = x ^ (n + 1) * y ^ n * c ^ n * (e ^ n.choose 2 * c ^ B) * (y * d ^ B) := by group
    _ = x ^ (n + 1) * y ^ n * c ^ n * (c ^ B * e ^ n.choose 2) * (y * d ^ B) := by
          rw [(hec.pow_pow _ _).eq]
    _ = x ^ (n + 1) * y ^ n * c ^ (n + B) * (e ^ n.choose 2 * y) * d ^ B := by group
    _ = x ^ (n + 1) * y ^ n * (c ^ (n + B) * y) * e ^ n.choose 2 * d ^ B := by
          rw [(hey.pow_left _).eq]; group
    _ = x ^ (n + 1) * y ^ n * (y * c ^ (n + B) * e ^ (n + B)) * e ^ n.choose 2 * d ^ B := by
          rw [pow_mul_eq_mul_pow_mul_pow hcy hec (n + B)]
    _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + B) * (e ^ (n + B + n.choose 2) * d ^ B) := by group
    _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + B) * (d ^ B * e ^ (n + B + n.choose 2)) := by
          rw [(hde.pow_pow _ _).symm.eq]
    _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + B) * d ^ B * e ^ (n + B + n.choose 2) := by group

theorem mul_pow_of_relations {x y c d e : G}
    (hyx : y * x = x * y * c) (hcx : c * x = x * c * d) (hcy : c * y = y * c * e)
    (hdx : Commute d x) (hdy : Commute d y) (hdc : Commute d c) (hde : Commute d e)
    (hex : Commute e x) (hey : Commute e y) (hec : Commute e c) (n : ℕ) :
    (x * y) ^ n
      = x ^ n * y ^ n * c ^ n.choose 2 * d ^ n.choose 3 * e ^ (2 * n.choose 3 + n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h2 : (n + 1).choose 2 = n + n.choose 2 := succ_choose_two n
    have h3 : (n + 1).choose 3 = n.choose 2 + n.choose 3 := succ_choose_three n
    have h4 : 2 * (n + 1).choose 3 + (n + 1).choose 2
        = n + n.choose 2 + n.choose 2 + (2 * n.choose 3 + n.choose 2) := by rw [h2, h3]; ring
    rw [h4, h3, h2]
    calc (x * y) ^ (n + 1) = (x * y) ^ n * (x * y) := pow_succ _ _
      _ = (x ^ n * y ^ n * c ^ n.choose 2 * d ^ n.choose 3
            * e ^ (2 * n.choose 3 + n.choose 2)) * (x * y) := by rw [ih]
      _ = (x ^ n * y ^ n * c ^ n.choose 2)
            * (d ^ n.choose 3 * (e ^ (2 * n.choose 3 + n.choose 2) * x) * y) := by group
      _ = (x ^ n * y ^ n * c ^ n.choose 2)
            * (d ^ n.choose 3 * (x * e ^ (2 * n.choose 3 + n.choose 2)) * y) := by
            rw [(hex.pow_left _).eq]
      _ = (x ^ n * y ^ n * c ^ n.choose 2)
            * ((d ^ n.choose 3 * x) * (e ^ (2 * n.choose 3 + n.choose 2) * y)) := by group
      _ = (x ^ n * y ^ n * c ^ n.choose 2)
            * ((x * d ^ n.choose 3) * (y * e ^ (2 * n.choose 3 + n.choose 2))) := by
            rw [(hdx.pow_left _).eq, (hey.pow_left _).eq]
      _ = (x ^ n * y ^ n * c ^ n.choose 2 * x) * (d ^ n.choose 3 * y)
            * e ^ (2 * n.choose 3 + n.choose 2) := by group
      _ = (x ^ n * y ^ n * c ^ n.choose 2 * x) * (y * d ^ n.choose 3)
            * e ^ (2 * n.choose 3 + n.choose 2) := by rw [(hdy.pow_left _).eq]
      _ = (x ^ n * y ^ n * c ^ n.choose 2 * x * y)
            * (d ^ n.choose 3 * e ^ (2 * n.choose 3 + n.choose 2)) := by group
      _ = (x ^ (n + 1) * y ^ (n + 1) * c ^ (n + n.choose 2) * d ^ n.choose 2
            * e ^ (n + n.choose 2 + n.choose 2))
            * (d ^ n.choose 3 * e ^ (2 * n.choose 3 + n.choose 2)) := by
            rw [collection_step hyx hcx hcy hdy hdc hde hey hec n (n.choose 2)]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + n.choose 2) * d ^ n.choose 2
            * (e ^ (n + n.choose 2 + n.choose 2) * d ^ n.choose 3)
            * e ^ (2 * n.choose 3 + n.choose 2) := by group
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + n.choose 2) * d ^ n.choose 2
            * (d ^ n.choose 3 * e ^ (n + n.choose 2 + n.choose 2))
            * e ^ (2 * n.choose 3 + n.choose 2) := by rw [(hde.pow_pow _ _).symm.eq]
      _ = x ^ (n + 1) * y ^ (n + 1) * c ^ (n + n.choose 2) * d ^ (n.choose 2 + n.choose 3)
            * e ^ (n + n.choose 2 + n.choose 2 + (2 * n.choose 3 + n.choose 2)) := by group

private theorem self_mem_closure_pair_left (x y : G) : x ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.subset_closure (by simp)

private theorem self_mem_closure_pair_right (x y : G) : y ∈ Subgroup.closure ({x, y} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem mul_pow_eq_of_triple_commutators_mem_center {x y c d e : G}
    (hc : c = y⁻¹ * x⁻¹ * y * x) (hd : d = c⁻¹ * x⁻¹ * c * x) (he : e = c⁻¹ * y⁻¹ * c * y)
    (hdZ : d ∈ Subgroup.closure ({x, y} : Set G) ⊓
      Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G))
    (heZ : e ∈ Subgroup.closure ({x, y} : Set G) ⊓
      Subgroup.centralizer (Subgroup.closure ({x, y} : Set G) : Set G))
    (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * c ^ (n * (n - 1) / 2) * d ^ (n * (n - 1) * (n - 2) / 6)
      * e ^ (n * (n - 1) * (2 * n - 1) / 6) := by
  obtain ⟨-, hdcomm⟩ := mem_inf_centralizer_iff_commute.mp hdZ
  obtain ⟨heH, hecomm⟩ := mem_inf_centralizer_iff_commute.mp heZ
  have hcH : c ∈ Subgroup.closure ({x, y} : Set G) := by
    subst hc
    exact mul_mem (mul_mem (mul_mem (inv_mem (self_mem_closure_pair_right x y))
      (inv_mem (self_mem_closure_pair_left x y))) (self_mem_closure_pair_right x y))
      (self_mem_closure_pair_left x y)
  rw [← choose_two_eq_div, ← choose_three_eq_div, ← two_mul_choose_three_add_choose_two_eq_div]
  exact mul_pow_of_relations (by subst hc; group) (by subst hd; group) (by subst he; group)
    (hdcomm x (self_mem_closure_pair_left x y)) (hdcomm y (self_mem_closure_pair_right x y))
    (hdcomm c hcH) (hdcomm e heH)
    (hecomm x (self_mem_closure_pair_left x y)) (hecomm y (self_mem_closure_pair_right x y))
    (hecomm c hcH) n

end CFSG.FeitThompson
