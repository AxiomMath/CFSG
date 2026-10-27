module

public import CFSG.LocalAnalysis.Mason73.Elements
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic.LinearCombination
public import CFSG.LocalAnalysis.Mason73.Abelian

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup

section Recognition

variable {G : Type*} [Group G] {m : ℕ} [NeZero m] {r j : G}

theorem pow_val_add (hr : orderOf r = 2 * m) (i k : ZMod (2 * m)) :
    r ^ (i + k).val = r ^ i.val * r ^ k.val := by
  rw [ZMod.val_add, ← pow_add]
  have h := pow_mod_orderOf r (i.val + k.val)
  rw [hr] at h
  exact h

theorem pow_val_sub (hr : orderOf r = 2 * m) (i k : ZMod (2 * m)) :
    r ^ (k - i).val = (r ^ i.val)⁻¹ * r ^ k.val := by
  rw [eq_inv_mul_iff_mul_eq, ← pow_val_add hr, add_sub_cancel]

theorem pow_mul_eq_mul_inv (hj : j * r * j⁻¹ = r⁻¹) (k : ℕ) : r ^ k * j = j * (r ^ k)⁻¹ := by
  have h1 : j * r ^ k * j⁻¹ = (r ^ k)⁻¹ := by rw [← conj_pow, hj, inv_pow]
  have h2 : j * (r ^ k)⁻¹ * j⁻¹ = r ^ k := by
    rw [show j * (r ^ k)⁻¹ * j⁻¹ = (j * r ^ k * j⁻¹)⁻¹ by group, h1, inv_inv]
  calc r ^ k * j = j * (r ^ k)⁻¹ * j⁻¹ * j := by rw [h2]
    _ = j * (r ^ k)⁻¹ := by group

@[expose] def quatHom (hr : orderOf r = 2 * m) (hjj : j * j = r ^ m)
    (hj : j * r * j⁻¹ = r⁻¹) : QuaternionGroup m →* G where
  toFun
    | .a i => r ^ i.val
    | .xa i => j * r ^ i.val
  map_one' := by
    change r ^ (0 : ZMod (2 * m)).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rcases x with i | i <;> rcases y with k | k
    · change r ^ (i + k).val = r ^ i.val * r ^ k.val
      exact pow_val_add hr i k
    · change j * r ^ (k - i).val = r ^ i.val * (j * r ^ k.val)
      rw [pow_val_sub hr, ← mul_assoc (r ^ i.val), pow_mul_eq_mul_inv hj]
      group
    · change j * r ^ (i + k).val = j * r ^ i.val * r ^ k.val
      rw [pow_val_add hr, mul_assoc]
    · change r ^ ((m : ZMod (2 * m)) + k - i).val = j * r ^ i.val * (j * r ^ k.val)
      have hm : r ^ ((m : ZMod (2 * m))).val = r ^ m := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by have := NeZero.pos m; omega)]
      rw [add_sub_assoc, pow_val_add hr, hm, pow_val_sub hr, ← hjj]
      calc j * j * ((r ^ i.val)⁻¹ * r ^ k.val) = j * (j * (r ^ i.val)⁻¹) * r ^ k.val := by group
        _ = j * (r ^ i.val * j) * r ^ k.val := by rw [pow_mul_eq_mul_inv hj]
        _ = j * r ^ i.val * (j * r ^ k.val) := by group

theorem quatHom_injective (hr : orderOf r = 2 * m) (hjj : j * j = r ^ m)
    (hj : j * r * j⁻¹ = r⁻¹) (hjr : j ∉ zpowers r) : Function.Injective (quatHom hr hjj hj) := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) hx
  · change r ^ i.val = 1 at hx
    have hdvd := orderOf_dvd_of_pow_eq_one hx
    rw [hr] at hdvd
    have hlt := ZMod.val_lt i
    have h0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    rw [ZMod.val_eq_zero] at h0
    rw [h0]
    rfl
  · change j * r ^ i.val = 1 at hx
    exfalso
    apply hjr
    rw [eq_inv_of_mul_eq_one_left hx]
    exact inv_mem (pow_mem (mem_zpowers r) _)

theorem range_quatHom (hr : orderOf r = 2 * m) (hjj : j * j = r ^ m)
    (hj : j * r * j⁻¹ = r⁻¹) (hm : 1 < 2 * m) : (quatHom hr hjj hj).range = closure {r, j} := by
  apply le_antisymm
  · rintro _ ⟨i | i, rfl⟩
    · exact pow_mem (subset_closure (by simp)) _
    · exact mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _)
  · rw [closure_le]
    rintro x (rfl | rfl)
    · refine ⟨.a 1, ?_⟩
      change x ^ (1 : ZMod (2 * m)).val = x
      rw [ZMod.val_one'' (by omega), pow_one]
    · refine ⟨.xa 0, ?_⟩
      change x * r ^ (0 : ZMod (2 * m)).val = x
      rw [ZMod.val_zero, pow_zero, mul_one]

theorem nonempty_closure_mulEquiv_quaternion (hr : orderOf r = 2 * m) (hjj : j * j = r ^ m)
    (hj : j * r * j⁻¹ = r⁻¹) (hjr : j ∉ zpowers r) (hm : 1 < 2 * m) :
    Nonempty (closure ({r, j} : Set G) ≃* QuaternionGroup m) :=
  ⟨((MonoidHom.ofInjective (quatHom_injective hr hjj hj hjr)).trans
    (MulEquiv.subgroupCongr (range_quatHom hr hjj hj hm))).symm⟩

end Recognition

variable {n : ℕ}

theorem detSum_nsmul {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) (k : ℕ) : detSum (k • d) 1 := by
  rw [detSum_one_iff] at h ⊢
  simp only [Pi.smul_apply, ← Finset.smul_sum, h, smul_zero]

theorem el_one_pow {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) (k : ℕ) :
    (el d 1 h) ^ k = el (k • d) 1 (detSum_nsmul h k) := by
  induction k with
  | zero =>
    rw [pow_zero, ← el_zero_one]
    congr 1
    simp
  | succ k ih =>
    rw [pow_succ, ih, el_mul]
    congr 1
    simp only [OneMemClass.coe_one, pv_one, succ_nsmul]

theorem detSum_neg {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) : detSum (-d) 1 := by
  rw [detSum_one_iff] at h ⊢
  simp [Finset.sum_neg_distrib, h]

theorem el_one_inv {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) :
    (el d 1 h)⁻¹ = el (-d) 1 (detSum_neg h) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  rw [el_mul, ← el_zero_one]
  congr 1
  simp only [OneMemClass.coe_one, pv_one, neg_add_cancel]

theorem el_one_eq_one_iff (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} (h : detSum d 1) :
    el d 1 h = 1 ↔ IsConst d := by
  rw [← el_zero_one, el_eq_el_iff hn]
  simp only [true_and, zero_sub, isConst_neg_iff]

abbrev s01 : Fin81.R0 := ⟨swap 0 1, by decide⟩
abbrev s23 : Fin81.R0 := ⟨swap 2 3, by decide⟩

theorem sgnH_swap (hn : 1 ≤ n) {π : Fin81.R0} (hπ : Perm.sign (π : Perm (Fin 4)) = -1) :
    sgnH (n := n) π = hh n := by
  rw [sgnH, hπ, signZ_neg_one, toAdd_ofAdd]

theorem sgnH_s01 (hn : 1 ≤ n) : sgnH (n := n) s01 = hh n :=
  sgnH_swap hn (Perm.sign_swap (by decide))

theorem sgnH_s23 (hn : 1 ≤ n) : sgnH (n := n) s23 = hh n :=
  sgnH_swap hn (Perm.sign_swap (by decide))

theorem detSum_hv_odd (hn : 1 ≤ n) {χ : Fin 4 → ℕ} {π : Fin81.R0} (hπ : sgnH (n := n) π = hh n)
    (hχ : (χ 0 + χ 1 + χ 2 + χ 3) % 2 = 1) : detSum (hv n χ) π := by
  rw [detSum, sum_hv_four, hπ]
  have h1 := (hh_mul_natCast_eq_iff hn (χ 0 + χ 1 + χ 2 + χ 3) 1).2 (by omega)
  rw [h1, Nat.cast_one, mul_one, hh_add_hh hn]

abbrev v1 (n : ℕ) : Fin 4 → ZMod (2 ^ n) := ![1, -1, 0, 0]
abbrev v2 (n : ℕ) : Fin 4 → ZMod (2 ^ n) := ![0, 0, 1, -1]

theorem detSum_v1 : detSum (v1 n) 1 := by
  rw [detSum_one_iff, Fin.sum_univ_four]
  simp

theorem detSum_v2 : detSum (v2 n) 1 := by
  rw [detSum_one_iff, Fin.sum_univ_four]
  simp

@[expose] def r1T (n : ℕ) : L4Model n := el (v1 n) 1 detSum_v1
@[expose] def r2T (n : ℕ) : L4Model n := el (v2 n) 1 detSum_v2

@[expose] def j1T (hn : 1 ≤ n) : L4Model n :=
  el (hv n ![1, 0, 0, 0]) s01 (detSum_hv_odd hn (sgnH_s01 hn) (by decide))
@[expose] def j2T (hn : 1 ≤ n) : L4Model n :=
  el (hv n ![0, 0, 1, 0]) s23 (detSum_hv_odd hn (sgnH_s23 hn) (by decide))

theorem natCast_two_pow_ne_zero (hn : 1 ≤ n) : ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by positivity) h
  have h2 : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem orderOf_r1T (hn : 2 ≤ n) : orderOf (r1T n) = 2 ^ n := by
  have key : ∀ k : ℕ, (r1T n) ^ k = 1 ↔ ((k : ℕ) : ZMod (2 ^ n)) = 0 := by
    intro k
    rw [r1T, el_one_pow, el_one_eq_one_iff hn]
    constructor
    · intro hc
      have := hc 0 2
      simpa using this
    · intro hk i j
      fin_cases i <;> fin_cases j <;> simp [hk]
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 1) (x := r1T n)
    (by rw [key]; exact natCast_two_pow_ne_zero (by omega))
    (by rw [key, show n - 1 + 1 = n by omega]; exact ZMod.natCast_self _)
  rwa [show n - 1 + 1 = n by omega] at h

@[expose] def iv (n : ℕ) (κ : Fin 4 → ℤ) : Fin 4 → ZMod (2 ^ n) := fun i => (κ i : ZMod (2 ^ n))

theorem iv_sub (κ κ' : Fin 4 → ℤ) : iv n κ - iv n κ' = iv n (κ - κ') := by
  funext i
  simp [iv]

theorem neg_iv_sub_iv (κ κ' : Fin 4 → ℤ) : -iv n κ - iv n κ' = iv n (-κ - κ') := by
  funext i
  simp [iv]

theorem pv_iv (π : Perm (Fin 4)) (κ : Fin 4 → ℤ) : pv π (iv n κ) = iv n (fun i => κ (π⁻¹ i)) :=
  rfl

theorem isConst_iv {κ : Fin 4 → ℤ} (hκ : ∀ i j, κ i = κ j) : IsConst (iv n κ) := by
  intro i j
  simp [iv, hκ i j]

theorem v1_eq : v1 n = iv n ![1, -1, 0, 0] := by
  funext i
  fin_cases i <;> simp [iv]

theorem v2_eq : v2 n = iv n ![0, 0, 1, -1] := by
  funext i
  fin_cases i <;> simp [iv]

theorem s01_mul_s01 : s01 * s01 = 1 := Subtype.ext (by decide)
theorem s23_mul_s23 : s23 * s23 = 1 := Subtype.ext (by decide)

theorem j1T_sq (hn : 2 ≤ n) : j1T (n := n) (by omega) * j1T (by omega) = zT (by omega) := by
  rw [j1T, zT, el_mul, el_eq_el_iff hn, pv_hv, hv_add]
  refine ⟨s01_mul_s01, ?_⟩
  rw [hv_sub_hv_isConst_iff (by omega)]
  decide

theorem j2T_sq (hn : 2 ≤ n) : j2T (n := n) (by omega) * j2T (by omega) = zT (by omega) := by
  rw [j2T, zT, el_mul, el_eq_el_iff hn, pv_hv, hv_add]
  refine ⟨s23_mul_s23, ?_⟩
  rw [hv_sub_hv_isConst_iff (by omega)]
  decide

theorem r1T_pow (hn : 2 ≤ n) : r1T n ^ 2 ^ (n - 1) = zT (by omega) := by
  rw [r1T, el_one_pow, zT, el_eq_el_iff hn]
  refine ⟨rfl, ?_⟩
  have h2 : (2 : ZMod (2 ^ n)) * 2 ^ (n - 1) = 0 := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
    exact_mod_cast ZMod.natCast_self (2 ^ n)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hv, v1, hh] <;>
    first | linear_combination | linear_combination h2 | linear_combination (-1) * h2 |
      linear_combination 2 * h2 | linear_combination (-2) * h2

theorem r2T_pow (hn : 2 ≤ n) : r2T n ^ 2 ^ (n - 1) = zT (by omega) := by
  rw [r2T, el_one_pow, zT, el_eq_el_iff hn]
  refine ⟨rfl, ?_⟩
  have h2 : (2 : ZMod (2 ^ n)) * 2 ^ (n - 1) = 0 := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
    exact_mod_cast ZMod.natCast_self (2 ^ n)
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hv, v2, hh] <;>
    first | linear_combination | linear_combination h2 | linear_combination (-1) * h2 |
      linear_combination 2 * h2 | linear_combination (-2) * h2

theorem j1T_mul_r1T (hn : 2 ≤ n) :
    j1T (n := n) (by omega) * r1T n = (r1T n)⁻¹ * j1T (by omega) := by
  rw [j1T, r1T, el_one_inv, el_mul, el_mul, el_eq_el_iff hn]
  refine ⟨by rw [mul_one, one_mul], ?_⟩
  rw [OneMemClass.coe_one, pv_one,
    show -v1 n + hv n ![1, 0, 0, 0] - (hv n ![1, 0, 0, 0] + pv (s01 : Perm (Fin 4)) (v1 n)) =
      -v1 n - pv (s01 : Perm (Fin 4)) (v1 n) by abel,
    v1_eq, pv_iv, neg_iv_sub_iv]
  exact isConst_iv (by decide)

theorem j2T_mul_r2T (hn : 2 ≤ n) :
    j2T (n := n) (by omega) * r2T n = (r2T n)⁻¹ * j2T (by omega) := by
  rw [j2T, r2T, el_one_inv, el_mul, el_mul, el_eq_el_iff hn]
  refine ⟨by rw [mul_one, one_mul], ?_⟩
  rw [OneMemClass.coe_one, pv_one,
    show -v2 n + hv n ![0, 0, 1, 0] - (hv n ![0, 0, 1, 0] + pv (s23 : Perm (Fin 4)) (v2 n)) =
      -v2 n - pv (s23 : Perm (Fin 4)) (v2 n) by abel,
    v2_eq, pv_iv, neg_iv_sub_iv]
  exact isConst_iv (by decide)

theorem conj_of_mul_eq {G : Type*} [Group G] {r j : G} (h : j * r = r⁻¹ * j) :
    j * r * j⁻¹ = r⁻¹ := by
  rw [h, mul_inv_cancel_right]

theorem j1T_not_mem (hn : 1 ≤ n) : j1T (n := n) hn ∉ zpowers (r1T n) := by
  intro h
  have hA : zpowers (r1T n) ≤ A n := zpowers_le.2 (mem_A_of_one _)
  have := (el_mem_A _).1 (hA h)
  exact absurd (congrArg Subtype.val this) (by decide)

theorem j2T_not_mem (hn : 1 ≤ n) : j2T (n := n) hn ∉ zpowers (r2T n) := by
  intro h
  have hA : zpowers (r2T n) ≤ A n := zpowers_le.2 (mem_A_of_one _)
  have := (el_mem_A _).1 (hA h)
  exact absurd (congrArg Subtype.val this) (by decide)

instance neZero_two_pow_pred : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩

theorem two_mul_two_pow_pred (hn : 1 ≤ n) : 2 * 2 ^ (n - 1) = 2 ^ n := by
  rw [← pow_succ']
  congr 1
  omega

theorem nonempty_Q1_mulEquiv (hn : 2 ≤ n) :
    Nonempty (closure ({r1T n, j1T (by omega)} : Set (L4Model n)) ≃*
      QuaternionGroup (2 ^ (n - 1))) :=
  nonempty_closure_mulEquiv_quaternion (by rw [orderOf_r1T hn, two_mul_two_pow_pred (by omega)])
    (by rw [j1T_sq hn, r1T_pow hn]) (conj_of_mul_eq (j1T_mul_r1T hn)) (j1T_not_mem _)
    (by rw [two_mul_two_pow_pred (by omega)]; exact Nat.one_lt_two_pow (by omega))

theorem orderOf_r2T (hn : 2 ≤ n) : orderOf (r2T n) = 2 ^ n := by
  have key : ∀ k : ℕ, (r2T n) ^ k = 1 ↔ ((k : ℕ) : ZMod (2 ^ n)) = 0 := by
    intro k
    rw [r2T, el_one_pow, el_one_eq_one_iff hn]
    constructor
    · intro hc
      have := hc 2 0
      simpa using this
    · intro hk i j
      fin_cases i <;> fin_cases j <;> simp [hk]
  have h := orderOf_eq_prime_pow (p := 2) (n := n - 1) (x := r2T n)
    (by rw [key]; exact natCast_two_pow_ne_zero (by omega))
    (by rw [key, show n - 1 + 1 = n by omega]; exact ZMod.natCast_self _)
  rwa [show n - 1 + 1 = n by omega] at h

theorem nonempty_Q2_mulEquiv (hn : 2 ≤ n) :
    Nonempty (closure ({r2T n, j2T (by omega)} : Set (L4Model n)) ≃*
      QuaternionGroup (2 ^ (n - 1))) :=
  nonempty_closure_mulEquiv_quaternion (by rw [orderOf_r2T hn, two_mul_two_pow_pred (by omega)])
    (by rw [j2T_sq hn, r2T_pow hn]) (conj_of_mul_eq (j2T_mul_r2T hn)) (j2T_not_mem _)
    (by rw [two_mul_two_pow_pred (by omega)]; exact Nat.one_lt_two_pow (by omega))

abbrev Q1 (hn : 1 ≤ n) : Subgroup (L4Model n) := closure {r1T n, j1T hn}
abbrev Q2 (hn : 1 ≤ n) : Subgroup (L4Model n) := closure {r2T n, j2T hn}

theorem closure_le_centralizer_closure {G : Type*} [Group G] {S S' : Set G}
    (h : ∀ a ∈ S, ∀ b ∈ S', b * a = a * b) : closure S ≤ centralizer (closure S') := by
  rw [closure_le]
  intro a ha
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro b hb
  have hle : closure S' ≤ centralizer {a} := by
    rw [closure_le]
    intro b' hb'
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact h a ha b' hb'
  exact mem_centralizer_singleton_iff.1 (hle hb)

theorem r1T_comm_j2T (hn : 2 ≤ n) : j2T (n := n) (by omega) * r1T n = r1T n * j2T (by omega) := by
  rw [j2T, r1T, el_comm_diag_iff hn, v1_eq, pv_iv, iv_sub]
  exact isConst_iv (by decide)

theorem r2T_comm_j1T (hn : 2 ≤ n) : j1T (n := n) (by omega) * r2T n = r2T n * j1T (by omega) := by
  rw [j1T, r2T, el_comm_diag_iff hn, v2_eq, pv_iv, iv_sub]
  exact isConst_iv (by decide)

theorem j1T_comm_j2T (hn : 2 ≤ n) :
    j2T (n := n) (by omega) * j1T (by omega) = j1T (by omega) * j2T (by omega) := by
  rw [j1T, j2T, el_mul, el_mul, el_eq_el_iff hn, pv_hv, pv_hv, hv_add, hv_add]
  refine ⟨Subtype.ext (by decide), ?_⟩
  rw [hv_sub_hv_isConst_iff (by omega)]
  decide

theorem Q2_le_centralizer_Q1 (hn : 2 ≤ n) :
    Q2 (n := n) (by omega) ≤ centralizer ((Q1 (n := n) (by omega) : Subgroup (L4Model n)) :
      Set (L4Model n)) := by
  apply closure_le_centralizer_closure
  rintro a (rfl | rfl) b (rfl | rfl)
  · exact A_comm (mem_A_of_one _) (mem_A_of_one _)
  · exact r2T_comm_j1T hn
  · exact (r1T_comm_j2T hn).symm
  · exact (j1T_comm_j2T hn).symm

theorem mem_Q1_iff_exists (hn : 2 ≤ n) {x : L4Model n} (hx : x ∈ Q1 (n := n) (by omega)) :
    ∃ a : ℕ, x = r1T n ^ a ∨ x = j1T (by omega) * r1T n ^ a := by
  have hr : orderOf (r1T n) = 2 * 2 ^ (n - 1) := by
    rw [orderOf_r1T hn, two_mul_two_pow_pred (by omega)]
  rw [Q1, ← range_quatHom hr (by rw [j1T_sq hn, r1T_pow hn]) (conj_of_mul_eq (j1T_mul_r1T hn))
    (by rw [two_mul_two_pow_pred (by omega)]; exact Nat.one_lt_two_pow (by omega))] at hx
  obtain ⟨q, rfl⟩ := hx
  rcases q with i | i
  · exact ⟨i.val, Or.inl rfl⟩
  · exact ⟨i.val, Or.inr rfl⟩

theorem mem_Q2_iff_exists (hn : 2 ≤ n) {x : L4Model n} (hx : x ∈ Q2 (n := n) (by omega)) :
    ∃ a : ℕ, x = r2T n ^ a ∨ x = j2T (by omega) * r2T n ^ a := by
  have hr : orderOf (r2T n) = 2 * 2 ^ (n - 1) := by
    rw [orderOf_r2T hn, two_mul_two_pow_pred (by omega)]
  rw [Q2, ← range_quatHom hr (by rw [j2T_sq hn, r2T_pow hn]) (conj_of_mul_eq (j2T_mul_r2T hn))
    (by rw [two_mul_two_pow_pred (by omega)]; exact Nat.one_lt_two_pow (by omega))] at hx
  obtain ⟨q, rfl⟩ := hx
  rcases q with i | i
  · exact ⟨i.val, Or.inl rfl⟩
  · exact ⟨i.val, Or.inr rfl⟩

theorem piT_pow_r1T (a : ℕ) : piT (r1T n ^ a) = 1 := by
  rw [map_pow, r1T, piT_el, one_pow]

theorem piT_pow_r2T (a : ℕ) : piT (r2T n ^ a) = 1 := by
  rw [map_pow, r2T, piT_el, one_pow]

theorem mod_eq_of_two_mul_zero (hn : 1 ≤ n) {a : ℕ} (ha : ((2 * a : ℕ) : ZMod (2 ^ n)) = 0) :
    a % 2 ^ n = 0 ∨ a % 2 ^ n = 2 ^ (n - 1) := by
  rw [ZMod.natCast_eq_zero_iff] at ha
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := (two_mul_two_pow_pred hn).symm
  rw [h2] at ha
  obtain ⟨k, hk⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp ha
  subst hk
  rw [h2]
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [show 2 ^ (n - 1) * (j + j) = 2 * 2 ^ (n - 1) * j by ring, Nat.mul_mod_right]
  · right
    rw [show 2 ^ (n - 1) * (2 * j + 1) = 2 ^ (n - 1) + 2 * 2 ^ (n - 1) * j by ring,
      Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by have : 0 < 2 ^ (n - 1) := by positivity
                           omega)]

theorem Q1_inf_Q2 (hn : 2 ≤ n) :
    Q1 (n := n) (by omega) ⊓ Q2 (by omega) = zpowers (zT (by omega)) := by
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    obtain ⟨a, ha | ha⟩ := mem_Q1_iff_exists hn hx1 <;>
      obtain ⟨b, hb | hb⟩ := mem_Q2_iff_exists hn hx2
    ·
      have hab : r1T n ^ a = r2T n ^ b := ha.symm.trans hb
      rw [r1T, r2T, el_one_pow, el_one_pow, el_eq_el_iff hn] at hab
      have h01 := hab.2 0 1
      simp only [Pi.sub_apply, Pi.smul_apply, v1, v2] at h01
      have h2a : ((2 * a : ℕ) : ZMod (2 ^ n)) = 0 := by
        simp at h01
        push_cast
        linear_combination -h01
      rw [ha]
      rcases mod_eq_of_two_mul_zero (by omega) h2a with h0 | h0
      · rw [← pow_mod_orderOf (r1T n) a, orderOf_r1T hn, h0, pow_zero]
        exact one_mem _
      · rw [← pow_mod_orderOf (r1T n) a, orderOf_r1T hn, h0, r1T_pow hn]
        exact mem_zpowers _
    · exfalso
      have h1 := congrArg piT (ha.symm.trans hb)
      rw [piT_pow_r1T, map_mul, piT_pow_r2T, mul_one, j2T, piT_el] at h1
      exact absurd (congrArg Subtype.val h1) (by decide)
    · exfalso
      have h1 := congrArg piT (ha.symm.trans hb)
      rw [piT_pow_r2T, map_mul, piT_pow_r1T, mul_one, j1T, piT_el] at h1
      exact absurd (congrArg Subtype.val h1) (by decide)
    · exfalso
      have h1 := congrArg piT (ha.symm.trans hb)
      rw [map_mul, map_mul, piT_pow_r1T, piT_pow_r2T, mul_one, mul_one, j1T, j2T, piT_el,
        piT_el] at h1
      exact absurd (congrArg Subtype.val h1) (by decide)
  · rw [zpowers_le]
    refine ⟨?_, ?_⟩
    · rw [← j1T_sq hn]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
    · rw [← j2T_sq hn]
      exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))

end CFSG.LocalAnalysis.Mason73
