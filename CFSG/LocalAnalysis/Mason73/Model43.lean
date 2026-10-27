module

public import CFSG.LocalAnalysis.Mason73.Model36
public import CFSG.LocalAnalysis.Mason73.Model42
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv Subgroup
open scoped commutatorElement

variable {n : ℕ}

@[expose] noncomputable def psiT (g : L4Model n) : ZMod (2 ^ n) :=
  2 * ((exists_eq_el g).choose 2 + (exists_eq_el g).choose 3)

theorem two_mul_sgnH (hn : 1 ≤ n) (π : Fin81.R0) : 2 * sgnH (n := n) π = 0 := by
  rcases Int.units_eq_one_or (Perm.sign (π : Perm (Fin 4))) with h | h
  · rw [sgnH_even h, mul_zero]
  · rw [sgnH_swap hn h, two_mul_hh hn]

theorem psiT_el (hn : 2 ≤ n) {d : Fin 4 → ZMod (2 ^ n)} {π : Fin81.R0} (h : detSum d π) :
    psiT (el d π h) = 2 * (d 2 + d 3) := by
  obtain ⟨π', h', heq⟩ := (exists_eq_el (el d π h)).choose_spec
  rw [psiT]
  set d' := (exists_eq_el (el d π h)).choose with hd'
  obtain ⟨rfl, hc⟩ := (el_eq_el_iff hn h h').1 heq
  have hs : d' 0 + d' 1 + d' 2 + d' 3 = d 0 + d 1 + d 2 + d 3 := by
    rw [detSum, Fin.sum_univ_four] at h h'
    linear_combination h' - h
  have h1 := hc 0 1
  have h2 := hc 0 2
  have h3 := hc 0 3
  simp only [Pi.sub_apply] at h1 h2 h3
  linear_combination h1 - h2 - h3 + hs

theorem V1_pv_two_add_three : ∀ π ∈ (V1 : Subgroup Fin81.R0),
    ((π : Perm (Fin 4))⁻¹ 2 = 2 ∧ (π : Perm (Fin 4))⁻¹ 3 = 3) ∨
      ((π : Perm (Fin 4))⁻¹ 2 = 3 ∧ (π : Perm (Fin 4))⁻¹ 3 = 2) := by
  decide

theorem not_V1_pv_two_add_three : ∀ π : Fin81.R0, π ∉ V1 →
    ((π : Perm (Fin 4))⁻¹ 2 = 0 ∧ (π : Perm (Fin 4))⁻¹ 3 = 1) ∨
      ((π : Perm (Fin 4))⁻¹ 2 = 1 ∧ (π : Perm (Fin 4))⁻¹ 3 = 0) := by
  decide

theorem psiT_mul (hn : 2 ≤ n) {g : L4Model n} (hg : piT g ∈ V1) (g' : L4Model n) :
    psiT (g * g') = psiT g + psiT g' := by
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  obtain ⟨e, σ, h', rfl⟩ := exists_eq_el g'
  rw [piT_el] at hg
  rw [el_mul, psiT_el hn, psiT_el hn, psiT_el hn]
  simp only [Pi.add_apply, pv]
  rcases V1_pv_two_add_three π hg with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3] <;> ring

theorem psiT_mul_of_not_mem (hn : 2 ≤ n) {τ : L4Model n} (hτ : piT τ ∉ V1) (g : L4Model n) :
    psiT (τ * g) = psiT τ - psiT g := by
  obtain ⟨e, σ, h', rfl⟩ := exists_eq_el τ
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [piT_el] at hτ
  rw [el_mul, psiT_el hn, psiT_el hn, psiT_el hn]
  have hsum : 2 * (d 0 + d 1) = -(2 * (d 2 + d 3)) := by
    have hd : d 0 + d 1 + d 2 + d 3 + sgnH π = 0 := by
      rw [detSum, Fin.sum_univ_four] at h
      exact h
    linear_combination 2 * hd - two_mul_sgnH (n := n) (by omega) π
  simp only [Pi.add_apply, pv]
  rcases not_V1_pv_two_add_three σ hτ with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3] <;>
    linear_combination hsum

theorem psiT_one (hn : 2 ≤ n) : psiT (1 : L4Model n) = 0 := by
  rw [← el_zero_one, psiT_el hn]
  simp

theorem psiT_inv (hn : 2 ≤ n) {g : L4Model n} (hg : piT g ∈ V1) : psiT g⁻¹ = -psiT g := by
  have h := psiT_mul hn hg g⁻¹
  rw [mul_inv_cancel, psiT_one hn] at h
  linear_combination -h

theorem piT_conj_mem_V1 {τ g : L4Model n} (hg : piT g ∈ V1) : piT (τ * g * τ⁻¹) ∈ V1 := by
  have key : ∀ σ π : Fin81.R0, π ∈ V1 → σ * π * σ⁻¹ ∈ V1 := by
    decide
  rw [map_mul, map_mul, map_inv]
  exact key _ _ hg

theorem psiT_conj (hn : 2 ≤ n) (τ : L4Model n) {g : L4Model n} (hg : piT g ∈ V1) :
    psiT (τ * g * τ⁻¹) = psiT g ∨ psiT (τ * g * τ⁻¹) = -psiT g := by
  have hk := piT_conj_mem_V1 (τ := τ) hg
  have heq : τ * g * τ⁻¹ * τ = τ * g := by group
  have h1 := psiT_mul hn hk τ
  rw [heq] at h1
  by_cases hτ : piT τ ∈ V1
  · left
    rw [psiT_mul hn hτ g] at h1
    linear_combination -h1
  · right
    rw [psiT_mul_of_not_mem hn hτ g] at h1
    linear_combination -h1

theorem psiT_pow (hn : 2 ≤ n) {g : L4Model n} (hg : piT g ∈ V1) (k : ℕ) :
    psiT (g ^ k) = k • psiT g := by
  induction k with
  | zero => rw [pow_zero, psiT_one hn, zero_nsmul]
  | succ k ih => rw [pow_succ', psiT_mul hn hg, ih, succ_nsmul']

abbrev T1T (hn : 2 ≤ n) : Subgroup (L4Model n) := Q1T n ⊓ (xParity hn).ker

@[expose] noncomputable def T2T (hn : 2 ≤ n) : Subgroup (L4Model n) where
  carrier := {g | piT g ∈ V1 ∧ psiT g = 0}
  one_mem' := ⟨by rw [map_one]; exact one_mem _, psiT_one hn⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [map_mul]; exact mul_mem ha hb, by rw [psiT_mul hn ha, ha', hb', add_zero]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_inv]; exact inv_mem ha, by rw [psiT_inv hn ha, ha', neg_zero]⟩

theorem T2T_normal (hn : 2 ≤ n) (τ : L4Model n) {g : L4Model n} (hg : g ∈ T2T hn) :
    τ * g * τ⁻¹ ∈ T2T hn := by
  obtain ⟨hgV, hg0⟩ := hg
  refine ⟨piT_conj_mem_V1 hgV, ?_⟩
  rcases psiT_conj hn τ hgV with h | h <;> rw [h, hg0]
  exact neg_zero

theorem T2T_le_T1T (hn : 3 ≤ n) : T2T (n := n) (by omega) ≤ T1T (by omega) := by
  intro g ⟨hgV, hg0⟩
  refine ⟨hgV, ?_⟩
  obtain ⟨d, π, h, rfl⟩ := exists_eq_el g
  rw [psiT_el (by omega)] at hg0
  refine MonoidHom.mem_ker.2 ?_
  rw [xParity_el]
  obtain ⟨b, hb, hb'⟩ := exists_hh_of_two_mul (n := n) (by omega) hg0
  have hs := red2_sum_of_detSum (n := n) (by omega) h
  have h23 : red2 (n := n) (by omega) (d 2 + d 3) = 0 := by
    rw [hb', map_mul, red2_hh (by omega), zero_mul]
  have : red2 (n := n) (by omega) (d 0 + d 1) = 0 := by
    have heq : d 0 + d 1 = (d 0 + d 1 + d 2 + d 3) - (d 2 + d 3) := by ring
    rw [heq, map_sub, hs, h23, sub_zero]
  rw [this, ofAdd_zero]

theorem commutator_T1T_le_T2T (hn : 3 ≤ n) :
    ⁅T1T (n := n) (by omega), T1T (n := n) (by omega)⁆ ≤ T2T (n := n) (by omega) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haV : piT a ∈ V1 := ha.1
  have hbV : piT b ∈ V1 := hb.1
  have hcomm : ∀ σ τ : Fin81.R0, σ ∈ V1 → τ ∈ V1 → σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
    decide
  refine ⟨?_, ?_⟩
  · rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
      hcomm _ _ haV hbV]
    exact one_mem _
  · have h1 : piT (a * b * a⁻¹) ∈ V1 := by
      rw [map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem haV hbV) (inv_mem haV)
    have h2 : piT (a * b) ∈ V1 := by
      rw [map_mul]
      exact mul_mem haV hbV
    rw [commutatorElement_def, psiT_mul (by omega) h1, psiT_mul (by omega) h2,
      psiT_mul (by omega) haV, psiT_inv (by omega) haV, psiT_inv (by omega) hbV]
    ring

theorem mem_T1T_or (hn : 3 ≤ n) (g : L4Model n) :
    g ∈ T1T (n := n) (by omega) ∨ (xT n)⁻¹ * g ∈ T1T (by omega) ∨
      (tT (by omega))⁻¹ * g ∈ T1T (by omega) ∨ (txT n)⁻¹ * g ∈ T1T (by omega) := by
  have key : ∀ π : Fin81.R0, π ∉ V1 → tP⁻¹ * π ∈ V1 := by
    decide
  by_cases hV : piT g ∈ V1
  · by_cases hp : xParity (n := n) (by omega) g = 1
    · exact Or.inl ⟨hV, MonoidHom.mem_ker.2 hp⟩
    · refine Or.inr (Or.inl ⟨?_, MonoidHom.mem_ker.2 ?_⟩)
      · change piT ((xT n)⁻¹ * g) ∈ V1
        rw [map_mul, map_inv, mem_A_iff.1 xT_mem_A, inv_one, one_mul]
        exact hV
      · rw [map_mul, map_inv, xParity_xT, eq_ofAdd_one_of_ne_one _ hp]
        exact inv_mul_cancel _
  · by_cases hp : xParity (n := n) (by omega) g = 1
    · refine Or.inr (Or.inr (Or.inl ⟨?_, MonoidHom.mem_ker.2 ?_⟩))
      · change piT ((tT (n := n) (by omega))⁻¹ * g) ∈ V1
        rw [map_mul, map_inv, piT_tT]
        exact key _ hV
      · rw [map_mul, map_inv, xParity_tT, hp, inv_one, one_mul]
    · refine Or.inr (Or.inr (Or.inr ⟨?_, MonoidHom.mem_ker.2 ?_⟩))
      · change piT ((txT n)⁻¹ * g) ∈ V1
        rw [map_mul, map_inv, txT, piT_el]
        exact key _ hV
      · rw [map_mul, map_inv, xParity_txT, eq_ofAdd_one_of_ne_one _ hp]
        exact inv_mul_cancel _

theorem uT_mem_T2T (hn : 2 ≤ n) : uT (n := n) (by omega) ∈ T2T hn := by
  refine ⟨?_, ?_⟩
  · rw [piT_uT]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [uT, psiT_el hn]
    simp [hv]

theorem vT_mem_T2T (hn : 2 ≤ n) : vT (n := n) (by omega) ∈ T2T hn := by
  refine ⟨?_, ?_⟩
  · rw [piT_vT]
    exact Or.inr (Or.inl rfl)
  · rw [vT, psiT_el hn]
    simp only [hv, Matrix.cons_val, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, add_zero]
    exact two_mul_hh (by omega)

theorem r1T_mem_T2T (hn : 2 ≤ n) : r1T n ∈ T2T hn :=
  ⟨by rw [r1T, piT_el]; exact one_mem _, by rw [r1T, psiT_el hn]; simp⟩

theorem r2T_mem_T2T (hn : 2 ≤ n) : r2T n ∈ T2T hn :=
  ⟨by rw [r2T, piT_el]; exact one_mem _, by rw [r2T, psiT_el hn]; simp⟩

theorem psiT_w1T (hn : 3 ≤ n) : psiT (w1T (n := n) hn) = hh n := by
  rw [w1T, psiT_el (by omega)]
  simp only [wv, hv, Matrix.cons_val, Nat.cast_zero, mul_zero, add_zero]
  linear_combination four_mul_ss hn

theorem w1T_not_mem_T2T (hn : 3 ≤ n) : w1T (n := n) hn ∉ T2T (by omega) := fun h => by
  have := h.2
  rw [psiT_w1T hn] at this
  exact natCast_two_pow_ne_zero (n := n) (by omega) this

theorem w1T_mem_T1T (hn : 3 ≤ n) : w1T (n := n) hn ∈ T1T (by omega) := by
  refine ⟨A_le_Q1T (w1T_mem_A hn), MonoidHom.mem_ker.2 ?_⟩
  rw [w1T, xParity_el]
  simp only [wv, hv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.cast_one,
    Nat.cast_zero, mul_one, mul_zero, add_zero]
  rw [show ss n + hh n + ss n = 2 * ss n + hh n by ring, map_add, map_mul, red2_two, zero_mul,
    zero_add, red2_hh (by omega), ofAdd_zero]

theorem x1T_mem_commutator_T2T (hn : 3 ≤ n) :
    x1T (n := n) (by omega) ∈ ⁅T2T (n := n) (by omega), T2T (n := n) (by omega)⁆ := by
  have c1 := Subgroup.commutator_mem_commutator (r1T_mem_T2T (n := n) (by omega))
    (vT_mem_T2T (n := n) (by omega))
  have c2 := Subgroup.commutator_mem_commutator (r2T_mem_T2T (n := n) (by omega))
    (uT_mem_T2T (n := n) (by omega))
  have hprod := mul_mem (pow_mem c1 (2 ^ (n - 3))) (pow_mem c2 (2 ^ (n - 3)))
  convert hprod using 1
  rw [r1T, r2T, vT, uT, commutatorElement_el (by omega) _ _ (by decide),
    commutatorElement_el (by omega) _ _ (by decide), el_one_pow, el_one_pow, el_mul, x1T,
    el_eq_el_iff (by omega)]
  refine ⟨by rw [mul_one], ?_⟩
  have hz := two_mul_zL4 (n := n) (by omega)
  have h2 := two_mul_hh (n := n) (by omega)
  have h4 := four_mul_zL4 n
  have hk : ((2 ^ (n - 3) : ℕ) : ZMod (2 ^ n)) * 2 = zL4 n := by
    rw [zL4, show (2 : ZMod (2 ^ n)) = ((2 : ℕ) : ZMod (2 ^ n)) by norm_num, ← Nat.cast_mul,
      ← pow_succ]
    congr 2
    omega
  rw [pv_s01, pv_s23]
  refine isConst_of_forall_eq (-zL4 n) fun i => ?_
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, OneMemClass.coe_one, pv_one, hv,
      Matrix.cons_val, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, Nat.cast_one, Nat.cast_zero,
      mul_one, mul_zero, v1, v2, χx1, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | linear_combination hk - hz - h2 + h4
    | linear_combination -hk - 2 * hz + h4 - h2

theorem mem_closure_r_of_mem_T2T (hn : 3 ≤ n) {g : L4Model n} (hg : g ∈ T2T (by omega))
    (hπ : piT g = 1) : g ∈ closure {r1T n, r2T n} := by
  haveI : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨e, π, h, rfl⟩ := exists_eq_el g
  rw [piT_el] at hπ
  subst hπ
  have hpsi := hg.2
  rw [psiT_el (by omega)] at hpsi
  obtain ⟨b, -, hb⟩ := exists_hh_of_two_mul (n := n) (by omega) hpsi
  have hsum := detSum_one_iff.1 h
  rw [Fin.sum_univ_four] at hsum
  obtain ⟨c, hc⟩ : ∃ c : ZMod (2 ^ n), c = zL4 n * (b : ZMod (2 ^ n)) := ⟨_, rfl⟩
  have h2c : e 2 + e 3 = 2 * c := by
    rw [hc, ← mul_assoc, two_mul_zL4 (by omega), hb]
  have h4c : 4 * c = 0 := by rw [hc, ← mul_assoc, four_mul_zL4, zero_mul]
  have hmem : r1T n ^ (e 0 - c).val * r2T n ^ (e 2 - c).val ∈ closure {r1T n, r2T n} :=
    mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
  convert hmem using 1
  rw [r1T, r2T, el_one_pow, el_one_pow, el_mul, el_eq_el_iff (by omega)]
  refine ⟨by rw [mul_one], isConst_of_forall_eq (-c) fun i => ?_⟩
  have hv1 : ∀ i, ((e 0 - c).val • v1 n) i = (e 0 - c) * v1 n i := fun i => by
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hv2 : ∀ i, ((e 2 - c).val • v2 n) i = (e 2 - c) * v2 n i := fun i => by
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
  simp only [Pi.sub_apply, Pi.add_apply, OneMemClass.coe_one, pv_one, hv1, hv2]
  fin_cases i <;>
    simp only [v1, v2, Matrix.cons_val, mul_one, mul_zero, mul_neg, add_zero, zero_add,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    first
    | ring1
    | linear_combination -hsum + h2c + h4c
    | linear_combination -h2c

theorem T2T_le_closure (hn : 3 ≤ n) :
    T2T (n := n) (by omega) ≤ closure {uT (by omega), vT (by omega), r1T n, r2T n} := by
  intro g hg
  have hS : closure {r1T n, r2T n} ≤
      closure {uT (n := n) (by omega), vT (by omega), r1T n, r2T n} := by
    refine closure_mono fun x hx => ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hu : uT (n := n) (by omega) ∈
      closure {uT (n := n) (by omega), vT (by omega), r1T n, r2T n} :=
    subset_closure (by simp)
  have hv : vT (n := n) (by omega) ∈
      closure {uT (n := n) (by omega), vT (by omega), r1T n, r2T n} :=
    subset_closure (by simp)
  have key : ∀ a : L4Model n, a ∈ T2T (by omega) →
      a ∈ closure {uT (n := n) (by omega), vT (by omega), r1T n, r2T n} →
      g * a ∈ T2T (by omega) → piT (g * a) = 1 →
      g ∈ closure {uT (n := n) (by omega), vT (by omega), r1T n, r2T n} := by
    intro a _ ha hga hπ
    have := mul_mem (hS (mem_closure_r_of_mem_T2T hn hga hπ)) (inv_mem ha)
    rwa [mul_inv_cancel_right] at this
  have hgV : piT g ∈ V1 := hg.1
  have hcases := mem_finset_of_mem_V1 hgV
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  rcases hcases with h | h | h | h
  · exact key 1 (one_mem _) (one_mem _) (by rw [mul_one]; exact hg) (by rw [mul_one, h])
  · refine key _ (vT_mem_T2T (by omega)) hv (mul_mem hg (vT_mem_T2T _)) ?_
    rw [map_mul, h, piT_vT]
    decide
  · refine key _ (uT_mem_T2T (by omega)) hu (mul_mem hg (uT_mem_T2T _)) ?_
    rw [map_mul, h, piT_uT]
    decide
  · refine key _ (mul_mem (uT_mem_T2T (by omega)) (vT_mem_T2T (by omega))) (mul_mem hu hv)
      (mul_mem hg (mul_mem (uT_mem_T2T _) (vT_mem_T2T _))) ?_
    rw [map_mul, map_mul, h, piT_uT, piT_vT]
    decide

theorem isConj_uT_mul_r2T (hn : 3 ≤ n) :
    IsConj (uT (n := n) (by omega) * r2T n) (uT (by omega)) := by
  have hh2 := hh_add_hh (n := n) (by omega)
  have hd : detSum (![hh n, 0, -1, 1] : Fin 4 → ZMod (2 ^ n)) s23 := by
    rw [detSum_s23_iff (by omega)]
    simp only [Matrix.cons_val]
    linear_combination hh2
  have he : uT (n := n) (by omega) * r2T n = el ![hh n, 0, -1, 1] s23 hd := by
    rw [uT, r2T, el_mul, el_eq_el_iff (by omega), pv_s23]
    refine ⟨mul_one _, isConst_of_forall_eq 0 fun i => ?_⟩
    fin_cases i <;>
      simp only [Pi.sub_apply, Pi.add_apply, hv, v2, Matrix.cons_val, Nat.cast_one, Nat.cast_zero,
        mul_one, mul_zero, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring1
  have h2 : el ![hh n, 0, -1, 1] s23 hd * el ![hh n, 0, -1, 1] s23 hd = 1 := by
    rw [el_mul, ← el_zero_one, el_eq_el_iff (by omega), pv_s23]
    refine ⟨by decide, isConst_of_forall_eq 0 fun i => ?_⟩
    fin_cases i <;>
      simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply, Matrix.cons_val, Fin.zero_eta,
        Fin.mk_one, Fin.reduceFinMk] <;>
      first
      | ring1
      | linear_combination -hh2
  rw [he]
  refine isConj_el_s23_uT hn hd h2 ?_
  simp only [Matrix.cons_val]
  linear_combination -hh2

theorem tT_conj_uT_mul_r2T (hn : 2 ≤ n) :
    tT (n := n) (by omega) * (uT (by omega) * r2T n) * (tT (by omega))⁻¹ =
      vT (by omega) * r1T n := by
  rw [tT_inv hn, uT, r2T, el_mul, tT_mul_el_mul_tT, vT, r1T, el_mul, el_eq_el_iff hn]
  refine ⟨by decide, isConst_of_forall_eq 0 fun i => ?_⟩
  rw [pv_tP, pv_s23, pv_s01]
  fin_cases i <;>
    simp only [Pi.sub_apply, Pi.add_apply, hv, v1, v2, Matrix.cons_val, Nat.cast_one,
      Nat.cast_zero, mul_one, mul_zero, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> ring1

theorem psiT_uw1T (hn : 3 ≤ n) : psiT (uw1T (n := n) hn) = hh n := by
  rw [uw1T, psiT_el (by omega)]
  linear_combination four_mul_ss hn

theorem tT_not_mem_T2T (hn : 2 ≤ n) : tT (n := n) (by omega) ∉ T2T hn := fun h =>
  tT_not_mem_Q1T (n := n) (by omega) h.1

theorem txT_not_mem_T2T (hn : 2 ≤ n) : txT n ∉ T2T hn := fun h => by
  have : piT (txT n) ∉ V1 := by
    rw [txT, piT_el]
    decide
  exact this h.1

theorem w1T_inv_mul_mem_T2T (hn : 3 ≤ n) {g : L4Model n} (hg : piT g ∈ V1)
    (hψ : psiT g = hh n) : (w1T hn)⁻¹ * g ∈ T2T (by omega) := by
  have hw : piT (w1T (n := n) hn)⁻¹ ∈ V1 := by
    rw [map_inv, mem_A_iff.1 (w1T_mem_A hn), inv_one]
    exact one_mem _
  refine ⟨by rw [map_mul]; exact mul_mem hw hg, ?_⟩
  rw [psiT_mul (by omega) hw, psiT_inv (by omega) (A_le_Q1T (w1T_mem_A hn)), psiT_w1T, hψ,
    neg_add_cancel]

theorem uw1T_not_mem_T2T (hn : 3 ≤ n) : uw1T (n := n) hn ∉ T2T (by omega) := fun h => by
  have := h.2
  rw [psiT_uw1T hn] at this
  exact natCast_two_pow_ne_zero (n := n) (by omega) this

theorem mem_T2T_or_of_mul_self (hn : 3 ≤ n) {b : L4Model n} (hb : piT b ∈ V1)
    (h2 : b * b = 1) : b ∈ T2T (by omega) ∨ (w1T hn)⁻¹ * b ∈ T2T (by omega) := by
  have hψ : 2 * psiT b = 0 := by
    have := psiT_mul (n := n) (by omega) hb b
    rw [h2, psiT_one (by omega)] at this
    linear_combination -this
  obtain ⟨β, hβ, hβ'⟩ := exists_hh_of_two_mul (n := n) (by omega) hψ
  interval_cases β
  · left
    refine ⟨hb, ?_⟩
    rw [hβ', Nat.cast_zero, mul_zero]
  · right
    exact w1T_inv_mul_mem_T2T hn hb (by rw [hβ', Nat.cast_one, mul_one])

theorem exists_nsmul_eq_hh (hn : 1 ≤ n) {x : ZMod (2 ^ n)} (hx : x ≠ 0) :
    ∃ k : ℕ, k • x = hh n := by
  have hdvd : addOrderOf x ∣ 2 ^ n := addOrderOf_dvd_of_nsmul_eq_zero (by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, AddMonoid.addOrderOf_eq_one_iff] at hj
    exact hx hj
  have hy2 : 2 * (2 ^ (j - 1) • x) = 0 := by
    rw [two_mul, ← add_nsmul, ← two_mul, ← pow_succ',
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj0), ← hj, addOrderOf_nsmul_eq_zero]
  have hy0 : 2 ^ (j - 1) • x ≠ 0 := by
    refine nsmul_ne_zero_of_lt_addOrderOf (by positivity) ?_
    rw [hj]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨β, hβ, hβ'⟩ := exists_hh_of_two_mul hn hy2
  interval_cases β
  · rw [Nat.cast_zero, mul_zero] at hβ'
    exact absurd hβ' hy0
  · exact ⟨2 ^ (j - 1), by rw [hβ', Nat.cast_one, mul_one]⟩

theorem exists_pow_mem_w1T_coset (hn : 3 ≤ n) {g : L4Model n} (hg : piT g ∈ V1)
    (hg0 : g ∉ T2T (by omega)) : ∃ k : ℕ, (w1T hn)⁻¹ * g ^ k ∈ T2T (by omega) := by
  have hψ : psiT g ≠ 0 := fun h => hg0 ⟨hg, h⟩
  obtain ⟨k, hk⟩ := exists_nsmul_eq_hh (n := n) (by omega) hψ
  refine ⟨k, w1T_inv_mul_mem_T2T hn (by rw [map_pow]; exact pow_mem hg k) ?_⟩
  rw [psiT_pow (by omega) hg, hk]

end CFSG.LocalAnalysis.Mason73
