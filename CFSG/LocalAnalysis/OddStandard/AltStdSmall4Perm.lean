module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Defs

public section

namespace CFSG.OddStandard.AltStdSmall4

open Equiv Subgroup

variable {n : ℕ}

section Xor

theorem xor_lt_eight {a b : ℕ} (ha : a < 8) (hb : b < 8) : a ^^^ b < 8 := by
  have h := Nat.xor_lt_two_pow (n := 3) (x := a) (y := b) (by norm_num [ha]) (by norm_num [hb])
  simpa using h

theorem xor_eq_self_iff {a b : ℕ} : a ^^^ b = a ↔ b = 0 := by
  constructor
  · intro h
    have h1 : a ^^^ (a ^^^ b) = a ^^^ a := by rw [h]
    rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h1
  · rintro rfl
    exact Nat.xor_zero a

private theorem xor_cancel_aux (a b : ℕ) : a ^^^ (b ^^^ a) = b := by
  rw [Nat.xor_comm b a, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private theorem xor_affine_aux (a b c : ℕ) : a ^^^ c = a ^^^ (b ^^^ c) ^^^ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> rfl

private theorem xor_linear_aux (x y c : ℕ) : x ^^^ y ^^^ c ^^^ c = (x ^^^ c) ^^^ (y ^^^ c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases x.testBit i <;> cases y.testBit i <;> cases c.testBit i <;> rfl

@[expose] def xr (v w : Fin 8) : Fin 8 := ⟨v.val ^^^ w.val, xor_lt_eight v.2 w.2⟩

end Xor

section Translations

@[expose] def trFun (hn : 8 ≤ n) (v : Fin 8) (i : Fin n) : Fin n :=
  if h : i.val < 8 then ⟨i.val ^^^ v.val, lt_of_lt_of_le (xor_lt_eight h v.2) hn⟩ else i

theorem val_trFun_of_lt (hn : 8 ≤ n) (v : Fin 8) {i : Fin n} (hi : i.val < 8) :
    (trFun hn v i).val = i.val ^^^ v.val := by
  simp [trFun, hi]

theorem trFun_of_ge (hn : 8 ≤ n) (v : Fin 8) {i : Fin n} (hi : 8 ≤ i.val) :
    trFun hn v i = i := by
  simp [trFun, show ¬ i.val < 8 by omega]

theorem trFun_involutive (hn : 8 ≤ n) (v : Fin 8) : Function.Involutive (trFun hn v) := by
  intro i
  by_cases hi : i.val < 8
  · have h1 : (trFun hn v i).val < 8 := by
      rw [val_trFun_of_lt hn v hi]
      exact xor_lt_eight hi v.2
    apply Fin.ext
    rw [val_trFun_of_lt hn v h1, val_trFun_of_lt hn v hi, Nat.xor_assoc, Nat.xor_self,
      Nat.xor_zero]
  · have h : 8 ≤ i.val := by omega
    rw [trFun_of_ge hn v (i := i) h, trFun_of_ge hn v (i := i) h]

@[expose] def tr (hn : 8 ≤ n) (v : Fin 8) : Perm (Fin n) :=
  Function.Involutive.toPerm (trFun hn v) (trFun_involutive hn v)

theorem val_tr_of_lt (hn : 8 ≤ n) (v : Fin 8) {i : Fin n} (hi : i.val < 8) :
    (tr hn v i).val = i.val ^^^ v.val :=
  val_trFun_of_lt hn v hi

theorem tr_of_ge (hn : 8 ≤ n) (v : Fin 8) {i : Fin n} (hi : 8 ≤ i.val) : tr hn v i = i :=
  trFun_of_ge hn v hi

theorem val_tr_lt (hn : 8 ≤ n) (v : Fin 8) {i : Fin n} (hi : i.val < 8) :
    (tr hn v i).val < 8 := by
  rw [val_tr_of_lt hn v hi]
  exact xor_lt_eight hi v.2

theorem val_tr_pt_zero (hn : 8 ≤ n) (v : Fin 8) : (tr hn v (pt hn 0)).val = v.val := by
  rw [val_tr_of_lt hn v (i := pt hn 0) (show (0 : ℕ) < 8 by norm_num)]
  exact Nat.zero_xor _

theorem tr_pt_zero (hn : 8 ≤ n) {i : Fin n} (hi : i.val < 8) : tr hn ⟨i.val, hi⟩ (pt hn 0) = i :=
  Fin.ext (val_tr_pt_zero hn _)

theorem tr_mul_tr (hn : 8 ≤ n) (v w : Fin 8) : tr hn v * tr hn w = tr hn (xr v w) := by
  refine Equiv.ext fun i => ?_
  rw [Perm.mul_apply]
  by_cases hi : i.val < 8
  · apply Fin.ext
    rw [val_tr_of_lt hn v (val_tr_lt hn w hi), val_tr_of_lt hn w hi, val_tr_of_lt hn _ hi]
    show i.val ^^^ w.val ^^^ v.val = i.val ^^^ (v.val ^^^ w.val)
    rw [Nat.xor_assoc, Nat.xor_comm w.val]
  · push Not at hi
    rw [tr_of_ge hn w hi, tr_of_ge hn v hi, tr_of_ge hn _ hi]

theorem tr_zero (hn : 8 ≤ n) : tr hn 0 = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : i.val < 8
  · apply Fin.ext
    rw [val_tr_of_lt hn 0 hi, Perm.one_apply]
    simp
  · exact tr_of_ge hn 0 (by omega)

theorem tr_mul_self (hn : 8 ≤ n) (v : Fin 8) : tr hn v * tr hn v = 1 := by
  rw [tr_mul_tr, show xr v v = 0 from Fin.ext (by simp [xr]), tr_zero]

theorem tr_sq (hn : 8 ≤ n) (v : Fin 8) : tr hn v ^ 2 = 1 := by
  rw [sq, tr_mul_self]

theorem tr_inv (hn : 8 ≤ n) (v : Fin 8) : (tr hn v)⁻¹ = tr hn v :=
  inv_eq_of_mul_eq_one_right (tr_mul_self hn v)

theorem tr_injective (hn : 8 ≤ n) : Function.Injective (tr (n := n) hn) := by
  intro v w h
  apply Fin.ext
  rw [← val_tr_pt_zero hn v, ← val_tr_pt_zero hn w, h]

theorem tr_ne_self (hn : 8 ≤ n) {v : Fin 8} (hv : v ≠ 0) {i : Fin n} (hi : i.val < 8) :
    tr hn v i ≠ i := by
  intro h
  have h1 := congrArg Fin.val h
  rw [val_tr_of_lt hn v hi] at h1
  exact hv (Fin.ext (by simpa using xor_eq_self_iff.1 h1))

end Translations

section Generators

private def nswap (a b k : ℕ) : ℕ := if k = a then b else if k = b then a else k

private theorem val_swap_pt (hn : 8 ≤ n) {a b : ℕ} (ha : a < 8) (hb : b < 8) (x : Fin n) :
    (swap (pt hn a ha) (pt hn b hb) x).val = nswap a b x.val := by
  unfold nswap
  rw [swap_apply_def]
  by_cases h1 : x.val = a
  · rw [if_pos (Fin.ext h1 : x = pt hn a ha), if_pos h1] <;> rfl
  · have h3 : x ≠ pt hn a ha := fun h => h1 (congrArg Fin.val h)
    rw [if_neg h3, if_neg h1]
    by_cases h2 : x.val = b
    · rw [if_pos (Fin.ext h2 : x = pt hn b hb), if_pos h2] <;> rfl
    · have h4 : x ≠ pt hn b hb := fun h => h2 (congrArg Fin.val h)
      rw [if_neg h4, if_neg h2]

private theorem nswap_of_ge {a b k : ℕ} (ha : a < 8) (hb : b < 8) (hk : 8 ≤ k) :
    nswap a b k = k := by
  unfold nswap
  rw [if_neg (by omega), if_neg (by omega)]

theorem coe_quad_one (hn : 8 ≤ n) :
    ((quad hn 0 1 2 3 4 5 6 7 : alternatingGroup (Fin n)) : Perm (Fin n)) = tr hn 1 := by
  refine Equiv.ext fun x => Fin.ext ?_
  have hq : ((quad hn 0 1 2 3 4 5 6 7 : alternatingGroup (Fin n)) : Perm (Fin n)) x =
      swap (pt hn 0) (pt hn 1) (swap (pt hn 2) (pt hn 3)
        (swap (pt hn 4) (pt hn 5) (swap (pt hn 6) (pt hn 7) x))) := rfl
  rw [hq, val_swap_pt hn, val_swap_pt hn, val_swap_pt hn, val_swap_pt hn]
  by_cases hx : x.val < 8
  · rw [val_tr_of_lt hn 1 hx]
    have key : ∀ k : Fin 8,
        nswap 0 1 (nswap 2 3 (nswap 4 5 (nswap 6 7 k.val))) = k.val ^^^ (1 : Fin 8).val := by
      decide
    exact key ⟨x.val, hx⟩
  · have hx' : 8 ≤ x.val := by omega
    rw [tr_of_ge hn 1 (i := x) hx', nswap_of_ge (a := 6) (b := 7) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 4) (b := 5) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 2) (b := 3) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 0) (b := 1) (by norm_num) (by norm_num) hx']

theorem coe_quad_two (hn : 8 ≤ n) :
    ((quad hn 0 2 1 3 4 6 5 7 : alternatingGroup (Fin n)) : Perm (Fin n)) = tr hn 2 := by
  refine Equiv.ext fun x => Fin.ext ?_
  have hq : ((quad hn 0 2 1 3 4 6 5 7 : alternatingGroup (Fin n)) : Perm (Fin n)) x =
      swap (pt hn 0) (pt hn 2) (swap (pt hn 1) (pt hn 3)
        (swap (pt hn 4) (pt hn 6) (swap (pt hn 5) (pt hn 7) x))) := rfl
  rw [hq, val_swap_pt hn, val_swap_pt hn, val_swap_pt hn, val_swap_pt hn]
  by_cases hx : x.val < 8
  · rw [val_tr_of_lt hn 2 hx]
    have key : ∀ k : Fin 8,
        nswap 0 2 (nswap 1 3 (nswap 4 6 (nswap 5 7 k.val))) = k.val ^^^ (2 : Fin 8).val := by
      decide
    exact key ⟨x.val, hx⟩
  · have hx' : 8 ≤ x.val := by omega
    rw [tr_of_ge hn 2 (i := x) hx', nswap_of_ge (a := 5) (b := 7) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 4) (b := 6) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 1) (b := 3) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 0) (b := 2) (by norm_num) (by norm_num) hx']

theorem coe_quad_four (hn : 8 ≤ n) :
    ((quad hn 0 4 1 5 2 6 3 7 : alternatingGroup (Fin n)) : Perm (Fin n)) = tr hn 4 := by
  refine Equiv.ext fun x => Fin.ext ?_
  have hq : ((quad hn 0 4 1 5 2 6 3 7 : alternatingGroup (Fin n)) : Perm (Fin n)) x =
      swap (pt hn 0) (pt hn 4) (swap (pt hn 1) (pt hn 5)
        (swap (pt hn 2) (pt hn 6) (swap (pt hn 3) (pt hn 7) x))) := rfl
  rw [hq, val_swap_pt hn, val_swap_pt hn, val_swap_pt hn, val_swap_pt hn]
  by_cases hx : x.val < 8
  · rw [val_tr_of_lt hn 4 hx]
    have key : ∀ k : Fin 8,
        nswap 0 4 (nswap 1 5 (nswap 2 6 (nswap 3 7 k.val))) = k.val ^^^ (4 : Fin 8).val := by
      decide
    exact key ⟨x.val, hx⟩
  · have hx' : 8 ≤ x.val := by omega
    rw [tr_of_ge hn 4 (i := x) hx', nswap_of_ge (a := 3) (b := 7) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 2) (b := 6) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 1) (b := 5) (by norm_num) (by norm_num) hx',
      nswap_of_ge (a := 0) (b := 4) (by norm_num) (by norm_num) hx']

private theorem tr_mul_tr_eq (hn : 8 ≤ n) {u v w : Fin 8} (h : u.val ^^^ v.val = w.val) :
    tr hn u * tr hn v = tr hn w := by
  rw [tr_mul_tr]
  congr 1
  exact Fin.ext h

theorem exists_mem_eBar_coe_eq_tr (hn : 8 ≤ n) (v : Fin 8) :
    ∃ y ∈ eBar hn, (y : Perm (Fin n)) = tr hn v := by
  have g1 : quad hn 0 1 2 3 4 5 6 7 ∈ eBar hn := by
    unfold eBar
    exact subset_closure (by simp)
  have g2 : quad hn 0 2 1 3 4 6 5 7 ∈ eBar hn := by
    unfold eBar
    exact subset_closure (by simp)
  have g4 : quad hn 0 4 1 5 2 6 3 7 ∈ eBar hn := by
    unfold eBar
    exact subset_closure (by simp)
  have e1 := coe_quad_one hn
  have e2 := coe_quad_two hn
  have e4 := coe_quad_four hn
  obtain ⟨v, hv⟩ := v
  interval_cases v
  · exact ⟨1, one_mem _, (tr_zero hn).symm⟩
  · exact ⟨_, g1, e1⟩
  · exact ⟨_, g2, e2⟩
  · exact ⟨_, mul_mem g1 g2, by rw [Subgroup.coe_mul, e1, e2]; exact tr_mul_tr_eq hn (by simp)⟩
  · exact ⟨_, g4, e4⟩
  · exact ⟨_, mul_mem g1 g4, by rw [Subgroup.coe_mul, e1, e4]; exact tr_mul_tr_eq hn (by simp)⟩
  · exact ⟨_, mul_mem g2 g4, by rw [Subgroup.coe_mul, e2, e4]; exact tr_mul_tr_eq hn (by simp)⟩
  · refine ⟨_, mul_mem (mul_mem g1 g2) g4, ?_⟩
    rw [Subgroup.coe_mul, Subgroup.coe_mul, e1, e2, e4,
      tr_mul_tr_eq hn (u := 1) (v := 2) (w := 3) (by simp)]
    exact tr_mul_tr_eq hn (by simp)

theorem mem_eBar_iff (hn : 8 ≤ n) {x : alternatingGroup (Fin n)} :
    x ∈ eBar hn ↔ ∃ v : Fin 8, (x : Perm (Fin n)) = tr hn v := by
  constructor
  · intro hx
    unfold eBar at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨1, coe_quad_one hn⟩
      · exact ⟨2, coe_quad_two hn⟩
      · exact ⟨4, coe_quad_four hn⟩
    | one => exact ⟨0, (tr_zero hn).symm⟩
    | mul y w _ _ hy hw =>
      obtain ⟨v, hv⟩ := hy
      obtain ⟨u, hu⟩ := hw
      exact ⟨xr v u, by rw [Subgroup.coe_mul, hv, hu, tr_mul_tr]⟩
    | inv y _ hy =>
      obtain ⟨v, hv⟩ := hy
      exact ⟨v, by rw [Subgroup.coe_inv, hv, tr_inv]⟩
  · rintro ⟨v, hv⟩
    obtain ⟨y, hy, hyv⟩ := exists_mem_eBar_coe_eq_tr hn v
    have : x = y := Subtype.ext (hv.trans hyv.symm)
    rw [this]
    exact hy

theorem tr_mem_alternatingGroup (hn : 8 ≤ n) (v : Fin 8) :
    tr hn v ∈ alternatingGroup (Fin n) := by
  obtain ⟨y, -, hy⟩ := exists_mem_eBar_coe_eq_tr hn v
  rw [← hy]
  exact y.2

end Generators

section Basic

theorem card_eBar (hn : 8 ≤ n) : Nat.card (eBar hn) = 8 := by
  choose f hfm hf using exists_mem_eBar_coe_eq_tr hn
  let F : Fin 8 → eBar hn := fun v => ⟨f v, hfm v⟩
  have hF : Function.Bijective F := by
    refine ⟨fun v w hvw => tr_injective hn ?_, fun y => ?_⟩
    · rw [← hf v, ← hf w]
      exact congrArg (fun y : eBar hn => ((y : alternatingGroup (Fin n)) : Perm (Fin n))) hvw
    · obtain ⟨v, hv⟩ := (mem_eBar_iff hn).1 y.2
      exact ⟨v, Subtype.ext (Subtype.ext ((hf v).trans hv.symm))⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem wBar_mem_eBar (hn : 8 ≤ n) : wBar hn ∈ eBar hn := by
  unfold wBar eBar
  exact subset_closure (by simp)

theorem coe_wBar (hn : 8 ≤ n) : (wBar hn : Perm (Fin n)) = tr hn 1 :=
  coe_quad_one hn

theorem card_filter_lt_eight (hn : 8 ≤ n) :
    (Finset.univ.filter fun i : Fin n => i.val < 8).card = 8 := by
  rw [Fin.card_filter_val_lt]
  omega

end Basic

section Centralizer

theorem comm_tr_of_comm_eBar (hn : 8 ≤ n) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, σ * (e : Perm (Fin n)) = e * σ) (v : Fin 8) :
    σ * tr hn v = tr hn v * σ := by
  obtain ⟨y, hy, hyv⟩ := exists_mem_eBar_coe_eq_tr hn v
  rw [← hyv]
  exact hσ y hy

private theorem lt_eight_of_conj_tr_one (hn : 8 ≤ n) {σ : Perm (Fin n)} {w : Fin 8}
    (hw : σ * tr hn 1 = tr hn w * σ) {i : Fin n} (hi : i.val < 8) : (σ i).val < 8 := by
  by_contra hge
  push Not at hge
  have h1 : σ (tr hn 1 i) = tr hn w (σ i) := by
    rw [← Perm.mul_apply, hw, Perm.mul_apply]
  rw [tr_of_ge hn w hge] at h1
  exact tr_ne_self hn (by decide) hi (σ.injective h1)

theorem apply_of_comm_eBar (hn : 8 ≤ n) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, σ * (e : Perm (Fin n)) = e * σ) {i : Fin n} (hi : i.val < 8) :
    (σ i).val < 8 ∧ (σ i).val = (σ (pt hn 0)).val ^^^ i.val := by
  have hc := comm_tr_of_comm_eBar hn hσ
  have hlt : ∀ j : Fin n, j.val < 8 → (σ j).val < 8 := fun j hj =>
    lt_eight_of_conj_tr_one hn (hc 1) hj
  refine ⟨hlt i hi, ?_⟩
  have h1 : σ i = tr hn ⟨i.val, hi⟩ (σ (pt hn 0)) := by
    conv_lhs => rw [← tr_pt_zero hn hi]
    rw [← Perm.mul_apply σ (tr hn ⟨i.val, hi⟩), hc, Perm.mul_apply]
  rw [h1, val_tr_of_lt hn _ (hlt (pt hn 0) (show (0 : ℕ) < 8 by norm_num))]

theorem exists_eBar_eq_of_comm (hn : 8 ≤ n) (hn11 : n ≤ 11) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, σ * (e : Perm (Fin n)) = e * σ) {k : ℕ} (hk : σ ^ 2 ^ k = 1)
    (hev : n ≤ 9 ∨ σ ∈ alternatingGroup (Fin n)) :
    ∃ e ∈ eBar hn, (e : Perm (Fin n)) = σ := by
  have h0 := (apply_of_comm_eBar hn hσ (i := pt hn 0) (show (0 : ℕ) < 8 by norm_num)).1
  obtain ⟨s, hs⟩ : ∃ s : Fin 8, s.val = (σ (pt hn 0)).val := ⟨⟨_, h0⟩, rfl⟩
  have hfix : ∀ i : Fin n, i.val < 8 → (σ * tr hn s) i = i := by
    intro i hi
    apply Fin.ext
    rw [Perm.mul_apply, (apply_of_comm_eBar hn hσ (val_tr_lt hn s hi)).2, val_tr_of_lt hn s hi,
      hs]
    exact xor_cancel_aux _ _
  have hsupp : (σ * tr hn s).support ⊆ (Finset.univ.filter fun i : Fin n => i.val < 8)ᶜ := by
    intro i hi
    rw [Finset.mem_compl, Finset.mem_filter]
    intro h
    exact (Perm.mem_support.1 hi) (hfix i h.2)
  have hcard : (σ * tr hn s).support.card ≤ n - 8 := by
    have := Finset.card_le_card hsupp
    rwa [Finset.card_compl, Fintype.card_fin, card_filter_lt_eight hn] at this
  have hcomm : Commute σ (tr hn s) := comm_tr_of_comm_eBar hn hσ s
  have hσk : σ ^ 2 ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  have hτk : tr hn s ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, tr_sq, one_pow]
  have hρk : (σ * tr hn s) ^ 2 ^ (k + 1) = 1 := by rw [hcomm.mul_pow, hσk, hτk, one_mul]
  have hρ1 : σ * tr hn s = 1 := by
    rw [← Perm.support_eq_empty_iff, ← Finset.card_eq_zero]
    have hne1 := Perm.card_support_ne_one (σ * tr hn s)
    rcases hev with h9 | hev
    · omega
    · by_contra hne0
      rcases (show (σ * tr hn s).support.card = 2 ∨ (σ * tr hn s).support.card = 3 by omega)
        with h2 | h3
      · have hsg := (Perm.card_support_eq_two.1 h2).sign_eq
        rw [Perm.sign_mul, Perm.mem_alternatingGroup.1 hev,
          Perm.mem_alternatingGroup.1 (tr_mem_alternatingGroup hn s), mul_one] at hsg
        exact absurd hsg (by decide)
      · have h3' := (card_support_eq_three_iff.1 h3).orderOf
        have hdvd := orderOf_dvd_of_pow_eq_one hρk
        rw [h3'] at hdvd
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
        omega
  refine ⟨⟨tr hn s, tr_mem_alternatingGroup hn s⟩, (mem_eBar_iff hn).2 ⟨s, rfl⟩, ?_⟩
  show tr hn s = σ
  rw [eq_inv_of_mul_eq_one_left hρ1, tr_inv]

end Centralizer

section Normalizer

theorem exists_conj_tr_of_normalizes_eBar (hn : 8 ≤ n) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, ∃ e' ∈ eBar hn, σ * (e : Perm (Fin n)) * σ⁻¹ = e') (v : Fin 8) :
    ∃ w : Fin 8, σ * tr hn v = tr hn w * σ := by
  obtain ⟨y, hy, hyv⟩ := exists_mem_eBar_coe_eq_tr hn v
  obtain ⟨e', he', he'eq⟩ := hσ y hy
  obtain ⟨w, hw⟩ := (mem_eBar_iff hn).1 he'
  refine ⟨w, ?_⟩
  rw [← hw, ← he'eq, ← hyv]
  group

theorem lt_eight_of_normalizes_eBar (hn : 8 ≤ n) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, ∃ e' ∈ eBar hn, σ * (e : Perm (Fin n)) * σ⁻¹ = e') {i : Fin n}
    (hi : i.val < 8) : (σ i).val < 8 := by
  obtain ⟨w, hw⟩ := exists_conj_tr_of_normalizes_eBar hn hσ 1
  exact lt_eight_of_conj_tr_one hn hw hi

theorem affine_of_normalizes_eBar (hn : 8 ≤ n) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, ∃ e' ∈ eBar hn, σ * (e : Perm (Fin n)) * σ⁻¹ = e') {i j k : Fin n}
    (hi : i.val < 8) (hj : j.val < 8) (hk : k.val = i.val ^^^ j.val) :
    (σ k).val = (σ i).val ^^^ (σ j).val ^^^ (σ (pt hn 0)).val := by
  obtain ⟨w, hw⟩ := exists_conj_tr_of_normalizes_eBar hn hσ ⟨j.val, hj⟩
  have hk' : tr hn ⟨j.val, hj⟩ i = k := Fin.ext (by rw [val_tr_of_lt hn _ hi, hk])
  have h1 : σ k = tr hn w (σ i) := by
    rw [← hk', ← Perm.mul_apply σ (tr hn ⟨j.val, hj⟩), hw, Perm.mul_apply]
  have h2 : σ j = tr hn w (σ (pt hn 0)) := by
    conv_lhs => rw [← tr_pt_zero hn hj]
    rw [← Perm.mul_apply σ (tr hn ⟨j.val, hj⟩), hw, Perm.mul_apply]
  have hi8 := lt_eight_of_normalizes_eBar hn hσ hi
  have h08 := lt_eight_of_normalizes_eBar hn hσ (i := pt hn 0) (show (0 : ℕ) < 8 by norm_num)
  have h2' := congrArg Fin.val h2
  rw [val_tr_of_lt hn w h08] at h2'
  rw [h1, val_tr_of_lt hn w hi8, h2']
  exact xor_affine_aux _ _ _

@[expose] def lin8 (a1 a2 a4 : Fin 8) : Fin 8 → Fin 8 :=
  ![0, a1, a2, xr a1 a2, a4, xr a1 a4, xr a2 a4, xr (xr a1 a2) a4]

theorem sign_lin8 : ∀ a1 a2 a4 : Fin 8, ∀ h : Function.Injective (lin8 a1 a2 a4),
    Perm.sign (Equiv.ofBijective _ (Finite.injective_iff_bijective.1 h)) = 1 := by
  decide +kernel

theorem eq_lin8 {f : Fin 8 → Fin 8} (hf : ∀ i j, f (xr i j) = xr (f i) (f j)) :
    f = lin8 (f 1) (f 2) (f 4) := by
  have key : ∀ i j k : Fin 8, xr i j = k → f k = xr (f i) (f j) := fun i j k h => h ▸ hf i j
  have h0 : f 0 = 0 := by
    rw [key 0 0 0 (by decide)]
    exact Fin.ext (Nat.xor_self _)
  funext k
  obtain ⟨k, hk⟩ := k
  interval_cases k
  · exact h0
  · rfl
  · rfl
  · exact key 1 2 3 (by decide)
  · rfl
  · exact key 1 4 5 (by decide)
  · exact key 2 4 6 (by decide)
  · exact (key 3 4 7 (by decide)).trans (congrArg (fun t => xr t (f 4)) (key 1 2 3 (by decide)))

theorem mem_alternatingGroup_of_normalizes_eBar (hn : 8 ≤ n) (hn9 : n ≤ 9) {σ : Perm (Fin n)}
    (hσ : ∀ e ∈ eBar hn, ∃ e' ∈ eBar hn, σ * (e : Perm (Fin n)) * σ⁻¹ = e') :
    σ ∈ alternatingGroup (Fin n) := by
  have hlt : ∀ i : Fin n, i.val < 8 → (σ i).val < 8 := fun i hi =>
    lt_eight_of_normalizes_eBar hn hσ hi
  let emb : Fin 8 → Fin n := fun k => ⟨k.val, lt_of_lt_of_le k.2 hn⟩
  have hge : ∀ i : Fin n, 8 ≤ i.val → σ i = i := by
    intro i hi
    have hsi : 8 ≤ (σ i).val := by
      by_contra h
      push Not at h
      let f : Fin 8 → Fin 8 := fun k => ⟨(σ (emb k)).val, hlt (emb k) k.2⟩
      have hf : Function.Injective f := by
        intro a b hab
        have h0 : (f a).val = (f b).val := congrArg Fin.val hab
        have h1 : σ (emb a) = σ (emb b) := Fin.ext h0
        have h2 : (emb a).val = (emb b).val := congrArg Fin.val (σ.injective h1)
        exact Fin.ext h2
      obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) ⟨(σ i).val, h⟩
      have h0 : (f k).val = (σ i).val := congrArg Fin.val hk
      have h1 : σ (emb k) = σ i := Fin.ext h0
      have h2 : (emb k).val = i.val := congrArg Fin.val (σ.injective h1)
      have h3 : (emb k).val < 8 := k.2
      omega
    have h1 := (σ i).isLt
    have h2 := i.isLt
    apply Fin.ext
    omega
  obtain ⟨b, hb⟩ : ∃ b : Fin 8, b.val = (σ (pt hn 0)).val :=
    ⟨⟨_, hlt (pt hn 0) (show (0 : ℕ) < 8 by norm_num)⟩, rfl⟩
  have hσA : σ = tr hn b * (tr hn b * σ) := by rw [← mul_assoc, tr_mul_self, one_mul]
  have hAval : ∀ x : Fin n, x.val < 8 → ((tr hn b * σ) x).val = (σ x).val ^^^ b.val :=
    fun x hx => by rw [Perm.mul_apply, val_tr_of_lt hn b (hlt x hx)]
  have hAge : ∀ x : Fin n, 8 ≤ x.val → (tr hn b * σ) x = x := fun x hx => by
    rw [Perm.mul_apply, hge x hx, tr_of_ge hn b hx]
  have h₁ : ∀ x : Fin n, ((tr hn b * σ) x).val < 8 ↔ x.val < 8 := by
    intro x
    constructor
    · intro h
      by_contra hx
      push Not at hx
      rw [hAge x hx] at h
      omega
    · intro hx
      rw [hAval x hx]
      exact xor_lt_eight (hlt x hx) b.2
  have h₂ : ∀ x : Fin n, (tr hn b * σ) x ≠ x → x.val < 8 := by
    intro x hx
    by_contra h
    push Not at h
    exact hx (hAge x h)
  let e : {i : Fin n // i.val < 8} ≃ Fin 8 :=
    ⟨fun i => ⟨i.1.val, i.2⟩, fun k => ⟨emb k, k.2⟩, fun _ => rfl, fun _ => rfl⟩
  let π : Perm (Fin 8) := e.permCongr ((tr hn b * σ).subtypePerm h₁)
  have hπval : ∀ k : Fin 8, (π k).val = ((tr hn b * σ) (emb k)).val := fun _ => rfl
  have hπlin : ∀ i j : Fin 8, π (xr i j) = xr (π i) (π j) := by
    intro i j
    apply Fin.ext
    show (π (xr i j)).val = (π i).val ^^^ (π j).val
    have hk := affine_of_normalizes_eBar hn hσ (i := emb i) (j := emb j) (k := emb (xr i j))
      i.2 j.2 rfl
    rw [hπval (xr i j), hπval i, hπval j, hAval (emb (xr i j)) (xr i j).2, hAval (emb i) i.2,
      hAval (emb j) j.2, hk, ← hb]
    exact xor_linear_aux _ _ _
  have hsignπ : Perm.sign π = 1 := by
    have hfun := eq_lin8 hπlin
    have hinj : Function.Injective (lin8 (π 1) (π 2) (π 4)) := by
      rw [← hfun]
      exact π.injective
    have hπeq : π = Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj) :=
      Equiv.ext fun k => congrFun hfun k
    rw [hπeq]
    exact sign_lin8 _ _ _ hinj
  have hsignA : Perm.sign (tr hn b * σ) = 1 := by
    rw [← Perm.sign_subtypePerm _ h₁ h₂, ← Perm.sign_permCongr e]
    exact hsignπ
  rw [Perm.mem_alternatingGroup, hσA, Perm.sign_mul,
    Perm.mem_alternatingGroup.1 (tr_mem_alternatingGroup hn b), hsignA, one_mul]

end Normalizer

end CFSG.OddStandard.AltStdSmall4
