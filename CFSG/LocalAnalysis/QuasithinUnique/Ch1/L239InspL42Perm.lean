module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.L42Insp

open Equiv

@[expose] def pd (a i : Nat) : Nat := a / 8 ^ i % 8

@[expose] def pm (a b : Nat) : Nat :=
  pd a (pd b 0) + 8 * pd a (pd b 1) + 64 * pd a (pd b 2) + 512 * pd a (pd b 3) +
    4096 * pd a (pd b 4) + 32768 * pd a (pd b 5) + 262144 * pd a (pd b 6) +
    2097152 * pd a (pd b 7)

@[expose] def pone : Nat :=
  0 + 8 * 1 + 64 * 2 + 512 * 3 + 4096 * 4 + 32768 * 5 + 262144 * 6 + 2097152 * 7

@[expose] def pswap (a b : Nat) : Nat :=
  (List.range 8).foldr (fun i acc => (if i = a then b else if i = b then a else i) + 8 * acc) 0

@[expose] def pgen (i : Nat) : Nat := if i < 7 then pswap i (i + 1) else pone

@[expose] def pw (w : List Nat) : Nat := (w.map pgen).foldr pm pone

@[expose] def pn (σ : Perm (Fin 8)) : Nat :=
  (σ 0).val + 8 * (σ 1).val + 64 * (σ 2).val + 512 * (σ 3).val + 4096 * (σ 4).val +
    32768 * (σ 5).val + 262144 * (σ 6).val + 2097152 * (σ 7).val

theorem pd_pn (σ : Perm (Fin 8)) (k : Fin 8) : pd (pn σ) k.val = (σ k).val := by
  have h : ∀ a : Fin 8, (σ a).val < 8 := fun a => (σ a).isLt
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  fin_cases k <;> simp only [pd, pn] <;> norm_num <;> omega

theorem pn_mul (σ τ : Perm (Fin 8)) : pn (σ * τ) = pm (pn σ) (pn τ) := by
  have a0 : pd (pn τ) 0 = (τ 0).val := pd_pn τ 0
  have a1 : pd (pn τ) 1 = (τ 1).val := pd_pn τ 1
  have a2 : pd (pn τ) 2 = (τ 2).val := pd_pn τ 2
  have a3 : pd (pn τ) 3 = (τ 3).val := pd_pn τ 3
  have a4 : pd (pn τ) 4 = (τ 4).val := pd_pn τ 4
  have a5 : pd (pn τ) 5 = (τ 5).val := pd_pn τ 5
  have a6 : pd (pn τ) 6 = (τ 6).val := pd_pn τ 6
  have a7 : pd (pn τ) 7 = (τ 7).val := pd_pn τ 7
  have b : ∀ i : Fin 8, pd (pn σ) (τ i).val = (σ (τ i)).val := fun i => pd_pn σ (τ i)
  simp only [pm, a0, a1, a2, a3, a4, a5, a6, a7, b]
  rfl

theorem pn_inj : Function.Injective pn := by
  intro σ τ h
  have key : ∀ k : Fin 8, (σ k).val = (τ k).val := by
    intro k
    rw [← pd_pn σ k, ← pd_pn τ k, h]
  ext k
  exact key k

theorem pn_one : pn (1 : Perm (Fin 8)) = pone := by
  decide

theorem pn_swap : ∀ a b : Fin 8, pn (swap a b) = pswap a.val b.val := by
  decide

theorem card_subtype_mem {l : List Nat} (h : l.Nodup) : Nat.card {a // a ∈ l} = l.length := by
  classical
  have e : {a // a ∈ l} ≃ ↥l.toFinset :=
    Equiv.subtypeEquivRight fun a => by simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup h]

@[expose] def gen (i : Nat) : Perm (Fin 8) :=
  if h : i < 7 then swap ⟨i, by omega⟩ ⟨i + 1, by omega⟩ else 1

@[expose] def wg (w : List Nat) : Perm (Fin 8) := (w.map gen).prod

theorem pn_gen (i : Nat) : pn (gen i) = pgen i := by
  unfold gen pgen
  split_ifs with h
  · rw [pn_swap]
  · exact pn_one

theorem pn_wg (w : List Nat) : pn (wg w) = pw w := by
  induction w with
  | nil => exact pn_one
  | cons i w ih =>
    simp only [wg, pw, List.map_cons, List.prod_cons, List.foldr_cons] at ih ⊢
    rw [pn_mul, pn_gen, ih]

theorem gen_inv (i : Nat) : (gen i)⁻¹ = gen i := by
  unfold gen
  split_ifs
  · exact swap_inv _ _
  · exact inv_one

theorem wg_append (l₁ l₂ : List Nat) : wg (l₁ ++ l₂) = wg l₁ * wg l₂ := by
  simp [wg, List.prod_append]

theorem wg_inv (w : List Nat) : (wg w)⁻¹ = wg w.reverse := by
  induction w with
  | nil => simp [wg]
  | cons i w ih =>
    rw [List.reverse_cons, wg_append]
    have h1 : wg (i :: w) = gen i * wg w := by simp [wg]
    rw [h1, mul_inv_rev, ih, gen_inv]
    simp [wg]

theorem sign_gen {i : Nat} (hi : i < 7) : Perm.sign (gen i) = -1 := by
  unfold gen
  simp only [hi, dite_true]
  apply Perm.sign_swap
  intro h
  have := congrArg Fin.val h
  simp at this

theorem sign_wg {w : List Nat} (hw : ∀ i ∈ w, i < 7) : Perm.sign (wg w) = (-1) ^ w.length := by
  induction w with
  | nil => simp [wg]
  | cons i w ih =>
    have h1 : wg (i :: w) = gen i * wg w := by simp [wg]
    rw [h1, map_mul, sign_gen (hw i List.mem_cons_self), ih (fun j hj => hw j (List.mem_cons_of_mem i hj))]
    simp [pow_succ, mul_comm]

theorem step (k : Nat) (hk : k < 8) (h : Perm (Fin 8)) (hfix : ∀ i : Fin 8, i.val < k → h i = i) :
    ∃ j : Fin 8, k ≤ j.val ∧ ∀ i : Fin 8, i.val ≤ k → (swap ⟨k, hk⟩ j * h) i = i := by
  have hge : k ≤ (h ⟨k, hk⟩).val := by
    by_contra hlt
    push Not at hlt
    have hh : h (h ⟨k, hk⟩) = h ⟨k, hk⟩ := hfix (h ⟨k, hk⟩) hlt
    have h2 : h ⟨k, hk⟩ = ⟨k, hk⟩ := h.injective hh
    rw [h2] at hlt
    exact lt_irrefl _ hlt
  refine ⟨h ⟨k, hk⟩, hge, fun i hi => ?_⟩
  rcases Nat.lt_or_eq_of_le hi with hik | hik
  · rw [Perm.mul_apply, hfix i hik]
    apply swap_apply_of_ne_of_ne
    · intro h3
      have := congrArg Fin.val h3
      simp at this
      omega
    · intro h3
      have := congrArg Fin.val h3
      omega
  · have hi' : i = ⟨k, hk⟩ := Fin.ext hik
    rw [hi', Perm.mul_apply, swap_apply_right]

theorem eq_one_of_fix (h : Perm (Fin 8)) (hfix : ∀ i : Fin 8, i.val < 7 → h i = i) : h = 1 := by
  ext i
  by_cases hi : i.val < 7
  · simp [hfix i hi]
  · have hi7 : i = 7 := Fin.ext (by omega)
    subst hi7
    have h77 : (h 7).val = 7 := by
      by_contra hne
      have hlt : (h 7).val < 7 := by
        have := (h 7).isLt
        omega
      have h8 : h 7 = 7 := h.injective (hfix (h 7) hlt)
      rw [h8] at hlt
      exact absurd hlt (by decide)
    simpa using h77

theorem perm8_factor (σ : Perm (Fin 8)) :
    ∃ j0 j1 j2 j3 j4 j5 j6 : Fin 8, 0 ≤ j0.val ∧ 1 ≤ j1.val ∧ 2 ≤ j2.val ∧ 3 ≤ j3.val ∧
      4 ≤ j4.val ∧ 5 ≤ j5.val ∧ 6 ≤ j6.val ∧
      σ = swap 0 j0 * swap 1 j1 * swap 2 j2 * swap 3 j3 * swap 4 j4 * swap 5 j5 * swap 6 j6 := by
  obtain ⟨j0, hj0, h0⟩ := step 0 (by norm_num) σ (fun i hi => absurd hi (by omega))
  obtain ⟨j1, hj1, h1⟩ := step 1 (by norm_num) (swap ⟨0, by norm_num⟩ j0 * σ)
    (fun i hi => h0 i (by omega))
  obtain ⟨j2, hj2, h2⟩ := step 2 (by norm_num) (swap ⟨1, by norm_num⟩ j1 * (swap ⟨0, by norm_num⟩ j0 * σ))
    (fun i hi => h1 i (by omega))
  obtain ⟨j3, hj3, h3⟩ := step 3 (by norm_num)
    (swap ⟨2, by norm_num⟩ j2 * (swap ⟨1, by norm_num⟩ j1 * (swap ⟨0, by norm_num⟩ j0 * σ)))
    (fun i hi => h2 i (by omega))
  obtain ⟨j4, hj4, h4⟩ := step 4 (by norm_num)
    (swap ⟨3, by norm_num⟩ j3 * (swap ⟨2, by norm_num⟩ j2 * (swap ⟨1, by norm_num⟩ j1 *
      (swap ⟨0, by norm_num⟩ j0 * σ))))
    (fun i hi => h3 i (by omega))
  obtain ⟨j5, hj5, h5⟩ := step 5 (by norm_num)
    (swap ⟨4, by norm_num⟩ j4 * (swap ⟨3, by norm_num⟩ j3 * (swap ⟨2, by norm_num⟩ j2 *
      (swap ⟨1, by norm_num⟩ j1 * (swap ⟨0, by norm_num⟩ j0 * σ)))))
    (fun i hi => h4 i (by omega))
  obtain ⟨j6, hj6, h6⟩ := step 6 (by norm_num)
    (swap ⟨5, by norm_num⟩ j5 * (swap ⟨4, by norm_num⟩ j4 * (swap ⟨3, by norm_num⟩ j3 *
      (swap ⟨2, by norm_num⟩ j2 * (swap ⟨1, by norm_num⟩ j1 * (swap ⟨0, by norm_num⟩ j0 * σ))))))
    (fun i hi => h5 i (by omega))
  have h7 := eq_one_of_fix _ (fun i hi => h6 i (by omega))
  refine ⟨j0, j1, j2, j3, j4, j5, j6, hj0, hj1, hj2, hj3, hj4, hj5, hj6, ?_⟩
  have e := h7
  simp only [← mul_assoc] at e
  have e2 := eq_inv_of_mul_eq_one_right e
  rw [e2]
  simp only [mul_inv_rev, swap_inv, mul_assoc]
  rfl

theorem pn_swap_lit (a : Fin 8) (b : Fin 8) : pn (swap a b) = pswap a.val b.val := pn_swap a b

@[expose] def enumS8e (f : Nat → Bool) : Bool :=
  (List.range' 0 8).all fun j0 => (List.range' 1 7).all fun j1 => (List.range' 2 6).all fun j2 =>
  (List.range' 3 5).all fun j3 => (List.range' 4 4).all fun j4 => (List.range' 5 3).all fun j5 =>
  (List.range' 6 2).all fun j6 =>
    ((if j0 = 0 then 0 else 1) + (if j1 = 1 then 0 else 1) + (if j2 = 2 then 0 else 1) +
      (if j3 = 3 then 0 else 1) + (if j4 = 4 then 0 else 1) + (if j5 = 5 then 0 else 1) +
      (if j6 = 6 then 0 else 1)) % 2 != 0 ||
    f (pm (pm (pm (pm (pm (pm (pswap 0 j0) (pswap 1 j1)) (pswap 2 j2)) (pswap 3 j3)) (pswap 4 j4))
      (pswap 5 j5)) (pswap 6 j6))

theorem sign_swap_pow (a b : Fin 8) :
    Perm.sign (swap a b) = (-1) ^ (if b.val = a.val then 0 else 1 : Nat) := by
  rw [Perm.sign_swap']
  by_cases h : a = b
  · subst h
    simp
  · have h' : b.val ≠ a.val := fun h'' => h (Fin.ext h''.symm)
    simp [h, h']

theorem enum_complete_even {f : Nat → Bool} (h : enumS8e f = true) {σ : Perm (Fin 8)}
    (hσ : Perm.sign σ = 1) : f (pn σ) = true := by
  obtain ⟨j0, j1, j2, j3, j4, j5, j6, h0, h1, h2, h3, h4, h5, h6, rfl⟩ := perm8_factor σ
  simp only [enumS8e, List.all_eq_true, List.mem_range'_1] at h
  have key := h j0.val ⟨by omega, by omega⟩ j1.val ⟨by omega, by omega⟩ j2.val ⟨by omega, by omega⟩
    j3.val ⟨by omega, by omega⟩ j4.val ⟨by omega, by omega⟩ j5.val ⟨by omega, by omega⟩ j6.val
    ⟨by omega, by omega⟩
  have hpar : ((if j0.val = 0 then 0 else 1) + (if j1.val = 1 then 0 else 1) +
      (if j2.val = 2 then 0 else 1) + (if j3.val = 3 then 0 else 1) +
      (if j4.val = 4 then 0 else 1) + (if j5.val = 5 then 0 else 1) +
      (if j6.val = 6 then 0 else 1) : Nat) % 2 = 0 := by
    simp only [map_mul, sign_swap_pow] at hσ
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add] at hσ
    have hev := (neg_one_pow_eq_one_iff_even (by decide)).mp hσ
    exact Nat.even_iff.mp hev
  simp only [hpar, bne_self_eq_false, Bool.false_or] at key
  simp only [pn_mul, pn_swap_lit]
  exact key

end CFSG.QuasithinUnique.Vol2Native.L239.L42Insp
