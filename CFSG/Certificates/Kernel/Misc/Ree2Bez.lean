module

public import CFSG.Certificates.Kernel.Misc.Ree2Log

public section

namespace CFSG.KC.Misc.Ree2

open CFSG.KC.Loop Polynomial

section

variable {K : Type*} [Field K] {q1 hf ZT : ℕ} {γ : K}

theorem convAt_eq (q1 ZT A B n lo hi : ℕ) : convAt q1 ZT A B n lo hi =
    loopN (hi + 1 - lo) lo (fun i acc => addL q1 ZT acc (mulL q1 (getP A i) (getP B (n - i))))
      q1 := rfl

theorem LogEnv.convAt_spec (E : LogEnv q1 hf ZT γ) {A B : ℕ} (hA : ∀ i, getP A i ≤ q1)
    (hB : ∀ i, getP B i ≤ q1) (n lo hi : ℕ) : convAt q1 ZT A B n lo hi ≤ q1 ∧
      phi q1 γ (convAt q1 ZT A B n lo hi) =
        ∑ i ∈ Finset.Ico lo (hi + 1), phi q1 γ (getP A i) * phi q1 γ (getP B (n - i)) := by
  rw [convAt_eq]
  obtain ⟨h1, h2⟩ := E.loopN_addL (u := fun i => mulL q1 (getP A i) (getP B (n - i)))
    (hi + 1 - lo) lo q1 (fun i _ _ => (E.mulL_spec (hA i) (hB _)).1) le_rfl
  refine ⟨h1, ?_⟩
  rw [h2, phi_q1, zero_add, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (E.mulL_spec (hA _) (hB _)).2

theorem coeff_mul_window {S P : K[X]} {a b : ℕ → K} {ls D : ℕ}
    (hS : ∀ i, S.coeff i = if i < ls then a i else 0)
    (hP : ∀ j, P.coeff j = if j ≤ D then b j else 0) (hls : 0 < ls) (n : ℕ) :
    (S * P).coeff n = ∑ i ∈ Finset.Ico (n - D) (min n (ls - 1) + 1), a i * b (n - i) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h : ∀ i ∈ Finset.range n.succ, S.coeff i * P.coeff (n - i) =
      if i ∈ Finset.Ico (n - D) (min n (ls - 1) + 1) then a i * b (n - i) else 0 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [hS, hP]
    simp only [Finset.mem_Ico]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_mem]
  congr 1
  ext i
  simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_Ico]
  omega

theorem sum_shift_eq (D n : ℕ) (F : ℕ → K) :
    (∑ j ∈ Finset.range (D + 1), if n = 2 * D - 2 * j then F j else 0) =
      if n ≤ 2 * D ∧ n % 2 = 0 then F (D - n / 2) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (D - n / 2)]
    · rw [ite_eq_left (by omega)]
    · intro j hj hne
      simp only [Finset.mem_range] at hj
      rw [ite_eq_right (by omega)]
    · intro hn
      simp only [Finset.mem_range] at hn
      omega
  · refine Finset.sum_eq_zero fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [ite_eq_right (by omega)]

theorem LogEnv.getP_p1Pack (E : LogEnv q1 hf ZT γ) (hq : q1 < 65535) {D ζ : ℕ} {p' : List ℕ}
    (hp' : ∀ x ∈ p', x ≤ q1) (hζ : ζ ≤ q1) (n : ℕ) :
    getP (p1Pack q1 D ζ p') n = if n ≤ 2 * D then
      (if n % 2 = 0 then mulL q1 (p'.getD (D - n / 2) q1) (powL q1 ζ (D - n / 2)) else q1)
    else 0 := by
  set v : ℕ → ℕ := fun n => nIf(Nat.beq (Nat.mod n (nat_lit 2)) (nat_lit 0),
      strictN (Nat.sub D (Nat.div n (nat_lit 2))) (fun j => mulL q1 (nthL q1 p' j) (powL q1 ζ j)),
      q1) with hv
  have hv' : ∀ n, v n = if n % 2 = 0 then
      mulL q1 (p'.getD (D - n / 2) q1) (powL q1 ζ (D - n / 2)) else q1 := by
    intro n
    simp only [hv, nIf_eq, nbeq, sN, nthL_eq, decide_eq_true_eq]
    rfl
  have hgd : ∀ j, p'.getD j q1 ≤ q1 := by
    intro j
    rw [List.getD_eq_getElem?_getD]
    cases h : p'[j]? with
    | none => exact le_rfl
    | some a => exact hp' a (List.mem_of_getElem? h)
  have hvl : ∀ n, v n < 2 ^ 16 := by
    intro n
    rw [hv']
    split_ifs
    · exact (E.mulL_spec (hgd _) (E.powL_spec hζ _).1).1.trans_lt (by omega)
    · omega
  have hP : p1Pack q1 D ζ p' =
      loopN (2 * D + 1) 0 (fun n P => Nat.lor P (Nat.shiftLeft (v n) (Nat.mul 16 n))) 0 := by
    unfold p1Pack
    congr 1
    change D + D + 1 = 2 * D + 1
    omega
  rw [hP]
  by_cases h : n ≤ 2 * D
  · rw [ite_eq_left h, ← hv']
    exact fld_loopN_or (w := 16) (by norm_num) hvl (Nat.zero_le _) (by omega)
  · rw [ite_eq_right h]
    exact fld_loopN_or_out (w := 16) (by norm_num) hvl (by omega)

end

@[expose] noncomputable def ptsRec (R : ℕ) (xs : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ ih lo => bAnd(Nat.ble lo x, bAnd(Nat.blt x R, ih (Nat.succ x)))) xs

theorem ptsRec_spec {R : ℕ} : ∀ (xs : List ℕ) (lo : ℕ), ptsRec R xs lo = true →
    (∀ x ∈ xs, lo ≤ x ∧ x < R) ∧ xs.Pairwise (· < ·)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | x :: l, lo, h => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (ptsRec R l (Nat.succ x)) (Nat.blt x R)) (Nat.ble lo x) = true at h
    rw [bA, bA, nble, nblt] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨h4, h5⟩ := ptsRec_spec l (x + 1) h3
    refine ⟨fun y hy => ?_, List.Pairwise.cons (fun y hy => by have := h4 y hy; omega) h5⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨h1, h2⟩
    · have := h4 y hy
      omega

theorem ptsOK_spec {D R : ℕ} {xs : List ℕ} (h : ptsOK D R xs = true) :
    xs.length = D + 1 ∧ (∀ x ∈ xs, x < R) ∧ xs.Pairwise (· < ·) := by
  change Bool.rec (motive := fun _ => Bool) false (ptsRec R xs 0)
    (Nat.beq (lenL xs) (Nat.succ D)) = true at h
  rw [bA] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h3, h4⟩ := ptsRec_spec xs 0 h2
  refine ⟨?_, fun x hx => (h3 x hx).2, h4⟩
  have := Nat.eq_of_beq_eq_true h1
  rw [lenL_eq] at this
  exact this

end CFSG.KC.Misc.Ree2

end
