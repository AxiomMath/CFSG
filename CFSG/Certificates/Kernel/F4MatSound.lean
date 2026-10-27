module

public import Certificates.Data.Kernel.F4Mat
public import CFSG.Monster.B.TwoA.Unitary.Form
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.F4M

open CFSG.KC.Loop CFSG.Fischer CFSG.KLie.CT CFSG.Monster.B.TwoA.Unitary Matrix CFSG.LieType.Universal.Unitary

@[expose] noncomputable def decM (P : Nat) : Matrix (Fin 6) (Fin 6) F4 :=
  Matrix.of fun i => vec6 (fget P i.val 12)

@[expose] def cF4 (c : Nat) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩

namespace Aux

theorem fget2_eq' (X i : ℕ) : fget X i 2 = X >>> (2 * i) % 4 := by
  change (X >>> (i * 2)) &&& (pw2 2 - 1) = _
  change (X >>> (i * 2)) &&& (2 ^ 2 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm]

theorem fget2_lt (X i : ℕ) : fget X i 2 < 4 := by
  rw [fget2_eq']
  exact Nat.mod_lt _ (by decide)

theorem fm_spec {a b : ℕ} (ha : a < 4) (hb : b < 4) : cF4 (fm a b) = cF4 a * cF4 b := by
  interval_cases a <;> interval_cases b <;> rfl

theorem fm_lt (a b : ℕ) : fm a b < 4 := fget2_lt _ _

theorem cF4_xor {a b : ℕ} (ha : a < 4) (hb : b < 4) : cF4 (Nat.xor a b) = cF4 a + cF4 b := by
  interval_cases a <;> interval_cases b <;> rfl

theorem xor_lt4 {a b : ℕ} (ha : a < 4) (hb : b < 4) : Nat.xor a b < 4 :=
  Nat.xor_lt_two_pow (n := 2) ha hb

theorem xorN_spec (f : ℕ → ℕ) (hf : ∀ k, f k < 4) :
    ∀ n, xorN n f < 4 ∧ cF4 (xorN n f) = ∑ k ∈ Finset.range n, cF4 (f k)
  | 0 => ⟨(by decide : (0 : ℕ) < 4), rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := xorN_spec f hf n
    refine ⟨xor_lt4 (hf n) h1, ?_⟩
    change cF4 (Nat.xor (f n) (xorN n f)) = _
    rw [cF4_xor (hf n) h1, h2, Finset.sum_range_succ, add_comm]

theorem cF4_zero : cF4 0 = 0 := rfl

theorem cF4_one : cF4 1 = 1 := rfl

theorem testBit_mod4 (x n : ℕ) : (x % 4).testBit n = (decide (n < 2) && x.testBit n) := by
  rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow]

theorem testBit_mod4096 (x n : ℕ) : (x % 4096).testBit n = (decide (n < 12) && x.testBit n) := by
  rw [show (4096 : ℕ) = 2 ^ 12 from rfl, Nat.testBit_mod_two_pow]

theorem testBit_div4pow (x j n : ℕ) : (x / 4 ^ j).testBit n = x.testBit (n + 2 * j) := by
  rw [show (4 : ℕ) ^ j = 2 ^ (2 * j) by rw [pow_mul]; rfl, Nat.testBit_div_two_pow]

theorem fget12_eq (X i : ℕ) : fget X i 12 = X >>> (12 * i) % 4096 := by
  change (X >>> (i * 12)) &&& (pw2 12 - 1) = _
  change (X >>> (i * 12)) &&& (2 ^ 12 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm]

theorem cF4_ent (P : ℕ) (i j : Fin 6) : cF4 (ent P i j) = decM P i j := by
  change cF4 (fget P (6 * i + j) 2) = vec6 (fget P i 12) j
  unfold vec6 cF4
  congr 2
  rw [fget2_eq', fget12_eq]
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_mod4, testBit_mod4, testBit_mod4, testBit_div4pow, testBit_mod4096,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hn : n < 2
  · have hj := j.2
    rw [decide_eq_true hn, Bool.true_and, Bool.true_and, Bool.true_and,
      decide_eq_true (by omega : n + 2 * (j : ℕ) < 12), Bool.true_and]
    congr 1
    omega
  · rw [decide_eq_false hn, Bool.false_and, Bool.false_and]

noncomputable def rowN (A : Matrix (Fin 6) (Fin 6) F4) (r : ℕ) (c : Fin 6) : F4 :=
  if h : r < 6 then A ⟨r, h⟩ c else 0

open Classical in
noncomputable def subQ (A : Matrix (Fin 6) (Fin 6) F4) (k : ℕ) (S : Finset (Fin 6)) : F4 :=
  ∑ σ : Fin k → Fin 6, if Function.Injective σ ∧ Finset.univ.image σ = S then
    ∏ i : Fin k, rowN A i (σ i) else 0

theorem image_snoc {k : ℕ} (τ : Fin k → Fin 6) (j : Fin 6) :
    Finset.univ.image (Fin.snoc τ j : Fin (k + 1) → Fin 6) = insert j (Finset.univ.image τ) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  rw [Fin.exists_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm), fun h => h.elim (fun h => Or.inr h.symm)
    Or.inl⟩

theorem cond_snoc {k : ℕ} (τ : Fin k → Fin 6) (j : Fin 6) (S : Finset (Fin 6)) :
    (Function.Injective (Fin.snoc τ j : Fin (k + 1) → Fin 6) ∧
      Finset.univ.image (Fin.snoc τ j : Fin (k + 1) → Fin 6) = S) ↔
    j ∈ S ∧ (Function.Injective τ ∧ Finset.univ.image τ = S.erase j) := by
  rw [Fin.snoc_injective_iff, image_snoc]
  have hr : j ∈ Set.range τ ↔ j ∈ Finset.univ.image τ := by simp
  rw [hr]
  constructor
  · rintro ⟨⟨hi, hj⟩, rfl⟩
    exact ⟨Finset.mem_insert_self _ _, hi, (Finset.erase_insert hj).symm⟩
  · rintro ⟨hj, hi, he⟩
    refine ⟨⟨hi, by rw [he]; exact Finset.notMem_erase j S⟩, ?_⟩
    rw [he, Finset.insert_erase hj]

open Classical in
theorem term_snoc (A : Matrix (Fin 6) (Fin 6) F4) (k : ℕ) (S : Finset (Fin 6)) (j : Fin 6)
    (τ : Fin k → Fin 6) :
    (if Function.Injective (Fin.snoc τ j : Fin (k + 1) → Fin 6) ∧
        Finset.univ.image (Fin.snoc τ j : Fin (k + 1) → Fin 6) = S then
      ∏ i : Fin (k + 1), rowN A i ((Fin.snoc τ j : Fin (k + 1) → Fin 6) i) else 0) =
    if j ∈ S then rowN A k j * (if Function.Injective τ ∧ Finset.univ.image τ = S.erase j then
      ∏ i : Fin k, rowN A i (τ i) else 0) else 0 := by
  have hc := cond_snoc τ j S
  by_cases hj : j ∈ S
  · rw [if_pos hj]
    by_cases h : Function.Injective τ ∧ Finset.univ.image τ = S.erase j
    · rw [if_pos (hc.2 ⟨hj, h⟩), if_pos h, Fin.prod_univ_castSucc, mul_comm]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.coe_castSucc, Fin.val_last]
    · rw [if_neg (fun h' => h (hc.1 h').2), if_neg h, mul_zero]
  · rw [if_neg hj, if_neg (fun h' => hj (hc.1 h').1)]

open Classical in
theorem subQ_succ (A : Matrix (Fin 6) (Fin 6) F4) (k : ℕ) (S : Finset (Fin 6)) :
    subQ A (k + 1) S = ∑ j ∈ S, rowN A k j * subQ A k (S.erase j) := by
  unfold subQ
  rw [← Fintype.sum_equiv (Fin.snocEquiv fun _ => Fin 6)
    (fun p : Fin 6 × (Fin k → Fin 6) =>
      if Function.Injective (Fin.snoc p.2 p.1 : Fin (k + 1) → Fin 6) ∧
        Finset.univ.image (Fin.snoc p.2 p.1 : Fin (k + 1) → Fin 6) = S then
      ∏ i : Fin (k + 1), rowN A i ((Fin.snoc p.2 p.1 : Fin (k + 1) → Fin 6) i) else 0) _
    (fun p => rfl), Fintype.sum_prod_type]
  simp only [term_snoc]
  conv_rhs => rw [← Finset.univ_inter S, ← Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ S
  · simp only [if_pos hj]
    rw [Finset.mul_sum]
  · simp only [if_neg hj, Finset.sum_const_zero]

open Classical in
theorem subQ_zero (A : Matrix (Fin 6) (Fin 6) F4) : subQ A 0 ∅ = 1 := by
  unfold subQ
  rw [Fintype.sum_unique]
  rw [if_pos ⟨fun a => a.elim0, by simp⟩, Fin.prod_univ_zero]

theorem sign_smul (σ : Equiv.Perm (Fin 6)) (x : F4) : Equiv.Perm.sign σ • x = x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · exact one_smul _ x
  · rw [Units.neg_smul, one_smul]
    rfl

open Classical in
theorem det_eq_subQ (A : Matrix (Fin 6) (Fin 6) F4) : A.det = subQ A 6 Finset.univ := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [sign_smul, Matrix.transpose_apply]
  unfold subQ
  rw [← Finset.sum_filter]
  have hrow : ∀ σ : Fin 6 → Fin 6, ∏ i : Fin 6, rowN A i (σ i) = ∏ i, A i (σ i) := fun σ =>
    Finset.prod_congr rfl fun i _ => by simp [rowN, i.2]
  simp only [hrow]
  refine Finset.sum_bij (fun π _ => ⇑π) (fun π _ => ?_) (fun a _ b _ h => Equiv.coe_fn_injective h)
    (fun σ hσ => ?_) (fun _ _ => rfl)
  · rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, π.injective, Finset.image_univ_of_surjective π.surjective⟩
  · have hi := (Finset.mem_filter.1 hσ).2.1
    exact ⟨Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hi), Finset.mem_univ _, rfl⟩

noncomputable def bitSet (S : ℕ) : Finset (Fin 6) := Finset.univ.filter fun j => S.testBit j

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem testBit_fget2 (X S i : ℕ) : (fget X S 2).testBit i = (decide (i < 2) && X.testBit (2 * S + i)) := by
  rw [fget2_eq', show (4 : ℕ) = 2 ^ 2 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

theorem fget_append {T v n S : ℕ} (hT : T < 2 ^ (2 * n)) (hv : v < 4) :
    fget (Nat.lor T (Nat.shiftLeft v (Nat.mul 2 n))) S 2 = if S < n then fget T S 2 else
      if S = n then v else 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_fget2]
  change (decide (i < 2) && (T ||| (v <<< (2 * n))).testBit (2 * S + i)) = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : i < 2
  · simp only [hi, decide_true, Bool.true_and]
    split_ifs with h1 h2
    · rw [testBit_fget2, decide_eq_true hi, Bool.true_and]
      have : ¬ (2 * S + i ≥ 2 * n) := by omega
      simp [this]
    · subst h2
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp only [Bool.false_or, ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and,
        Nat.add_sub_cancel_left]
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.zero_testBit]
      have hv' : v < 2 ^ (2 * S + i - 2 * n) :=
        lt_of_lt_of_le hv (by
          change 2 ^ 2 ≤ _
          exact Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hv']
      simp
  · simp only [hi, decide_false, Bool.false_and]
    have hlt : (if S < n then fget T S 2 else if S = n then v else 0) < 2 ^ i :=
      lt_of_lt_of_le (by split_ifs <;> first | exact fget2_lt _ _ | exact hv | decide)
        (by change 2 ^ 2 ≤ _; exact Nat.pow_le_pow_right (by decide) (by omega))
    exact (Nat.testBit_lt_two_pow hlt).symm

theorem setOf_card (S : ℕ) : (bitSet S).card = popc 6 S := by
  unfold bitSet
  exact card_eq_popc' 6 S
  where
    card_eq_popc' (N X : ℕ) :
        (Finset.univ.filter fun y : Fin N => X.testBit y = true).card = popc N X := by
      rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun y => if X.testBit y = true then 1 else 0) N,
        popc]
      induction N with
      | zero => rfl
      | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        change _ = Nat.add (Nat.land (Nat.shiftRight X N) 1) (sumN N _)
        have e : Nat.land (Nat.shiftRight X N) 1 = (X >>> N) % 2 := Nat.and_one_is_mod _
        have e2 : X.testBit N = decide ((X >>> N) % 2 = 1) := by
          rw [← Nat.testBit_zero, Nat.testBit_shiftRight, Nat.add_zero]
        rw [e, e2, Nat.add_comm]
        rcases Nat.mod_two_eq_zero_or_one (X >>> N) with h | h <;> rw [h] <;> rfl

theorem sub_bit : ∀ n < 64, ∀ j < 6, n.testBit j = true → n - 2 ^ j < n ∧
    ∀ i < 6, (n - 2 ^ j).testBit i = (decide (i ≠ j) && n.testBit i) := by
  decide

theorem setOf_sub {n : ℕ} (hn : n < 64) (j : Fin 6) (hj : n.testBit j = true) :
    bitSet (n - pw2 j) = (bitSet n).erase j := by
  have e : pw2 j = 2 ^ (j : ℕ) := by
    change 1 <<< (j : ℕ) = _
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  rw [e]
  ext i
  have h := (sub_bit n hn j j.2 hj).2 i i.2
  simp only [bitSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, h,
    Bool.and_eq_true, decide_eq_true_eq, ne_eq, Fin.val_inj]

theorem setOf_zero : bitSet 0 = ∅ := by
  ext i
  simp [bitSet]

theorem setOf_ne {n : ℕ} (hn : n < 64) (h0 : n ≠ 0) : 0 < (bitSet n).card := by
  rw [Finset.card_pos]
  have : ∀ n < 64, n ≠ 0 → ∃ j < 6, n.testBit j = true := by decide
  obtain ⟨j, hj, h⟩ := this n hn h0
  exact ⟨⟨j, hj⟩, by simp [bitSet, h]⟩

theorem detTab_spec (P : ℕ) : ∀ n ≤ 64, detTab P n < 2 ^ (2 * n) ∧
    ∀ S < n, cF4 (fget (detTab P n) S 2) = subQ (decM P) (bitSet S).card (bitSet S)
  | 0, _ => ⟨(by decide : (0 : ℕ) < 2 ^ (2 * 0)), fun S h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    obtain ⟨hT, hS⟩ := detTab_spec P n (by omega)
    set v := nIf(Nat.beq n (nat_lit 0), nat_lit 1, detStep P (detTab P n) n) with hvdef
    have e : detTab P (n + 1) = Nat.lor (detTab P n) (Nat.shiftLeft v (Nat.mul 2 n)) := by
      change strictN (detTab P n) (fun T => Nat.lor T (Nat.shiftLeft
        (nIf(Nat.beq n (nat_lit 0), nat_lit 1, detStep P T n)) (Nat.mul (nat_lit 2) n))) = _
      rw [strictN_eq]
    rw [e]
    have hstep : ∀ j, (nIf(bit n j, fm (ent P (Nat.sub (popc (nat_lit 6) n) (nat_lit 1)) j)
        (fget (detTab P n) (Nat.sub n (pw2 j)) (nat_lit 2)), nat_lit 0)) < 4 := by
      intro j
      cases bit n j
      · exact (by decide : (0 : ℕ) < 4)
      · exact fm_lt _ _
    have hv : v < 4 := by
      rw [hvdef]
      cases Nat.beq n 0
      · exact (xorN_spec _ hstep 6).1
      · exact (by decide : (1 : ℕ) < 4)
    refine ⟨?_, fun S hS' => ?_⟩
    · exact append_lt hT hv
    · rw [fget_append hT hv]
      by_cases hlt : S < n
      · rw [if_pos hlt]
        exact hS S hlt
      · have hSn : S = n := by omega
        rw [if_neg hlt, if_pos hSn]
        subst hSn
        rcases Nat.eq_zero_or_pos S with rfl | hpos
        · rw [setOf_zero, Finset.card_empty, subQ_zero]
          rfl
        · have hnz : Nat.beq S 0 = false := by
            rw [Bool.eq_false_iff]
            intro h
            exact (by omega : S ≠ 0) (Nat.eq_of_beq_eq_true h)
          rw [hvdef, hnz]
          change cF4 (xorN 6 _) = _
          rw [(xorN_spec _ hstep 6).2]
          obtain ⟨k, hk⟩ : ∃ k, (bitSet S).card = k + 1 :=
            ⟨(bitSet S).card - 1, by have := setOf_ne (by omega) (by omega : S ≠ 0); omega⟩
          rw [hk, subQ_succ]
          rw [← Fin.sum_univ_eq_sum_range (fun j => cF4 (nIf(bit S j, fm (ent P (Nat.sub (popc 6 S) 1) j)
            (fget (detTab P S) (Nat.sub S (pw2 j)) 2), 0))) 6]
          have hsplit : ∑ j ∈ bitSet S, rowN (decM P) k j * subQ (decM P) k ((bitSet S).erase j) =
              ∑ j : Fin 6, if S.testBit j = true then
                rowN (decM P) k j * subQ (decM P) k ((bitSet S).erase j) else 0 := by
            unfold bitSet
            rw [Finset.sum_filter]
          rw [hsplit]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [bit_eq']
          by_cases hb : S.testBit j = true
          · rw [if_pos hb, hb]
            change cF4 (fm _ _) = _
            have hpop : Nat.sub (popc 6 S) 1 = k := by
              rw [← setOf_card, hk]
              rfl
            have hent : ent P (Nat.sub (popc 6 S) 1) j < 4 := fget2_lt _ _
            rw [fm_spec hent (fget2_lt _ _), hpop]
            have hk6 : k < 6 := by
              have := Finset.card_le_univ (bitSet S)
              rw [Fintype.card_fin] at this
              omega
            have hrow : cF4 (ent P k j) = rowN (decM P) k j := by
              rw [rowN, dif_pos hk6]
              exact cF4_ent P ⟨k, hk6⟩ j
            have hsub := sub_bit S (by omega) j j.2 hb
            have e2 : pw2 j = 2 ^ (j : ℕ) := by
              change 1 <<< (j : ℕ) = _
              rw [Nat.shiftLeft_eq, Nat.one_mul]
            have hq := hS (S - pw2 j) (by rw [e2]; exact hsub.1)
            rw [hrow]
            change _ * cF4 (fget (detTab P S) (S - pw2 j) 2) = _
            rw [hq, setOf_sub (by omega) j hb, Finset.card_erase_of_mem (by simp [bitSet, hb]), hk]
            rfl
          · rw [if_neg hb]
            rw [Bool.not_eq_true] at hb
            rw [hb]
            rfl
  where
    append_lt {T v n : ℕ} (hT : T < 2 ^ (2 * n)) (hv : v < 4) :
        Nat.lor T (Nat.shiftLeft v (Nat.mul 2 n)) < 2 ^ (2 * (n + 1)) := by
      have h1 : T < 2 ^ (2 * (n + 1)) := lt_of_lt_of_le hT (Nat.pow_le_pow_right (by decide) (by omega))
      have h2 : Nat.shiftLeft v (Nat.mul 2 n) < 2 ^ (2 * (n + 1)) := by
        change v <<< (2 * n) < _
        rw [Nat.shiftLeft_eq, show 2 * (n + 1) = 2 + 2 * n by ring, pow_add]
        exact Nat.mul_lt_mul_of_pos_right (by simpa using hv) (by positivity)
      exact Nat.or_lt_two_pow h1 h2
    bit_eq' (X i : ℕ) : bit X i = X.testBit i := by
      have h1 : (X >>> i) &&& 1 = X / 2 ^ i % 2 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.and_two_pow_sub_one_eq_mod _ 1
      change Nat.beq ((X >>> i) &&& 1) 1 = _
      rw [h1, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ i) with h | h <;> rw [h] <;> rfl

end Aux

open Aux

theorem det_sound (P : Nat) : (decM P).det = cF4 (det P) := by
  rw [det_eq_subQ]
  change _ = cF4 (strictN P fun P => fget (detTab P 64) 63 2)
  rw [strictN_eq, (detTab_spec P 64 le_rfl).2 63 (by decide)]
  have h : bitSet 63 = Finset.univ := by
    ext i
    fin_cases i <;> simp [bitSet] <;> decide
  rw [h, Finset.card_univ, Fintype.card_fin]

theorem cF4_sq {c : Nat} (hc : c < 4) : cF4 c ^ 2 = cF4 (sqC c) := by
  interval_cases c <;> rfl


namespace Aux

theorem testBit_orN (n i : ℕ) (f : ℕ → ℕ) :
    (orN n f).testBit i = true ↔ ∃ t < n, (f t).testBit i = true := by
  induction n with
  | zero => simp [orN]
  | succ n ih =>
    change ((f n) ||| orN n f).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨t, Nat.lt_succ_of_lt ht, h⟩
    · rintro ⟨t, ht, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact Or.inr ⟨t, ht, h⟩
      · exact Or.inl h

theorem testBit_mkTerm (c t i : ℕ) :
    (Nat.shiftLeft (Nat.land c 3) (Nat.mul 2 t)).testBit i =
      (decide (2 * t ≤ i) && decide (i < 2 * t + 2) && c.testBit (i - 2 * t)) := by
  change ((c &&& 3) <<< (2 * t)).testBit i = _
  rw [Nat.testBit_shiftLeft, show (3 : ℕ) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.testBit_mod_two_pow]
  by_cases h1 : 2 * t ≤ i
  · simp only [ge_iff_le, h1, decide_true, Bool.true_and]
    congr 1
    exact decide_eq_decide.2 (by omega)
  · simp [h1]

theorem cF4_ent_mk (f : ℕ → ℕ → ℕ) (i j : Fin 6) : cF4 (ent (mk f) i j) = cF4 (f i j) := by
  unfold cF4
  congr 2
  change fget (mk f) (6 * i + j) 2 % 4 = _
  rw [Nat.mod_eq_of_lt (fget2_lt _ _)]
  apply Nat.eq_of_testBit_eq
  intro n
  rw [testBit_fget2, testBit_mod4]
  by_cases hn : n < 2
  · rw [decide_eq_true hn, Bool.true_and, Bool.true_and]
    apply Bool.eq_iff_iff.2
    unfold mk
    rw [testBit_orN]
    have hi := i.2
    have hj := j.2
    constructor
    · rintro ⟨t, ht, h⟩
      rw [testBit_mkTerm] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have e1 : t = 6 * i + j := by omega
      subst e1
      have e2 : 2 * (6 * (i : ℕ) + j) + n - 2 * (6 * i + j) = n := by omega
      have e3 : Nat.div (6 * (i : ℕ) + j) 6 = i := by
        change (6 * (i : ℕ) + j) / 6 = i
        omega
      have e4 : Nat.mod (6 * (i : ℕ) + j) 6 = j := by
        change (6 * (i : ℕ) + j) % 6 = j
        omega
      rw [e2, e3, e4] at h3
      exact h3
    · intro h
      refine ⟨6 * i + j, (by omega : 6 * (i : ℕ) + j < 36), ?_⟩
      rw [testBit_mkTerm]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      have e2 : 2 * (6 * (i : ℕ) + j) + n - 2 * (6 * i + j) = n := by omega
      have e3 : Nat.div (6 * (i : ℕ) + j) 6 = i := by
        change (6 * (i : ℕ) + j) / 6 = i
        omega
      have e4 : Nat.mod (6 * (i : ℕ) + j) 6 = j := by
        change (6 * (i : ℕ) + j) % 6 = j
        omega
      rw [e2, e3, e4]
      exact ⟨⟨by omega, by omega⟩, h⟩
  · rw [decide_eq_false hn, Bool.false_and, Bool.false_and]

theorem ent_lt (P i j : ℕ) : ent P i j < 4 := fget2_lt _ _

end Aux

theorem decM_mmul (P Q : Nat) : decM (mmul P Q) = decM P * decM Q := by
  ext i j
  rw [← cF4_ent]
  unfold mmul
  rw [strictN_eq, strictN_eq, cF4_ent_mk, (xorN_spec _ (fun k => fm_lt _ _) 6).2, Matrix.mul_apply,
    ← Fin.sum_univ_eq_sum_range (fun k => cF4 (fm (ent P i k) (ent Q k j))) 6]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fm_spec (ent_lt _ _ _) (ent_lt _ _ _), cF4_ent, cF4_ent]

namespace Aux

theorem ent_xor (P Q i j : ℕ) : ent (Nat.xor P Q) i j = Nat.xor (ent P i j) (ent Q i j) := by
  apply Nat.eq_of_testBit_eq
  intro n
  change (fget (P ^^^ Q) _ 2).testBit n = ((fget P _ 2) ^^^ (fget Q _ 2)).testBit n
  rw [testBit_fget2, Nat.testBit_xor, Nat.testBit_xor, testBit_fget2, testBit_fget2]
  cases decide (n < 2) <;> rfl

end Aux

theorem decM_xor (P Q : Nat) : decM (Nat.xor P Q) = decM P + decM Q := by
  ext i j
  rw [← cF4_ent, ent_xor, cF4_xor (ent_lt _ _ _) (ent_lt _ _ _), cF4_ent, cF4_ent]
  rfl

theorem decM_trn (P : Nat) : decM (trn P) = (decM P)ᵀ := by
  ext i j
  rw [← cF4_ent]
  unfold trn
  rw [strictN_eq, cF4_ent_mk, cF4_ent]
  rfl

theorem decM_barM (P : Nat) : decM (barM P) = (decM P).map fun a => a ^ 2 := by
  ext i j
  rw [← cF4_ent]
  unfold barM
  rw [strictN_eq, cF4_ent_mk, Matrix.map_apply, ← cF4_ent, cF4_sq (ent_lt _ _ _)]

theorem tr_sound (P : Nat) : (decM P).trace = cF4 (tr P) ∧ tr P < 4 := by
  unfold tr
  rw [strictN_eq]
  obtain ⟨h1, h2⟩ := xorN_spec (fun i => ent P i i) (fun i => ent_lt _ _ _) 6
  refine ⟨?_, h1⟩
  rw [h2, Matrix.trace, ← Fin.sum_univ_eq_sum_range (fun i => cF4 (ent P i i)) 6]
  exact Finset.sum_congr rfl fun i _ => (cF4_ent P i i).symm

theorem decM_ONE : decM ONE = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem decM_ANTI : decM ANTI = antidiag 6 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem decM_E23 : decM E23 = Matrix.single 2 3 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cF4_ne {c d : Nat} (hc : c < 4) (hd : d < 4) (h : Nat.beq c d = false) : cF4 c ≠ cF4 d := by
  intro heq
  have h2 : c % 4 = d % 4 := congrArg (fun x : F4 => x.code.val) heq
  rw [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd] at h2
  subst h2
  rw [Nat.beq_refl] at h
  exact Bool.noConfusion h

end CFSG.KC.F4M

end
