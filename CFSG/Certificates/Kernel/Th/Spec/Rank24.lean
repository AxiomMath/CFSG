module

public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.Spec.DceMat
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.KC.Th.Spec.Rank24

open CFSG.KC.Th CFSG.KC.Th.Spec.Dce

private theorem land_sub_one_add (x : ℕ) (hx : x ≠ 0) :
    ∃ t, x.testBit t = true ∧ (x &&& (x - 1)) + 2 ^ t = x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · obtain ⟨t, ht, e⟩ := ih (x / 2) (by omega) (by omega)
      have hxy : x &&& (x - 1) = 2 * (x / 2 &&& (x / 2 - 1)) := by
        apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          rw [Nat.testBit_and]
          simp [Nat.testBit_zero, h]
        | succ j =>
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
            show (x - 1) / 2 = x / 2 - 1 by omega,
            show 2 * (x / 2 &&& (x / 2 - 1)) / 2 = x / 2 &&& (x / 2 - 1) by omega, Nat.testBit_and]
      refine ⟨t + 1, by rw [Nat.testBit_succ]; exact ht, ?_⟩
      rw [hxy, Nat.pow_succ]
      omega
    · have hxy : x &&& (x - 1) = x - 1 := by
        apply Nat.eq_of_testBit_eq
        intro j
        cases j with
        | zero =>
          have : (x - 1) % 2 = 0 := by omega
          rw [Nat.testBit_and]
          simp [Nat.testBit_zero, h, this]
        | succ j =>
          rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ,
            show (x - 1) / 2 = x / 2 by omega, Bool.and_self]
      refine ⟨0, by simp [Nat.testBit_zero, h], ?_⟩
      rw [hxy, Nat.pow_zero]
      omega

private theorem lowBit_eq {x : ℕ} (hx : x ≠ 0) :
    ∃ t, x.testBit t = true ∧ OutS.lowBit x = 2 ^ t := by
  obtain ⟨t, ht, e⟩ := land_sub_one_add x hx
  exact ⟨t, ht, Nat.sub_eq_of_eq_add (e.symm.trans (Nat.add_comm _ _))⟩

private noncomputable def piv (b : ℕ) : ℕ := Nat.log2 (OutS.lowBit b)

private theorem piv_spec {b : ℕ} (hb : b ≠ 0) :
    OutS.lowBit b = 2 ^ piv b ∧ b.testBit (piv b) = true := by
  obtain ⟨t, ht, e⟩ := lowBit_eq hb
  have hp : piv b = t := by rw [piv, e, Nat.log2_two_pow]
  rw [hp]
  exact ⟨e, ht⟩

private theorem pos_and_two_pow_iff (a p : ℕ) : 0 < a &&& 2 ^ p ↔ a.testBit p = true := by
  constructor
  · intro h
    by_contra hb
    have h0 : a &&& 2 ^ p = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hi : p = i
      · subst hi
        simpa using hb
      · simp [hi]
    omega
  · intro h
    apply Nat.pos_of_ne_zero
    intro h0
    have := congrArg (fun n => n.testBit p) h0
    simp [Nat.testBit_and, h] at this

private theorem toVec_xor (x y : ℕ) : toVec (x ^^^ y) = toVec x + toVec y := by
  funext j
  simp only [toVec, Pi.add_apply, Nat.testBit_xor]
  exact cast_xor _ _

private theorem toVec_zero : toVec 0 = 0 := by
  funext j
  simp [toVec]

private theorem toMat_xor (A B : ℕ) : toMat (A ^^^ B) = toMat A + toMat B := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor]
  exact cast_xor _ _

private noncomputable def bspan (B k : ℕ) : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Submodule.span (ZMod 2) {x | ∃ i < k, toVec (rowOf B i) = x}

private theorem bspan_succ (B k : ℕ) :
    bspan B (k + 1) = Submodule.span (ZMod 2) {toVec (rowOf B k)} ⊔ bspan B k := by
  unfold bspan
  rw [← Submodule.span_insert]
  congr 1
  ext x
  simp only [Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact Or.inr ⟨i, hi, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨k, Nat.lt_succ_self k, rfl⟩
    · exact ⟨i, Nat.lt_succ_of_lt hi, rfl⟩

private theorem bspan_mono (B : ℕ) {m n : ℕ} (h : m ≤ n) : bspan B m ≤ bspan B n :=
  Submodule.span_mono fun _ ⟨i, hi, e⟩ => ⟨i, by omega, e⟩

private theorem mem_bspan {B k i : ℕ} (hi : i < k) : toVec (rowOf B i) ∈ bspan B k :=
  Submodule.subset_span ⟨i, hi, rfl⟩

private theorem bspan_congr {B B' k : ℕ} (h : ∀ i < k, rowOf B' i = rowOf B i) :
    bspan B' k = bspan B k := by
  unfold bspan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [h i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [h i hi]⟩

private theorem sup_span_eq {W : Submodule (ZMod 2) (Fin 24 → ZMod 2)} {u v : Fin 24 → ZMod 2}
    (h : v - u ∈ W) :
    Submodule.span (ZMod 2) {v} ⊔ W = Submodule.span (ZMod 2) {u} ⊔ W := by
  apply le_antisymm
  · refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 ?_) le_sup_right
    have := Submodule.add_mem_sup (Submodule.mem_span_singleton_self u) h
    simpa using this
  · refine sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 ?_) le_sup_right
    have := sub_mem (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
      (Submodule.mem_sup_right h : v - u ∈ Submodule.span (ZMod 2) {v} ⊔ W)
    simpa using this

private theorem toVec_rowOf_toMat (M : ℕ) (i : Fin 24) : toVec (rowOf M i) = (toMat M).row i := by
  funext j
  rw [Matrix.row_apply]
  simp only [toVec, toMat, Matrix.of_apply, testBit_rowOf]
  simp

private theorem bspan_rows (M : ℕ) :
    bspan M 24 = Submodule.span (ZMod 2) (Set.range (toMat M).row) := by
  unfold bspan
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, (toVec_rowOf_toMat M ⟨i, hi⟩).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, toVec_rowOf_toMat M i⟩

private theorem linIndep {B k : ℕ} (hne : ∀ i < k, rowOf B i ≠ 0)
    (htri : ∀ i j, i < j → j < k → (rowOf B j).testBit (piv (rowOf B i)) = false) :
    LinearIndependent (ZMod 2) (fun i : Fin k => toVec (rowOf B i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ n, ∀ i : Fin k, (i : ℕ) = n → g i = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hin
      have hp := (piv_spec (hne i i.2)).2
      have hp24 : piv (rowOf B i) < 24 := by
        by_contra hge
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (rowOf_lt B i)
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hge)))] at hp
        exact Bool.false_ne_true hp
      have hc := congrFun hg ⟨piv (rowOf B i), hp24⟩
      rw [Finset.sum_apply, Finset.sum_eq_single i] at hc
      · simpa [toVec, hp] using hc
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with hlt | hlt
        · have : g j = 0 := ih j (lt_of_lt_of_eq (Fin.lt_def.1 hlt) hin) j rfl
          simp [this]
        · simp [toVec, htri i j hlt j.2]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
  exact fun i => key i i rfl

private theorem finrank_bspan {B k : ℕ} (hne : ∀ i < k, rowOf B i ≠ 0)
    (htri : ∀ i j, i < j → j < k → (rowOf B j).testBit (piv (rowOf B i)) = false) :
    Module.finrank (ZMod 2) (bspan B k) = k := by
  have hset : {x | ∃ i < k, toVec (rowOf B i) = x} =
      Set.range (fun i : Fin k => toVec (rowOf B i)) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
  rw [bspan, hset, finrank_span_eq_card (linIndep hne htri), Fintype.card_fin]

private theorem reduce_succ (B n v : ℕ) : OutS.reduce B (n + 1) v =
    Bool.rec (motive := fun _ => ℕ) (OutS.reduce B n v) (OutS.reduce B n v ^^^ rowOf B n)
      (Nat.blt 0 (OutS.reduce B n v &&& OutS.lowBit (rowOf B n))) := rfl

private theorem reduce_spec {B k v : ℕ} (hv : v < 2 ^ 24) (hne : ∀ i < k, rowOf B i ≠ 0)
    (htri : ∀ i j, i < j → j < k → (rowOf B j).testBit (piv (rowOf B i)) = false) :
    ∀ n ≤ k, OutS.reduce B n v < 2 ^ 24 ∧
      (∀ i < n, (OutS.reduce B n v).testBit (piv (rowOf B i)) = false) ∧
      toVec (OutS.reduce B n v) - toVec v ∈ bspan B n
  | 0, _ => ⟨hv, fun i hi => absurd hi (Nat.not_lt_zero i), by
      rw [show OutS.reduce B 0 v = v from rfl, sub_self]
      exact zero_mem _⟩
  | n + 1, hn => by
    obtain ⟨h1, h2, h3⟩ := reduce_spec hv hne htri n (by omega)
    obtain ⟨hl, hp⟩ := piv_spec (hne n (by omega))
    rw [reduce_succ, hl]
    generalize OutS.reduce B n v = a at h1 h2 h3 ⊢
    cases hb : Nat.blt 0 (a &&& 2 ^ piv (rowOf B n))
    · have ha : a.testBit (piv (rowOf B n)) = false := by
        cases hab : a.testBit (piv (rowOf B n))
        · rfl
        · have := Nat.blt_eq.mpr ((pos_and_two_pow_iff _ _).2 hab)
          rw [hb] at this
          exact absurd this Bool.false_ne_true
      refine ⟨h1, fun i hi => ?_, bspan_mono B (Nat.le_succ n) h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h2 i hi
      · exact ha
    · have ha : a.testBit (piv (rowOf B n)) = true :=
        (pos_and_two_pow_iff _ _).1 (Nat.blt_eq.mp hb)
      refine ⟨Nat.xor_lt_two_pow h1 (rowOf_lt B n), fun i hi => ?_, ?_⟩
      · show (a ^^^ rowOf B n).testBit _ = false
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · simp [Nat.testBit_xor, h2 i hi, htri i n hi (by omega)]
        · simp [Nat.testBit_xor, ha, hp]
      · show toVec (a ^^^ rowOf B n) - toVec v ∈ bspan B (n + 1)
        rw [toVec_xor, add_sub_right_comm]
        exact add_mem (bspan_mono B (Nat.le_succ n) h3) (mem_bspan (Nat.lt_succ_self n))

private structure Good (M r k B : ℕ) : Prop where
  hle : k ≤ r
  hlt : B < 2 ^ (24 * k)
  hne : ∀ i < k, rowOf B i ≠ 0
  htri : ∀ i j, i < j → j < k → (rowOf B j).testBit (piv (rowOf B i)) = false
  hspan : bspan B k = bspan M r

private theorem pack_and {a c : ℕ} (ha : a < 32) : (a ||| (c <<< 5)) &&& 31 = a := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, show (31 : ℕ) = 2 ^ 5 - 1 from rfl,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 5
  · simp [hi, show ¬ (i ≥ 5) by omega]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show a < 2 ^ 5 from ha)
      (Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ i)))]
    simp [hi]

private theorem pack_shr {a c : ℕ} (ha : a < 32) : (a ||| (c <<< 5)) >>> 5 = c := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (show a < 2 ^ 5 from ha)
      (Nat.pow_le_pow_right (by omega) (by omega : 5 ≤ 5 + i)))]
  simp

private theorem rowOf_or_lt {B v k i : ℕ} (hi : i < k) :
    rowOf (B ||| (v <<< (24 * k))) i = rowOf B i := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowOf, testBit_rowOf, Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hj : j < 24
  · simp [hj, show ¬ (24 * i + j ≥ 24 * k) by omega]
  · simp [hj]

private theorem rowOf_or_eq {B v k : ℕ} (hB : B < 2 ^ (24 * k)) (hv : v < 2 ^ 24) :
    rowOf (B ||| (v <<< (24 * k))) k = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowOf, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hB
      (Nat.pow_le_pow_right (by omega) (by omega : 24 * k ≤ 24 * k + j))),
    show 24 * k + j - 24 * k = j by omega]
  by_cases hj : j < 24
  · simp [hj]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
      (Nat.pow_le_pow_right (by omega) (by omega : 24 ≤ j)))]
    simp [hj]

private theorem or_lt {B v k : ℕ} (hB : B < 2 ^ (24 * k)) (hv : v < 2 ^ 24) :
    B ||| (v <<< (24 * k)) < 2 ^ (24 * (k + 1)) := by
  apply Nat.or_lt_two_pow
  · exact Nat.lt_of_lt_of_le hB (Nat.pow_le_pow_right (by omega) (by omega))
  · rw [Nat.shiftLeft_eq, show 24 * (k + 1) = 24 + 24 * k by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_right hv (Nat.two_pow_pos _)

private theorem good_zero {M r k B : ℕ} (h : Good M r k B)
    (hv : OutS.reduce B k (rowOf M r) = 0) : Good M (r + 1) k B := by
  obtain ⟨-, -, hvs⟩ := reduce_spec (rowOf_lt M r) h.hne h.htri k le_rfl
  rw [hv, toVec_zero, zero_sub, neg_mem_iff] at hvs
  refine ⟨Nat.le_succ_of_le h.hle, h.hlt, h.hne, h.htri, ?_⟩
  rw [bspan_succ M r, ← h.hspan]
  exact (sup_eq_right.2 ((Submodule.span_singleton_le_iff_mem _ _).2 hvs)).symm

private theorem good_pos {M r k B : ℕ} (h : Good M r k B)
    (hv : 0 < OutS.reduce B k (rowOf M r)) :
    Good M (r + 1) (k + 1) (B ||| (OutS.reduce B k (rowOf M r) <<< (24 * k))) := by
  obtain ⟨hvlt, hvp, hvs⟩ := reduce_spec (rowOf_lt M r) h.hne h.htri k le_rfl
  generalize OutS.reduce B k (rowOf M r) = v at hv hvlt hvp hvs ⊢
  have hrow : ∀ i < k, rowOf (B ||| (v <<< (24 * k))) i = rowOf B i :=
    fun i hi => rowOf_or_lt hi
  have hrowk : rowOf (B ||| (v <<< (24 * k))) k = v := rowOf_or_eq h.hlt hvlt
  refine ⟨Nat.succ_le_succ h.hle, or_lt h.hlt hvlt, fun i hi => ?_, fun i j hij hj => ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [hrow i hi]
      exact h.hne i hi
    · rw [hrowk]
      exact Nat.pos_iff_ne_zero.1 hv
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hrow i (hij.trans hj), hrow j hj]
      exact h.htri i j hij hj
    · rw [hrow i hij, hrowk]
      exact hvp i hij
  · rw [bspan_succ, bspan_succ, hrowk, bspan_congr hrow, ← h.hspan]
    exact sup_span_eq hvs

private theorem good_step {M r S : ℕ} (hr : r < 24) (h : Good M r (S &&& 31) (S >>> 5)) :
    Good M (r + 1) (OutS.rankStep M r S &&& 31) (OutS.rankStep M r S >>> 5) := by
  have hstep : OutS.rankStep M r S = Bool.rec (motive := fun _ => ℕ) S
      (((S &&& 31) + 1) ||| (((S >>> 5) ||| (OutS.reduce (S >>> 5) (S &&& 31) (rowOf M r) <<<
        (24 * (S &&& 31)))) <<< 5))
      (Nat.blt 0 (OutS.reduce (S >>> 5) (S &&& 31) (rowOf M r))) := rfl
  rw [hstep]
  cases hb : Nat.blt 0 (OutS.reduce (S >>> 5) (S &&& 31) (rowOf M r))
  · refine good_zero h (Nat.eq_zero_of_not_pos fun hp => ?_)
    have := Nat.blt_eq.mpr hp
    rw [hb] at this
    exact Bool.false_ne_true this
  · have hk : (S &&& 31) + 1 < 32 := by
      have := h.hle
      omega
    show Good M (r + 1) ((((S &&& 31) + 1) ||| (_ <<< 5)) &&& 31)
      ((((S &&& 31) + 1) ||| (_ <<< 5)) >>> 5)
    rw [pack_and hk, pack_shr hk]
    exact good_pos h (Nat.blt_eq.mp hb)

private noncomputable def st (M r : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun r S => OutS.rankStep M r S) r

private theorem good_st (M : ℕ) : ∀ r ≤ 24, Good M r (st M r &&& 31) (st M r >>> 5)
  | 0, _ => by
    rw [show st M 0 = 0 from rfl, Nat.zero_and, Nat.zero_shiftRight]
    exact ⟨le_rfl, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun _ j _ hj => absurd hj (Nat.not_lt_zero j),
      bspan_congr fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | r + 1, hr => by
    rw [show st M (r + 1) = OutS.rankStep M r (st M r) from rfl]
    exact good_step (by omega) (good_st M r (by omega))

private theorem conj_iff {n : ℕ} {S P Q : Matrix (Fin n) (Fin n) (ZMod 2)} (hQP : Q * P = 1)
    (r : ℕ) :
    (Q * S * P * (Q * S * P) = 1 ∧ (Q * S * P + 1).rank = r) ↔
      (S * S = 1 ∧ (S + 1).rank = r) := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have e1 : Q * S * P * (Q * S * P) = Q * (S * S) * P := by
    calc Q * S * P * (Q * S * P) = Q * S * (P * Q) * S * P := by simp only [Matrix.mul_assoc]
      _ = Q * (S * S) * P := by rw [hPQ, Matrix.mul_one, Matrix.mul_assoc Q S S]
  have e2 : Q * S * P + 1 = Q * (S + 1) * P := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP]
  have hsq : Q * (S * S) * P = 1 ↔ S * S = 1 := by
    constructor
    · intro h1
      calc S * S = P * Q * (S * S) * (P * Q) := by rw [hPQ, Matrix.one_mul, Matrix.mul_one]
        _ = P * (Q * (S * S) * P) * Q := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.mul_one, hPQ]
    · intro h1
      rw [h1, Matrix.mul_one, hQP]
  have hrank : (Q * (S + 1) * P).rank = (S + 1).rank := by
    apply le_antisymm
    · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · calc (S + 1).rank = (P * (Q * (S + 1) * P) * Q).rank := by
            congr 1
            calc S + 1 = P * Q * (S + 1) * (P * Q) := by
                  rw [hPQ, Matrix.one_mul, Matrix.mul_one]
              _ = P * (Q * (S + 1) * P) * Q := by simp only [Matrix.mul_assoc]
        _ ≤ (P * (Q * (S + 1) * P)).rank := Matrix.rank_mul_le_left _ _
        _ ≤ (Q * (S + 1) * P).rank := Matrix.rank_mul_le_right _ _
  rw [e1, e2, hsq, hrank]

theorem rank24_eq (A : ℕ) : OutS.rank24 A = Matrix.rank (toMat A) := by
  have hg := good_st A 24 le_rfl
  have e : OutS.rank24 A = st A 24 &&& 31 := rfl
  rw [e, Matrix.rank_eq_finrank_span_row (toMat A), ← bspan_rows, ← hg.hspan,
    finrank_bspan hg.hne hg.htri]

theorem invRank_iff {r σ : ℕ} (hσ : σ < 2 ^ 576) :
    OutS.invRank r σ = true ↔ toMat σ * toMat σ = 1 ∧ Matrix.rank (toMat σ + 1) = r := by
  have h1 : mul24 σ σ = ident24 ↔ toMat σ * toMat σ = 1 := by
    constructor
    · intro h
      rw [← toMat_mul24, h, toMat_ident24]
    · intro h
      exact eq_of_toMat_eq (mul24_lt σ σ) ident24_lt (by rw [toMat_mul24, h, toMat_ident24])
  have h2 : OutS.rank24 (σ ^^^ ident24) = Matrix.rank (toMat σ + 1) := by
    rw [rank24_eq, toMat_xor, toMat_ident24]
  show andB (Nat.beq (mul24 σ σ) ident24) (Nat.beq (OutS.rank24 (σ ^^^ ident24)) r) = true ↔ _
  rw [andB_iff, Nat.beq_eq, Nat.beq_eq, h1, h2]

theorem invRank_conj {r σ τ : ℕ} (hσ : σ < 2 ^ 576) (hτ : τ < 2 ^ 576)
    {P Q : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hQP : Q * P = 1)
    (h : toMat τ = Q * toMat σ * P) : OutS.invRank r τ = OutS.invRank r σ := by
  refine Bool.eq_iff_iff.2 ((invRank_iff hτ).trans (Iff.trans ?_ (invRank_iff hσ).symm))
  rw [h]
  exact conj_iff hQP r

end CFSG.KC.Th.Spec.Rank24

end
