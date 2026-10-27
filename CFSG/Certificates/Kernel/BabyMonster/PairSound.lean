module

public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.Certificates.Kernel.BabyMonster.VStripSound

public section

namespace CFSG.KC.BM

inductive AllStrips2 (Ws Ds : List (List Nat)) : List Nat → List Nat → Prop
  | nil : AllStrips2 Ws Ds [] []
  | cons (a c : Nat) (as cs : List Nat) :
      Nat.beq (mulW Ws a) (mulW Ds c) = true → AllStrips2 Ws Ds as cs →
        AllStrips2 Ws Ds (a :: as) (c :: cs)

theorem stripMat_mul_eq_of_allStrips2 {Ws Ds : List (List Nat)} {A C : List Nat}
    (hW : ∀ W ∈ Ws, wfMat W = true) (hD : ∀ D ∈ Ds, wfMat D = true) (hA : wfMat A = true)
    (hC : wfMat C = true) (h : AllStrips2 Ws Ds A C) :
    (Ws.map stripMat).foldl (· * ·) (stripMat A) =
      (Ds.map stripMat).foldl (· * ·) (stripMat C) := by
  have hmap : ∀ {A C : List Nat}, AllStrips2 Ws Ds A C →
      A.map (mulWn 4370 Ws) = C.map (mulWn 4370 Ds) := by
    intro A C h
    induction h with
    | nil => rfl
    | cons a c as cs hb _ ih =>
      rw [List.map_cons, List.map_cons, ih]
      exact congrArg (· :: _) (Nat.eq_of_beq_eq_true hb)
  simp only [CFSG.KC.BM.SL.wfMat_eq] at hW hD hA hC
  exact (CFSG.KC.BM.SL.stripMatG_foldl (by norm_num) hW (CFSG.KC.BM.SL.wf_bit hA).1).trans
    ((congrArg (CFSG.KC.BM.SL.stripMatG 4370) (hmap h)).trans
      (CFSG.KC.BM.SL.stripMatG_foldl (by norm_num) hD (CFSG.KC.BM.SL.wf_bit hC).1).symm)

inductive WChain : List (List Nat) → List Nat → List Nat → Prop
  | nil (A : List Nat) : WChain [] A A
  | step (Ws Fs : List (List Nat)) (A B C : List Nat) :
      AllStrips Ws A B → wfMat B = true → WChain Fs B C → WChain (Ws ++ Fs) A C

theorem foldl_mul_append {M : Type*} [Monoid M] (xs ys : List M) (a : M) :
    (xs ++ ys).foldl (· * ·) a = ys.foldl (· * ·) (xs.foldl (· * ·) a) :=
  List.foldl_append

theorem stripMat_wchain {Fs : List (List Nat)} {A C : List Nat} (h : WChain Fs A C) :
    (∀ W ∈ Fs, wfMat W = true) → wfMat A = true →
      (Fs.map stripMat).foldl (· * ·) (stripMat A) = stripMat C := by
  induction h with
  | nil A => exact fun _ _ => rfl
  | step Ws Fs A B C hs hB _ ih =>
    intro hF hA
    rw [List.map_append, foldl_mul_append,
      stripMat_mul_of_allStrips (fun W hW => hF W (List.mem_append_left _ hW)) hA hs]
    exact ih (fun W hW => hF W (List.mem_append_right _ hW)) hB

@[expose] noncomputable def orbOK (V : Nat) (A : List Nat) (m m₁ : Nat) : Bool :=
  andB (andB (onlyRows V m) (Nat.beq (rowsBlk V (nat_lit 0) (nat_lit 1)) (nat_lit 1)))
    (andB (Nat.beq (rowsBlk V (nat_lit 1) m₁) (rowsBlk (mulS A V) (nat_lit 0) m₁))
      (allDistinct (rowList [V] m)))

open scoped Matrix
open CFSG.KC.BM.SL

theorem testBit_lowM {m : Nat} (hm : m ≤ 64) (j t : Nat) (ht : t < 64) :
    (lowM m).testBit (64 * j + t) = (decide (t < m) && decide (j < 4370)) := by
  have hc : 2 ^ m - 1 < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos m) (by norm_num))
      (Nat.pow_le_pow_right (by norm_num) hm)
  unfold lowM
  rw [nmul, nsub, nshl, Nat.one_shiftLeft, Nat.mul_comm SM,
    testBit_mul_sparse hc j SM (by rw [SM_eq]; exact SMn_sparse 4370) t ht,
    Nat.testBit_two_pow_sub_one, SM_eq, testBit_SMn_mul]

theorem testBit_rowsBlk (X lo : Nat) {m : Nat} (hm : m ≤ 64) (j t : Nat) (ht : t < 64) :
    (rowsBlk X lo m).testBit (64 * j + t) =
      (X.testBit (64 * j + t + lo) && (decide (t < m) && decide (j < 4370))) := by
  unfold rowsBlk
  rw [nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, testBit_lowM hm j t ht,
    Nat.add_comm lo]

theorem testBit_rowOf (X t p : Nat) :
    (rowOf X t).testBit p =
      (X.testBit (t + p) && (decide (p < 64 * 4370) && decide (p % 64 = 0))) := by
  unfold rowOf
  rw [nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, SM_eq, testBit_SMn]

theorem rowOf_inj {X Y t s : Nat} (h : vrow (rowOf X t) = vrow (rowOf Y s)) :
    rowOf X t = rowOf Y s := by
  apply Nat.eq_of_testBit_eq
  intro p
  rw [testBit_rowOf, testBit_rowOf]
  by_cases hp : p < 64 * 4370 ∧ p % 64 = 0
  · have hj : p / 64 < 4370 := by omega
    have hc := congrFun h ⟨p / 64, hj⟩
    rw [vrow_rowOf, vrow_rowOf] at hc
    have hc' : X.testBit (64 * (p / 64) + t) = Y.testBit (64 * (p / 64) + s) := bz_inj hc
    have e1 : 64 * (p / 64) + t = t + p := by omega
    have e2 : 64 * (p / 64) + s = s + p := by omega
    rw [e1, e2] at hc'
    rw [hc']
  · have : (decide (p < 64 * 4370) && decide (p % 64 = 0)) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hp hc
    rw [this, Bool.and_false, Bool.and_false]

theorem allDistinct_nodup : ∀ L : List Nat, allDistinct L = true → L.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    change andB (allDistinct xs) (List.rec (motive := fun _ => Bool) true
      (fun y _ ih2 => andB ih2 (notB (Nat.beq x y))) xs) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨?_, allDistinct_nodup xs h.1⟩
    have key : ∀ ys : List Nat, List.rec (motive := fun _ => Bool) true
        (fun y _ ih2 => andB ih2 (notB (Nat.beq x y))) ys = true → x ∉ ys := by
      intro ys
      induction ys with
      | nil => intro _; simp
      | cons y ys ih =>
        intro hy
        change andB (List.rec (motive := fun _ => Bool) true
          (fun y _ ih2 => andB ih2 (notB (Nat.beq x y))) ys) (notB (Nat.beq x y)) = true at hy
        rw [andB_eq, Bool.and_eq_true] at hy
        rw [List.mem_cons, not_or]
        refine ⟨?_, ih hy.1⟩
        intro e
        subst e
        rw [Nat.beq_refl] at hy
        exact absurd hy.2 (by decide)
    exact key xs h.2

theorem rowRec_eq (X m : Nat) : ∀ n acc, n ≤ m →
    (Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun t ih2 acc => ih2 (List.cons (rowOf X (Nat.sub (Nat.sub m t) (nat_lit 1))) acc))
      n acc) = (List.range' (m - n) n).reverse.map (rowOf X) ++ acc
  | 0, acc, _ => by
    change acc = _
    simp
  | n + 1, acc, h => by
    change (Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun t ih2 acc => ih2 (List.cons (rowOf X (Nat.sub (Nat.sub m t) (nat_lit 1))) acc)) n
      (rowOf X (m - n - 1) :: acc)) = _
    rw [rowRec_eq X m n _ (by omega)]
    have e : m - (n + 1) = m - n - 1 := by omega
    have e3 : m - n - 1 + 1 = m - n := by omega
    rw [e, List.range'_succ, e3, List.reverse_cons, List.map_append, List.append_assoc]
    rfl

theorem rowList_eq (X m : Nat) : rowList [X] m = (List.range' 0 m).reverse.map (rowOf X) := by
  have h := rowRec_eq X m m [] le_rfl
  rw [Nat.sub_self, List.append_nil] at h
  exact h

theorem orbOK_sound {V : Nat} {A : List Nat} {m m₁ : Nat} (hm : m = m₁ + 1) (hm64 : m ≤ 64)
    (hA : wfMat A = true) (h : orbOK V A m m₁ = true) :
    ∀ t, 0 < t → t < m → stripMat A ^ t ≠ 1 := by
  unfold orbOK at h
  rw [andB_eq, andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨_, h0⟩, h1, hd⟩ := h
  have h0' := Nat.eq_of_beq_eq_true h0
  have h1' := Nat.eq_of_beq_eq_true h1
  have hm1 : m₁ ≤ 64 := by omega
  have hv0 : vrow (rowOf V 0) = e0 := by
    funext j
    rw [vrow_rowOf]
    have this : (rowsBlk V 0 1).testBit (64 * j.val + 0) = (1 : Nat).testBit (64 * j.val + 0) :=
      congrArg (fun x => Nat.testBit x (64 * j.val + 0)) h0'
    rw [testBit_rowsBlk V 0 (by norm_num) j.val 0 (by norm_num), testBit_one'] at this
    simp only [Nat.add_zero, decide_eq_true (by norm_num : 0 < 1), decide_eq_true j.isLt,
      Bool.and_true] at this
    rw [Nat.add_zero, this]
    unfold e0
    rw [Pi.single_apply, bz_decide]
    by_cases hj : j = 0
    · subst hj
      simp
    · have hj' : ¬ 64 * j.val = 0 := by
        intro e
        have hj0 : j.val = 0 := by omega
        exact hj (Fin.ext hj0)
      rw [ite_eq_right hj', ite_eq_right hj]
  have hstep : ∀ t, t < m₁ → vrow (rowOf V (t + 1)) = vrow (rowOf V t) ᵥ* stripMat A := by
    intro t ht
    rw [← mulS_rows hA V (t := t) (by omega)]
    funext j
    rw [vrow_rowOf, vrow_rowOf]
    have this : (rowsBlk V 1 m₁).testBit (64 * j.val + t) =
        (rowsBlk (mulS A V) 0 m₁).testBit (64 * j.val + t) :=
      congrArg (fun x => Nat.testBit x (64 * j.val + t)) h1'
    rw [testBit_rowsBlk V 1 hm1 j.val t (by omega), testBit_rowsBlk _ 0 hm1 j.val t (by omega)]
      at this
    simp only [decide_eq_true ht, decide_eq_true j.isLt, Bool.and_true, Nat.add_zero] at this
    rw [← Nat.add_assoc, this]
  have hpow : ∀ t, t ≤ m₁ → vrow (rowOf V t) = e0 ᵥ* stripMat A ^ t := by
    intro t
    induction t with
    | zero => intro _; rw [pow_zero, Matrix.vecMul_one, hv0]
    | succ t ih =>
      intro ht
      rw [hstep t (by omega), ih (by omega), Matrix.vecMul_vecMul, pow_succ]
  intro t ht0 htm hone
  have e : vrow (rowOf V t) = vrow (rowOf V 0) := by
    rw [hpow t (by omega), hone, Matrix.vecMul_one, hv0]
  have e' := rowOf_inj e
  have hnd := allDistinct_nodup _ hd
  rw [rowList_eq] at hnd
  have := List.inj_on_of_nodup_map hnd (x := t) (y := 0)
    (by rw [List.mem_reverse, List.mem_range'_1]; omega)
    (by rw [List.mem_reverse, List.mem_range'_1]; omega) e'
  omega

theorem notId_sound {A : List Nat} (hA : wfMat A = true) (h : notB (isId A) = true) :
    stripMat A ≠ 1 := by
  intro e
  rw [CFSG.KC.BM.SL.wfMat_eq] at hA
  have hid := CFSG.KC.BM.SL.stripMatG_id (n := 4370) (by norm_num) rfl
  rw [CFSG.KC.BM.SL.stripMat_eq, ← hid] at e
  have hA' := CFSG.KC.BM.SL.stripMatG_inj (CFSG.KC.BM.SL.stripShape_of_wf hA)
    (CFSG.KC.BM.SL.stripShape_id 4370) e
  rw [hA', CFSG.KC.BM.SL.isId_id] at h
  exact absurd h (by decide)

end CFSG.KC.BM

end
