module

public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.Certificates.Kernel.Common.Loop
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

namespace CFSG.HardMathSupport.Lang.E6Descent.DiagWeylK

open CFSG.RankThree.Lattice CFSG.KC.Loop

@[expose] def tc (M : List (List ℤ)) (k i : ℕ) : ℕ := (lget M k i % 3).toNat

@[expose] def rowCode (M : List (List ℤ)) (k : ℕ) : ℕ :=
  tc M k 0 + tc M k 1 * 256 + tc M k 2 * 256 ^ 2 + tc M k 3 * 256 ^ 3 + tc M k 4 * 256 ^ 4 +
    tc M k 5 * 256 ^ 5 + 2 * 256 ^ k

@[expose] noncomputable def strictBK (y : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def lane3 (S : ℕ) : Bool := Nat.beq (Nat.mod (Nat.land S 255) 3) 0

@[expose] noncomputable def lanes3 (S : ℕ) : Bool :=
  strictBK S fun S0 => bAnd(lane3 S0,
  strictBK (Nat.shiftRight S0 8) fun S1 => bAnd(lane3 S1,
  strictBK (Nat.shiftRight S1 8) fun S2 => bAnd(lane3 S2,
  strictBK (Nat.shiftRight S2 8) fun S3 => bAnd(lane3 S3,
  strictBK (Nat.shiftRight S3 8) fun S4 => bAnd(lane3 S4,
  strictBK (Nat.shiftRight S4 8) fun S5 => lane3 S5)))))

@[expose] noncomputable def okP (r0 r1 r2 r3 r4 r5 n : ℕ) : Bool :=
  lanes3 (Nat.add (Nat.mul (Nat.mod n 3) r0) (Nat.add (Nat.mul (Nat.mod (Nat.div n 3) 3) r1)
    (Nat.add (Nat.mul (Nat.mod (Nat.div n 9) 3) r2) (Nat.add (Nat.mul (Nat.mod (Nat.div n 27) 3) r3)
    (Nat.add (Nat.mul (Nat.mod (Nat.div n 81) 3) r4) (Nat.mul (Nat.mod (Nat.div n 243) 3) r5))))))

@[expose] noncomputable def cntP (r0 r1 r2 r3 r4 r5 N : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun n ih => strictN ih fun c => nIf(okP r0 r1 r2 r3 r4 r5 n, Nat.succ c, c)) N

@[expose] noncomputable def fixCnt (M : List (List ℤ)) : ℕ :=
  strictN (rowCode M 0) fun r0 => strictN (rowCode M 1) fun r1 => strictN (rowCode M 2) fun r2 =>
    strictN (rowCode M 3) fun r3 => strictN (rowCode M 4) fun r4 => strictN (rowCode M 5) fun r5 =>
      cntP r0 r1 r2 r3 r4 r5 729

@[expose] noncomputable def chkB (b3 b1 : Bool) (c : ℕ) : Bool :=
  bIf(b3, strictBK c fun c => bAnd(Nat.ble 27 c, bIf(b1, Nat.ble 81 c, true)), true)

@[expose] noncomputable def chk (M : List (List ℤ)) : Bool :=
  chkB (decide (∀ i j : Fin 6, lget (lmul 6 M (lmul 6 M M)) i j = lget (lid 6) i j))
    (decide (∀ i j : Fin 6, lget M i j = lget (lid 6) i j)) (fixCnt M)

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(f a, ih)) L

theorem strictN_eqK (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem strictBK_eq (y : ℕ) (k : ℕ → Bool) : strictBK y k = k y := by
  cases y <;> rfl

theorem bAnd_eqK (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_trueK (x y : Bool) : Bool.rec (motive := fun _ => Bool) y x true = x := rfl

theorem bAnd_iffK (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem allL_spec {α : Type} (f : α → Bool) (L : List α) (h : allL f L = true) :
    ∀ a ∈ L, f a = true := by
  induction L with
  | nil => simp
  | cons b L ih =>
    have h' : (f b && allL f L) = true := by
      rw [← bAnd_eqK]
      exact h
    rw [Bool.and_eq_true] at h'
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact h'.1
    · exact ih h'.2 a ha

theorem cntP_eq (r0 r1 r2 r3 r4 r5 N : ℕ) :
    cntP r0 r1 r2 r3 r4 r5 N = ((List.range N).filter (okP r0 r1 r2 r3 r4 r5)).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have e : cntP r0 r1 r2 r3 r4 r5 (N + 1) =
        strictN (cntP r0 r1 r2 r3 r4 r5 N) fun c => nIf(okP r0 r1 r2 r3 r4 r5 N, Nat.succ c, c) :=
      rfl
    rw [e, strictN_eqK, ih, List.range_succ, List.filter_append, List.length_append]
    cases hb : okP r0 r1 r2 r3 r4 r5 N <;> simp [hb]

theorem land255 (x : ℕ) : Nat.land x 255 = x % 256 := by
  have h : (255 : ℕ) = 2 ^ 8 - 1 := by norm_num
  have h2 : (256 : ℕ) = 2 ^ 8 := by norm_num
  rw [h, h2]
  exact Nat.and_two_pow_sub_one_eq_mod x 8

theorem lane3_iff (s t : ℕ) (hs : s < 256) : lane3 (s + 256 * t) = true ↔ s % 3 = 0 := by
  unfold lane3
  rw [Nat.beq_eq, land255]
  have e : (s + 256 * t) % 256 = s := by omega
  rw [e]
  exact Iff.rfl

theorem lane3_iff' (s : ℕ) (hs : s < 256) : lane3 s = true ↔ s % 3 = 0 := by
  have := lane3_iff s 0 hs
  rwa [Nat.mul_zero, Nat.add_zero] at this

theorem shr8 (s t : ℕ) (hs : s < 256) : Nat.shiftRight (s + 256 * t) 8 = t := by
  have e := Nat.shiftRight_eq_div_pow (s + 256 * t) 8
  have p : (2 : ℕ) ^ 8 = 256 := by norm_num
  rw [p] at e
  have e2 : (s + 256 * t) / 256 = t := by omega
  exact e.trans e2

theorem lanes_iff (s0 s1 s2 s3 s4 s5 : ℕ) (h0 : s0 < 256) (h1 : s1 < 256) (h2 : s2 < 256)
    (h3 : s3 < 256) (h4 : s4 < 256) (h5 : s5 < 256) :
    lanes3 (s0 + 256 * (s1 + 256 * (s2 + 256 * (s3 + 256 * (s4 + 256 * s5))))) = true ↔
      s0 % 3 = 0 ∧ s1 % 3 = 0 ∧ s2 % 3 = 0 ∧ s3 % 3 = 0 ∧ s4 % 3 = 0 ∧ s5 % 3 = 0 := by
  unfold lanes3
  simp only [strictBK_eq, bAnd_iffK, shr8 _ _ h0, shr8 _ _ h1, shr8 _ _ h2, shr8 _ _ h3,
    shr8 _ _ h4, lane3_iff _ _ h0, lane3_iff _ _ h1, lane3_iff _ _ h2, lane3_iff _ _ h3,
    lane3_iff _ _ h4, lane3_iff' _ h5]

theorem tc_le (M : List (List ℤ)) (k i : ℕ) : tc M k i ≤ 2 := by
  unfold tc
  omega

theorem laneB (t0 t1 t2 t3 t4 t5 d0 d1 d2 d3 d4 d5 e : ℕ) (ht0 : t0 ≤ 2) (ht1 : t1 ≤ 2)
    (ht2 : t2 ≤ 2) (ht3 : t3 ≤ 2) (ht4 : t4 ≤ 2) (ht5 : t5 ≤ 2) (hd0 : d0 < 3) (hd1 : d1 < 3)
    (hd2 : d2 < 3) (hd3 : d3 < 3) (hd4 : d4 < 3) (hd5 : d5 < 3) (he : e < 3) :
    t0 * d0 + t1 * d1 + t2 * d2 + t3 * d3 + t4 * d4 + t5 * d5 + 2 * e < 256 := by
  have p0 := Nat.mul_le_mul ht0 (Nat.le_of_lt_succ hd0)
  have p1 := Nat.mul_le_mul ht1 (Nat.le_of_lt_succ hd1)
  have p2 := Nat.mul_le_mul ht2 (Nat.le_of_lt_succ hd2)
  have p3 := Nat.mul_le_mul ht3 (Nat.le_of_lt_succ hd3)
  have p4 := Nat.mul_le_mul ht4 (Nat.le_of_lt_succ hd4)
  have p5 := Nat.mul_le_mul ht5 (Nat.le_of_lt_succ hd5)
  omega

theorem laneM (M : List (List ℤ)) (i d0 d1 d2 d3 d4 d5 e : ℕ) (hd0 : d0 < 3) (hd1 : d1 < 3)
    (hd2 : d2 < 3) (hd3 : d3 < 3) (hd4 : d4 < 3) (hd5 : d5 < 3) (he : e < 3) :
    tc M 0 i * d0 + tc M 1 i * d1 + tc M 2 i * d2 + tc M 3 i * d3 + tc M 4 i * d4 +
      tc M 5 i * d5 + 2 * e < 256 :=
  laneB _ _ _ _ _ _ _ _ _ _ _ _ _ (tc_le M 0 i) (tc_le M 1 i) (tc_le M 2 i) (tc_le M 3 i)
    (tc_le M 4 i) (tc_le M 5 i) hd0 hd1 hd2 hd3 hd4 hd5 he

theorem coordB (a0 a1 a2 a3 a4 a5 : ℤ) (d0 d1 d2 d3 d4 d5 e : ℕ) (he : e < 3) :
    (a0 * d0 + (a1 * d1 + (a2 * d2 + (a3 * d3 + (a4 * d4 + (a5 * d5 + 0)))))) % 3 = (e : ℤ) ↔
      ((a0 % 3).toNat * d0 + (a1 % 3).toNat * d1 + (a2 % 3).toNat * d2 + (a3 % 3).toNat * d3 +
        (a4 % 3).toNat * d4 + (a5 % 3).toNat * d5 + 2 * e) % 3 = 0 := by
  have hm : ∀ a : ℤ, (((a % 3).toNat : ℕ) : ℤ) = a % 3 :=
    fun a => Int.toNat_of_nonneg (Int.emod_nonneg a (by norm_num))
  have h0 := Int.emod_add_mul_ediv a0 3
  have h1 := Int.emod_add_mul_ediv a1 3
  have h2 := Int.emod_add_mul_ediv a2 3
  have h3 := Int.emod_add_mul_ediv a3 3
  have h4 := Int.emod_add_mul_ediv a4 3
  have h5 := Int.emod_add_mul_ediv a5 3
  have hN : ((((a0 % 3).toNat * d0 + (a1 % 3).toNat * d1 + (a2 % 3).toNat * d2 +
      (a3 % 3).toNat * d3 + (a4 % 3).toNat * d4 + (a5 % 3).toNat * d5 + 2 * e : ℕ)) : ℤ) =
      a0 % 3 * d0 + a1 % 3 * d1 + a2 % 3 * d2 + a3 % 3 * d3 + a4 % 3 * d4 + a5 % 3 * d5 +
        2 * e := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hm]
  have hP : a0 * d0 + (a1 * d1 + (a2 * d2 + (a3 * d3 + (a4 * d4 + (a5 * d5 + 0))))) =
      a0 % 3 * d0 + a1 % 3 * d1 + a2 % 3 * d2 + a3 % 3 * d3 + a4 % 3 * d4 + a5 % 3 * d5 +
        3 * (a0 / 3 * d0 + a1 / 3 * d1 + a2 / 3 * d2 + a3 / 3 * d3 + a4 / 3 * d4 +
          a5 / 3 * d5) := by
    linear_combination (-(d0 : ℤ)) * h0 + (-(d1 : ℤ)) * h1 + (-(d2 : ℤ)) * h2 +
      (-(d3 : ℤ)) * h3 + (-(d4 : ℤ)) * h4 + (-(d5 : ℤ)) * h5
  rw [hP]
  generalize (a0 % 3).toNat * d0 + (a1 % 3).toNat * d1 + (a2 % 3).toNat * d2 +
    (a3 % 3).toNat * d3 + (a4 % 3).toNat * d4 + (a5 % 3).toNat * d5 + 2 * e = N at hN ⊢
  generalize a0 % 3 * (d0 : ℤ) + a1 % 3 * d1 + a2 % 3 * d2 + a3 % 3 * d3 + a4 % 3 * d4 +
    a5 % 3 * d5 = Q at hN ⊢
  generalize a0 / 3 * (d0 : ℤ) + a1 / 3 * d1 + a2 / 3 * d2 + a3 / 3 * d3 + a4 / 3 * d4 +
    a5 / 3 * d5 = R
  omega

theorem lmulVecT_six (M : List (List ℤ)) (v0 v1 v2 v3 v4 v5 : ℤ) :
    lmulVecT 6 M [v0, v1, v2, v3, v4, v5] =
      [lget M 0 0 * v0 + (lget M 1 0 * v1 + (lget M 2 0 * v2 + (lget M 3 0 * v3 +
          (lget M 4 0 * v4 + (lget M 5 0 * v5 + 0))))),
        lget M 0 1 * v0 + (lget M 1 1 * v1 + (lget M 2 1 * v2 + (lget M 3 1 * v3 +
          (lget M 4 1 * v4 + (lget M 5 1 * v5 + 0))))),
        lget M 0 2 * v0 + (lget M 1 2 * v1 + (lget M 2 2 * v2 + (lget M 3 2 * v3 +
          (lget M 4 2 * v4 + (lget M 5 2 * v5 + 0))))),
        lget M 0 3 * v0 + (lget M 1 3 * v1 + (lget M 2 3 * v2 + (lget M 3 3 * v3 +
          (lget M 4 3 * v4 + (lget M 5 3 * v5 + 0))))),
        lget M 0 4 * v0 + (lget M 1 4 * v1 + (lget M 2 4 * v2 + (lget M 3 4 * v3 +
          (lget M 4 4 * v4 + (lget M 5 4 * v5 + 0))))),
        lget M 0 5 * v0 + (lget M 1 5 * v1 + (lget M 2 5 * v2 + (lget M 3 5 * v3 +
          (lget M 4 5 * v4 + (lget M 5 5 * v5 + 0)))))] := by
  rfl

theorem keyD (M : List (List ℤ)) (d0 d1 d2 d3 d4 d5 : ℕ) (h0 : d0 < 3) (h1 : d1 < 3)
    (h2 : d2 < 3) (h3 : d3 < 3) (h4 : d4 < 3) (h5 : d5 < 3) :
    decide ((lmulVecT 6 M [(d0 : ℤ), d1, d2, d3, d4, d5]).map (fun x => x % 3) =
        [(d0 : ℤ), d1, d2, d3, d4, d5]) =
      lanes3 (Nat.add (Nat.mul d0 (rowCode M 0)) (Nat.add (Nat.mul d1 (rowCode M 1))
        (Nat.add (Nat.mul d2 (rowCode M 2)) (Nat.add (Nat.mul d3 (rowCode M 3))
        (Nat.add (Nat.mul d4 (rowCode M 4)) (Nat.mul d5 (rowCode M 5))))))) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  have hS : Nat.add (Nat.mul d0 (rowCode M 0)) (Nat.add (Nat.mul d1 (rowCode M 1))
        (Nat.add (Nat.mul d2 (rowCode M 2)) (Nat.add (Nat.mul d3 (rowCode M 3))
        (Nat.add (Nat.mul d4 (rowCode M 4)) (Nat.mul d5 (rowCode M 5)))))) =
      (tc M 0 0 * d0 + tc M 1 0 * d1 + tc M 2 0 * d2 + tc M 3 0 * d3 + tc M 4 0 * d4 +
          tc M 5 0 * d5 + 2 * d0) + 256 *
        ((tc M 0 1 * d0 + tc M 1 1 * d1 + tc M 2 1 * d2 + tc M 3 1 * d3 + tc M 4 1 * d4 +
          tc M 5 1 * d5 + 2 * d1) + 256 *
        ((tc M 0 2 * d0 + tc M 1 2 * d1 + tc M 2 2 * d2 + tc M 3 2 * d3 + tc M 4 2 * d4 +
          tc M 5 2 * d5 + 2 * d2) + 256 *
        ((tc M 0 3 * d0 + tc M 1 3 * d1 + tc M 2 3 * d2 + tc M 3 3 * d3 + tc M 4 3 * d4 +
          tc M 5 3 * d5 + 2 * d3) + 256 *
        ((tc M 0 4 * d0 + tc M 1 4 * d1 + tc M 2 4 * d2 + tc M 3 4 * d3 + tc M 4 4 * d4 +
          tc M 5 4 * d5 + 2 * d4) + 256 *
        (tc M 0 5 * d0 + tc M 1 5 * d1 + tc M 2 5 * d2 + tc M 3 5 * d3 + tc M 4 5 * d4 +
          tc M 5 5 * d5 + 2 * d5))))) := by
    simp only [rowCode, Nat.add_eq, Nat.mul_eq]
    ring
  rw [hS, lanes_iff _ _ _ _ _ _ (laneM M 0 d0 d1 d2 d3 d4 d5 d0 h0 h1 h2 h3 h4 h5 h0)
    (laneM M 1 d0 d1 d2 d3 d4 d5 d1 h0 h1 h2 h3 h4 h5 h1)
    (laneM M 2 d0 d1 d2 d3 d4 d5 d2 h0 h1 h2 h3 h4 h5 h2)
    (laneM M 3 d0 d1 d2 d3 d4 d5 d3 h0 h1 h2 h3 h4 h5 h3)
    (laneM M 4 d0 d1 d2 d3 d4 d5 d4 h0 h1 h2 h3 h4 h5 h4)
    (laneM M 5 d0 d1 d2 d3 d4 d5 d5 h0 h1 h2 h3 h4 h5 h5), lmulVecT_six]
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  exact and_congr (coordB _ _ _ _ _ _ _ _ _ _ _ _ _ h0) (and_congr
    (coordB _ _ _ _ _ _ _ _ _ _ _ _ _ h1) (and_congr (coordB _ _ _ _ _ _ _ _ _ _ _ _ _ h2)
    (and_congr (coordB _ _ _ _ _ _ _ _ _ _ _ _ _ h3) (and_congr
    (coordB _ _ _ _ _ _ _ _ _ _ _ _ _ h4) (coordB _ _ _ _ _ _ _ _ _ _ _ _ _ h5)))))

theorem fixCnt_eq (M : List (List ℤ)) :
    ((((List.range 729).map fun n =>
      [(n % 3 : ℕ), (n / 3 % 3 : ℕ), (n / 9 % 3 : ℕ), (n / 27 % 3 : ℕ), (n / 81 % 3 : ℕ),
        (n / 243 % 3 : ℕ)].map (fun x : ℕ => (x : ℤ))).filter
      fun u => (lmulVecT 6 M u).map (fun x => x % 3) = u).length) = fixCnt M := by
  rw [List.filter_map, List.length_map]
  unfold fixCnt
  simp only [strictN_eqK]
  rw [cntP_eq]
  refine congrArg List.length (List.filter_congr fun n _ => ?_)
  simp only [Function.comp_apply, List.map_cons, List.map_nil]
  exact keyD M _ _ _ _ _ _ (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num))

theorem chkB_spec (b3 b1 : Bool) (c : ℕ) (h : chkB b3 b1 c = true) (h3 : b3 = true) :
    27 ≤ c ∧ (b1 = true → 81 ≤ c) := by
  subst h3
  unfold chkB at h
  rw [bIf_trueK _ true, strictBK_eq, bAnd_iffK] at h
  refine ⟨Nat.le_of_ble_eq_true h.1, fun h1 => ?_⟩
  have h2 := h.2
  subst h1
  exact Nat.le_of_ble_eq_true h2

theorem chk_spec (M : List (List ℤ)) (hc : chk M = true)
    (h3 : ∀ i j : Fin 6, lget (lmul 6 M (lmul 6 M M)) i j = lget (lid 6) i j) :
    27 ≤ fixCnt M ∧ ((∀ i j : Fin 6, lget M i j = lget (lid 6) i j) → 81 ≤ fixCnt M) := by
  have h := chkB_spec _ _ _ hc (decide_eq_true h3)
  exact ⟨h.1, fun hI => h.2 (decide_eq_true hI)⟩

end CFSG.HardMathSupport.Lang.E6Descent.DiagWeylK

end
