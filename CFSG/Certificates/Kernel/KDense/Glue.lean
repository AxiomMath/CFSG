module

public import CFSG.Certificates.Kernel.KDense.StepSound
public import CFSG.Monster.AxisCount.DenseModFive

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.Monster.AxisCount

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : notB a = !a := by cases a <;> rfl

theorem strictS_eq (y : ℕ) (k : ℕ → St) : strictS y k = k y := by cases y <;> rfl

theorem forceSt_eq (s : St) (k : St → St) : forceSt s k = k s := by
  obtain ⟨f, X, A, W⟩ := s
  change strictS X (fun X' => strictS A (fun A' => strictS W (fun W' => k (f, X', A', W')))) = _
  simp only [strictS_eq]

theorem SX_eq : SX = 131072 := rfl

theorem SA_eq : SA = 1024 := rfl

theorem ones_eq (S : ℕ) : ones S = 2 ^ S - 1 := by
  change 1 <<< S - 1 = _
  rw [Nat.one_shiftLeft]

theorem ones_lt (S : ℕ) : ones S < 2 ^ S := by
  rw [ones_eq]
  exact Nat.sub_lt (Nat.two_pow_pos S) Nat.one_pos

theorem testBit_ones {S p : ℕ} (hp : p < S) : (ones S).testBit p = true := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hp

theorem rep4_eq (S m : ℕ) : rep4 S m = (m ||| m <<< S) ||| (m ||| m <<< S) <<< (2 * S) := by
  change (m ||| m <<< S) ||| (m ||| m <<< S) <<< (S <<< 1) = _
  rw [Nat.shiftLeft_eq S 1, pow_one, mul_comm]

theorem rep4_lt {S m : ℕ} (hm : m < 2 ^ S) : rep4 S m < 2 ^ (4 * S) := by
  have h2 : m ||| m <<< S < 2 ^ (2 * S) := by
    refine Nat.or_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
    rw [Nat.shiftLeft_eq, two_mul, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos S)
  rw [rep4_eq]
  refine Nat.or_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega))) ?_
  rw [Nat.shiftLeft_eq, (by ring : 4 * S = 2 * S + 2 * S), pow_add]
  exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)

theorem testBit_rep4 {S m : ℕ} (hm : m < 2 ^ S) {p : ℕ} (hp : p < S) :
    (rep4 S m).testBit p = m.testBit p ∧ (rep4 S m).testBit (S + p) = m.testBit p ∧
      (rep4 S m).testBit (2 * S + p) = m.testBit p ∧
      (rep4 S m).testBit (3 * S + p) = m.testBit p := by
  have hz : ∀ j, S ≤ j → m.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hj))
  rw [rep4_eq]
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have l1 : ¬ S ≤ p := by omega
    have l2 : ¬ 2 * S ≤ p := by omega
    simp [l1, l2]
  · have e1 : S + p - S = p := by omega
    have l1 : ¬ 2 * S ≤ S + p := by omega
    simp [hz, e1, l1]
  · have e1 : 2 * S + p - S = S + p := by omega
    have e2 : 2 * S + p - 2 * S = p := by omega
    have l1 : S ≤ 2 * S + p := by omega
    have l2 : S ≤ S + p := by omega
    have l3 : ¬ S ≤ p := by omega
    simp [hz, e1, e2, l1, l2, l3]
  · have e1 : 3 * S + p - S = 2 * S + p := by omega
    have e2 : 3 * S + p - 2 * S = S + p := by omega
    have e3 : S + p - S = p := by omega
    have l1 : S ≤ 2 * S + p := by omega
    have l2 : S ≤ S + p := by omega
    have l3 : 2 * S ≤ 3 * S + p := by omega
    have l4 : S ≤ 3 * S + p := by omega
    simp [hz, e1, e2, e3, l1, l2, l3, l4]

@[expose] noncomputable def dig (S x p : ℕ) : ℕ :=
  x / 2 ^ p % 2 + 2 * (x / 2 ^ (S + p) % 2) + 4 * (x / 2 ^ (2 * S + p) % 2) +
    8 * (x / 2 ^ (3 * S + p) % 2)

theorem resP_eq (S x p : ℕ) : resP S x p = (dig S x p : ZMod 15) := rfl

theorem norm15_eq (S x : ℕ) : norm15 S x = x ^^^ rep4 S
    ((((x >>> (0 * S)) &&& ones S) &&& ((x >>> (1 * S)) &&& ones S)) &&&
      (((x >>> (2 * S)) &&& ones S) &&& ((x >>> (3 * S)) &&& ones S))) := rfl

theorem mask_lt (S x : ℕ) : (((x >>> (0 * S)) &&& ones S) &&& ((x >>> (1 * S)) &&& ones S)) &&&
    (((x >>> (2 * S)) &&& ones S) &&& ((x >>> (3 * S)) &&& ones S)) < 2 ^ S :=
  Nat.and_lt_two_pow _ (Nat.and_lt_two_pow _ (Nat.and_lt_two_pow _ (ones_lt S)))

theorem resP_norm15 {S x p : ℕ} (hp : p < S) : resP S (norm15 S x) p = resP S x p := by
  obtain ⟨h0, h1, h2, h3⟩ := testBit_rep4 (mask_lt S x) hp
  simp only [resP_eq, dig, ← Nat.toNat_testBit]
  rw [norm15_eq]
  simp only [Nat.testBit_xor, h0, h1, h2, h3]
  simp only [Nat.testBit_and, Nat.testBit_shiftRight,
    testBit_ones hp, Bool.and_true, zero_mul, zero_add, one_mul]
  generalize x.testBit p = a0
  generalize x.testBit (S + p) = a1
  generalize x.testBit (2 * S + p) = a2
  generalize x.testBit (3 * S + p) = a3
  cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> decide

theorem norm15_lt {S x : ℕ} (hx : x < 2 ^ (4 * S)) : norm15 S x < 2 ^ (4 * S) := by
  rw [norm15_eq]
  exact Nat.xor_lt_two_pow hx (rep4_lt (mask_lt S x))

theorem lt_of_norm15 {S x : ℕ} (hx : norm15 S x < 2 ^ (4 * S)) : x < 2 ^ (4 * S) := by
  rw [norm15_eq] at hx
  have e := Nat.xor_lt_two_pow hx (rep4_lt (mask_lt S x))
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at e

theorem resP_congr {S x y p : ℕ} (hp : p < S) (h : norm15 S x = norm15 S y) :
    resP S y p = resP S x p := by
  rw [← resP_norm15 hp, ← h, resP_norm15 hp]

theorem stEq_iff (f X A W f' X' A' W' : _) : stEq (f, X, A, W) (f', X', A', W') = true ↔
    f = true ∧ f' = true ∧ norm15 SX X = norm15 SX X' ∧ norm15 SA A = norm15 SA A' ∧
      norm15 SX W = norm15 SX W' := by
  change andB f (andB f' (andB (Nat.beq (norm15 SX X) (norm15 SX X'))
    (andB (Nat.beq (norm15 SA A) (norm15 SA A')) (Nat.beq (norm15 SX W) (norm15 SX W'))))) =
      true ↔ _
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq]

theorem stEq_flag {s t : St} (h : stEq s t = true) : s.1 = true := by
  obtain ⟨f, X, A, W⟩ := s
  obtain ⟨f', X', A', W'⟩ := t
  exact ((stEq_iff _ _ _ _ _ _ _ _).1 h).1

theorem pairTab_lt (i : ℕ) :
    (Native.pairTab ())[i]!.1 < 24 ∧ (Native.pairTab ())[i]!.2 < 24 := by
  generalize hP : Native.pairTab () = P
  by_cases h : i < P.size
  · rw [getElem!_pos P i h]
    have hm : P[i] ∈ P := Array.getElem_mem h
    generalize P[i] = x at hm
    subst hP
    simp only [Native.pairTab, List.mem_toArray, List.mem_flatMap, List.mem_map, List.mem_filter,
      List.mem_range] at hm
    obtain ⟨a, ha, b, ⟨hb, -⟩, rfl⟩ := hm
    exact ⟨ha, hb⟩
  · rw [getElem!_neg P i h]
    exact ⟨by decide, by decide⟩

theorem xposK_lt {q : ℕ} (hq : q < 98280) : xposK q < SX := by
  have := pairTab_lt (q / 2)
  rw [SX_eq]
  unfold xposK
  split_ifs <;> omega

theorem stEq_rep {v : Native.DVec} {s t : St} (h : stEq s t = true) (hs : Rep v s) : Rep v t := by
  obtain ⟨f, X, A, W⟩ := s
  obtain ⟨f', X', A', W'⟩ := t
  obtain ⟨-, -, hX, hA, hW⟩ := (stEq_iff _ _ _ _ _ _ _ _).1 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, ?_, fun i hi j hj => ?_, fun p hp hq => ?_, ?_,
    fun r hr j hj => ?_, fun p hp hq => ?_, ?_⟩
  · rw [resP_congr (xposK_lt hq) hX]
    exact h1 q hq
  · rw [resP_congr hp hX]
    exact h2 p hp hq
  · exact lt_of_norm15 (hX ▸ norm15_lt h3)
  · rw [resP_congr (by rw [SA_eq]; omega) hA]
    exact h4 i hi j hj
  · rw [resP_congr hp hA]
    exact h5 p hp hq
  · exact lt_of_norm15 (hA ▸ norm15_lt h6)
  · rw [resP_congr (by rw [SX_eq]; omega) hW]
    exact h7 r hr j hj
  · rw [resP_congr hp hW]
    exact h8 p hp hq
  · exact lt_of_norm15 (hW ▸ norm15_lt h9)

theorem res15_halve {v : Native.DVec} (he : 0 < v.e) (hD : ∀ x ∈ v.D, x % 2 = 0) (k : ℕ) :
    res15 ⟨v.e - 1, v.D.map (· / 2)⟩ k = res15 v k := by
  obtain ⟨e, D⟩ := v
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt he
  simp only [res15, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases hk : D[k]? with _ | x
  · simp
  · have hx : x % 2 = 0 := hD x (Array.mem_of_getElem? hk)
    obtain ⟨y, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero hx
    have h16 : (16 : ZMod 15) = 1 := by decide
    simp only [Option.map_some, Option.getD_some, Nat.add_sub_cancel, zero_add,
      Int.mul_ediv_cancel_left _ two_ne_zero]
    push_cast
    linear_combination (-(y : ZMod 15) * 8 ^ e) * h16

theorem res15_reduceN (n : ℕ) (v : Native.DVec) (k : ℕ) :
    res15 (Native.reduceN n v) k = res15 v k := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Native.reduceN]
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
        beq_iff_eq] at h
      rw [ih, res15_halve h.1 h.2]
    · rfl

theorem rep_reduce {v : Native.DVec} {s : St} (h : Rep v s) : Rep v.reduce s := by
  have e : res15 v.reduce = res15 v := funext (res15_reduceN v.e v)
  unfold Rep at h ⊢
  rw [e]
  exact h

theorem evalWordC_nil (c : Native.Ctx) (v : Native.DVec) : Native.evalWordC c [] v = v := rfl

theorem evalWordC_cons (c : Native.Ctx) (g : Native.Gen) (w : List Native.Gen) (v : Native.DVec) :
    Native.evalWordC c (g :: w) v = Native.evalWordC c w (Native.applyGen c g v).reduce := rfl

theorem evalWordC_append (c : Native.Ctx) (w w' : List Native.Gen) (v : Native.DVec) :
    Native.evalWordC c (w ++ w') v = Native.evalWordC c w' (Native.evalWordC c w v) :=
  List.foldl_append

theorem step_flag {F : Fix} {T : Tab} (g : Native.Gen) (s : St) (h : (step F T g s).1 = true) :
    s.1 = true := by
  obtain ⟨f, X, A, W⟩ := s
  cases g with
  | rho q =>
    obtain ⟨qs, qa, qd⟩ := q
    have e : (step F T (.rho (qs, qa, qd)) (f, X, A, W)).1 = andB f true := rfl
    rw [e, andB_eq, Bool.and_true] at h
    exact h
  | perm arr =>
    have e : (step F T (.perm arr) (f, X, A, W)).1 = andB f (findIdx (arrList arr) T.arrs).1 := rfl
    rw [e, andB_eq, Bool.and_eq_true] at h
    exact h.1
  | sign a =>
    have e : (step F T (.sign a) (f, X, A, W)).1 = false := rfl
    rw [e] at h
    exact absurd h Bool.false_ne_true
  | xi => exact h
  | tau => exact h

theorem run_cons {F : Fix} {T : Tab} (g : Native.Gen) (w : List Native.Gen) (i n : ℕ) (s : St) :
    run F T (g :: w) i n s = Bool.rec (motive := fun _ => St)
      (Bool.rec (motive := fun _ => St) (run F T w i (n - 1) (step F T g s)) s (Nat.beq n 0))
      (run F T w (i - 1) n s) (Nat.blt 0 i) := by
  rw [← forceSt_eq (step F T g s) (fun t' => run F T w i (n - 1) t')]
  rfl

theorem run_pos {F : Fix} {T : Tab} (g : Native.Gen) (w : List Native.Gen) {i : ℕ} (hi : 0 < i)
    (n : ℕ) (s : St) : run F T (g :: w) i n s = run F T w (i - 1) n s := by
  rw [run_cons, (Nat.blt_eq.mpr hi : Nat.blt 0 i = true)]

theorem run_zero_zero {F : Fix} {T : Tab} (g : Native.Gen) (w : List Native.Gen) (s : St) :
    run F T (g :: w) 0 0 s = s := rfl

theorem run_zero_succ {F : Fix} {T : Tab} (g : Native.Gen) (w : List Native.Gen) (n : ℕ) (s : St) :
    run F T (g :: w) 0 (n + 1) s = run F T w 0 n (step F T g s) := by
  rw [run_cons]
  rfl

theorem run_len_zero {F : Fix} {T : Tab} (w : List Native.Gen) (i : ℕ) (s : St) :
    run F T w i 0 s = s := by
  induction w generalizing i with
  | nil => rfl
  | cons g w ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rfl
    · rw [run_pos g w hi, ih]

theorem run_flag {F : Fix} {T : Tab} (w : List Native.Gen) (i n : ℕ) (s : St)
    (h : (run F T w i n s).1 = true) : s.1 = true := by
  induction w generalizing i n s with
  | nil => exact h
  | cons g w ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases n with _ | n
      · exact h
      · rw [run_zero_succ] at h
        exact step_flag g s (ih 0 n _ h)
    · rw [run_pos g w hi] at h
      exact ih _ _ _ h

theorem run_rep {F : Fix} {T : Tab} {KT TH OCT DU1 : Nat} (hd : dataOK F T KT TH OCT DU1 = true)
    (w : List Native.Gen) (hL : ∀ g ∈ w, letterOK g = true) (i n : ℕ) (v : Native.DVec) (s : St)
    (hs : Rep v s) (hf : (run F T w i n s).1 = true) :
    (∀ g ∈ (w.drop i).take n, g.validB = true) ∧
      Rep (Native.evalWordC (Native.mkCtx ()) ((w.drop i).take n) v) (run F T w i n s) := by
  induction w generalizing i n v s with
  | nil =>
    refine ⟨by simp, ?_⟩
    simp only [List.drop_nil, List.take_nil]
    exact hs
  | cons g w ih =>
    have hL' : ∀ g ∈ w, letterOK g = true := fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases n with _ | n
      · exact ⟨by simp, hs⟩
      · rw [run_zero_succ] at hf ⊢
        obtain ⟨hv, hr⟩ := step_sound hd g (hL g List.mem_cons_self) v s hs (run_flag w 0 n _ hf)
        obtain ⟨h1, h2⟩ := ih hL' 0 n _ _ (rep_reduce hr) hf
        simp only [List.drop_zero, List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at h1 h2 ⊢
        exact ⟨⟨hv, h1⟩, h2⟩
    · rw [run_pos g w hi] at hf ⊢
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hi
      simpa using ih hL' _ n v s hs hf

theorem aIdx_cover {k : ℕ} (hk : k < 300) : ∃ i < 24, ∃ j < 24, Native.aIdx i j = k := by
  by_cases h : k < 24
  · exact ⟨k, h, k, h, by simp [Native.aIdx]⟩
  have hc : ∀ z < 276, ∃ i < 23, i * (47 - i) / 2 ≤ z ∧ z < i * (47 - i) / 2 + (23 - i) := by
    decide +kernel
  obtain ⟨i, hi, h1, h2⟩ := hc (k - 24) (by omega)
  refine ⟨i, by omega, i + 1 + (k - 24 - i * (47 - i) / 2), by omega, ?_⟩
  have hne : i ≠ i + 1 + (k - 24 - i * (47 - i) / 2) := by omega
  simp only [Native.aIdx, hne, ↓reduceIte, Native.pairIdx]
  rw [min_eq_left (by omega), max_eq_right (by omega)]
  omega

theorem rep_unique {u v : Native.DVec} {s : St} (hu : Rep u s) (hv : Rep v s) {k : ℕ}
    (hk : k < 196884) : res15 u k = res15 v k := by
  by_cases h1 : k < 300
  · obtain ⟨i, hi, j, hj, rfl⟩ := aIdx_cover h1
    rw [← hu.2.2.2.1 i hi j hj, hv.2.2.2.1 i hi j hj]
  by_cases h2 : k < 98580
  · have e : k = 300 + (k - 300) := by omega
    rw [e, ← hu.1 _ (by omega), hv.1 _ (by omega)]
  · have e : k = 98580 + 24 * ((k - 98580) / 24) + (k - 98580) % 24 := by omega
    rw [e, ← hu.2.2.2.2.2.2.1 _ (by omega) _ (by omega), hv.2.2.2.2.2.2.1 _ (by omega) _ (by omega)]

noncomputable abbrev to5 : ZMod 15 →+* ZMod 5 := ZMod.castHom (by norm_num) (ZMod 5)

theorem res5_eq (v : Native.DVec) (k : ℕ) : DVec.res5 v k = to5 (res15 v k) := by
  simp only [res15, DVec.res5, map_mul, map_pow, map_intCast]
  rfl

theorem bitN_eq (x i : ℕ) : bitN x i = x / 2 ^ i % 2 := by
  change (x >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem resX5_eq (s : St) (p : ℕ) : resX5 s p = dig SX s.2.1 p % 15 % 5 := by
  obtain ⟨f, X, A, W⟩ := s
  change (0 + bitN X (0 * SX + p) <<< 0 + bitN X (1 * SX + p) <<< 1 + bitN X (2 * SX + p) <<< 2 +
    bitN X (3 * SX + p) <<< 3) % 15 % 5 = _
  simp only [bitN_eq, Nat.shiftLeft_eq, dig, zero_mul, one_mul, zero_add]
  congr 2
  ring

theorem resX5_cast (s : St) (p : ℕ) : (resX5 s p : ZMod 5) = to5 (resP SX s.2.1 p) := by
  rw [resX5_eq, resP_eq, map_natCast, Nat.mod_mod_of_dvd _ (by norm_num), ZMod.natCast_mod]

theorem res5_sep {u v : Native.DVec} {s t : St} (hu : Rep u s) (hv : Rep v t) {p : ℕ}
    (hne : resX5 s p ≠ resX5 t p) (hp : p < SX) :
    ∃ k < 196884, DVec.res5 u k ≠ DVec.res5 v k := by
  by_cases hq : ∃ q < 98280, xposK q = p
  · obtain ⟨q, hq, rfl⟩ := hq
    refine ⟨300 + q, by omega, fun e => hne ?_⟩
    rw [res5_eq, res5_eq, ← hu.1 q hq, ← hv.1 q hq, ← resX5_cast, ← resX5_cast,
      ZMod.natCast_eq_natCast_iff'] at e
    have h5 : ∀ r : St, resX5 r (xposK q) < 5 := fun r => by
      rw [resX5_eq]
      exact Nat.mod_lt _ (by norm_num)
    rwa [Nat.mod_eq_of_lt (h5 s), Nat.mod_eq_of_lt (h5 t)] at e
  · push Not at hq
    have z : ∀ (w : Native.DVec) (r : St), Rep w r → resX5 r p = 0 := fun w r hr => by
      have h0 := hr.2.1 p hp hq
      rw [resP_eq, ZMod.natCast_eq_zero_iff] at h0
      rw [resX5_eq, Nat.mod_eq_zero_of_dvd h0]
    exact absurd ((z u s hu).trans (z v t hv).symm) hne

theorem wlen_eq (w : List Native.Gen) : wlen w = w.length := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    change wlen w + 1 = _
    rw [ih, List.length_cons]

theorem chunk_kind0 {F : Fix} {T : Tab} {words : ℕ → List Native.Gen} {S : ℕ → St} {c : ℕ}
    (h : chunkOK F T words S c = true) (hk : f20 c 5 = 0) :
    stEq (run F T (words (f20 c 0)) (f20 c 1) (f20 c 2) (S (f20 c 3))) (S (f20 c 4)) = true := by
  have e : chunkOK F T words S c = Bool.rec (motive := fun _ => Bool)
      (stEq (run F T (words (f20 c 0)) (f20 c 1) (f20 c 2) (S (f20 c 3))) (S (f20 c 4)))
      (andB (Nat.blt (f20 c 1) SX) (andB (flagOf (S (f20 c 3))) (andB (flagOf (S (f20 c 4)))
        (notB (Nat.beq (resX5 (S (f20 c 3)) (f20 c 1)) (resX5 (S (f20 c 4)) (f20 c 1)))))))
      (Nat.beq (f20 c 5) 1) := rfl
  rw [e, hk] at h
  exact h

theorem chunk_kind1 {F : Fix} {T : Tab} {words : ℕ → List Native.Gen} {S : ℕ → St} {c : ℕ}
    (h : chunkOK F T words S c = true) (hk : f20 c 5 = 1) :
    f20 c 1 < SX ∧ resX5 (S (f20 c 3)) (f20 c 1) ≠ resX5 (S (f20 c 4)) (f20 c 1) := by
  have e : chunkOK F T words S c = Bool.rec (motive := fun _ => Bool)
      (stEq (run F T (words (f20 c 0)) (f20 c 1) (f20 c 2) (S (f20 c 3))) (S (f20 c 4)))
      (andB (Nat.blt (f20 c 1) SX) (andB (flagOf (S (f20 c 3))) (andB (flagOf (S (f20 c 4)))
        (notB (Nat.beq (resX5 (S (f20 c 3)) (f20 c 1)) (resX5 (S (f20 c 4)) (f20 c 1)))))))
      (Nat.beq (f20 c 5) 1) := rfl
  rw [e, hk] at h
  change andB _ _ = true at h
  simp only [andB_eq, notB_eq, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  exact ⟨h.1, Nat.ne_of_beq_eq_false h.2.2.2⟩

@[expose] noncomputable def sideFold (CH : ℕ → ℕ) (σ x a n : ℕ) : (Bool × ℕ) × ℕ :=
  Nat.rec (motive := fun _ => (Bool × ℕ) × ℕ) ((true, 0), x)
    (fun k ih => (fun c => ((andB ih.1.1 (andB (Nat.beq (f20 c 0) σ)
      (andB (Nat.beq (f20 c 1) ih.1.2) (andB (Nat.beq (f20 c 3) ih.2) (Nat.beq (f20 c 5) 0)))), ih.1.2 + f20 c 2), f20 c 4))
      (CH (a + k))) n

theorem sideOK_eq (CH : ℕ → ℕ) (σ len x a n : ℕ) : sideOK CH σ len x a n =
    (andB (sideFold CH σ x a n).1.1 (Nat.ble len (sideFold CH σ x a n).1.2),
      (sideFold CH σ x a n).2) := rfl

theorem sideFold_succ (CH : ℕ → ℕ) (σ x a n : ℕ) : sideFold CH σ x a (n + 1) =
    ((andB (sideFold CH σ x a n).1.1 (andB (Nat.beq (f20 (CH (a + n)) 0) σ)
      (andB (Nat.beq (f20 (CH (a + n)) 1) (sideFold CH σ x a n).1.2)
      (andB (Nat.beq (f20 (CH (a + n)) 3) (sideFold CH σ x a n).2)
        (Nat.beq (f20 (CH (a + n)) 5) 0)))),
      (sideFold CH σ x a n).1.2 + f20 (CH (a + n)) 2), f20 (CH (a + n)) 4) := rfl

theorem side_sound {F : Fix} {T : Tab} {KT TH OCT DU1 : Nat} (hd : dataOK F T KT TH OCT DU1 = true)
    {words : ℕ → List Native.Gen} {S : ℕ → St} {CH : ℕ → ℕ} {σ x a : ℕ}
    (hL : ∀ g ∈ words σ, letterOK g = true) (v : Native.DVec)
    (hx : Rep v (S x)) (n : ℕ) (hch : ∀ k < n, chunkOK F T words S (CH (a + k)) = true)
    (h : (sideFold CH σ x a n).1.1 = true) :
    (∀ g ∈ (words σ).take (sideFold CH σ x a n).1.2, g.validB = true) ∧
      Rep (Native.evalWordC (Native.mkCtx ()) ((words σ).take (sideFold CH σ x a n).1.2) v)
        (S (sideFold CH σ x a n).2) := by
  induction n with
  | zero =>
    refine ⟨fun g hg => ?_, hx⟩
    change g ∈ (words σ).take 0 at hg
    simp at hg
  | succ n ih =>
    rw [sideFold_succ] at h ⊢
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨hr, h0, h1, h3, h5⟩ := h
    obtain ⟨iv, ir⟩ := ih (fun k hk => hch k (by omega)) hr
    have hc := chunk_kind0 (hch n (by omega)) h5
    rw [h0, h1, h3] at hc
    obtain ⟨jv, jr⟩ := run_rep hd _ hL _ _ _ _ ir (stEq_flag hc)
    rw [List.take_add, evalWordC_append]
    refine ⟨fun g hg => ?_, stEq_rep hc jr⟩
    rcases List.mem_append.1 hg with hg | hg
    · exact iv g hg
    · exact jv g hg

@[expose] noncomputable def planFold (words : ℕ → List Native.Gen) (CH : ℕ → ℕ) (nch : ℕ)
    (IT : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun it _ ih t => andB (itemOK words CH nch it t) (ih (t + 1))) IT

theorem planFold_item {words : ℕ → List Native.Gen} {CH : ℕ → ℕ} {nch : ℕ} (IT : List ℕ) (t₀ : ℕ)
    (h : planFold words CH nch IT t₀ = true) (j : ℕ) (hj : j < IT.length) :
    itemOK words CH nch IT[j] (t₀ + j) = true := by
  induction IT generalizing t₀ j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons it IT ih =>
    change andB (itemOK words CH nch it t₀) (planFold words CH nch IT (t₀ + 1)) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases j with _ | j
    · exact h.1
    · rw [List.getElem_cons_succ, (by omega : t₀ + (j + 1) = t₀ + 1 + j)]
      exact ih _ h.2 j (by simpa using hj)

theorem itemOK_spec {words : ℕ → List Native.Gen} {CH : ℕ → ℕ} {nch it t : ℕ}
    (h : itemOK words CH nch it t = true) :
    ((sideFold CH (2 * t) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).1.1 = true ∧
      wlen (words (2 * t)) ≤
        (sideFold CH (2 * t) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).1.2) ∧
    ((sideFold CH (2 * t + 1) (Nat.land it 3) fld(it, 44, 1048575) fld(it, 64, 1048575)).1.1 =
        true ∧
      wlen (words (2 * t + 1)) ≤
        (sideFold CH (2 * t + 1) (Nat.land it 3) fld(it, 44, 1048575) fld(it, 64, 1048575)).1.2) ∧
    f20 (CH fld(it, 84, 1048575)) 2 = 0 ∧
    f20 (CH fld(it, 84, 1048575)) 3 =
      (sideFold CH (2 * t) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).2 ∧
    f20 (CH fld(it, 84, 1048575)) 4 =
      (sideFold CH (2 * t + 1) (Nat.land it 3) fld(it, 44, 1048575) fld(it, 64, 1048575)).2 ∧
    Nat.land it 3 < 3 ∧ f20 (CH fld(it, 84, 1048575)) 5 = bitN it 2 ∧
    fld(it, 84, 1048575) < nch ∧ fld(it, 4, 1048575) + fld(it, 24, 1048575) ≤ nch ∧
    fld(it, 44, 1048575) + fld(it, 64, 1048575) ≤ nch := by
  change andB (sideOK CH (2 * t) (wlen (words (2 * t))) (Nat.land it 3) fld(it, 4, 1048575)
      fld(it, 24, 1048575)).1
    (andB (sideOK CH (2 * t + 1) (wlen (words (2 * t + 1))) (Nat.land it 3) fld(it, 44, 1048575)
      fld(it, 64, 1048575)).1
    (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 2) 0)
    (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 3) (sideOK CH (2 * t) (wlen (words (2 * t)))
      (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).2)
    (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 4) (sideOK CH (2 * t + 1)
      (wlen (words (2 * t + 1))) (Nat.land it 3) fld(it, 44, 1048575) fld(it, 64, 1048575)).2)
    (andB (Nat.blt (Nat.land it 3) 3) (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 5) (bitN it 2))
    (andB (Nat.blt fld(it, 84, 1048575) nch)
    (andB (Nat.ble (fld(it, 4, 1048575) + fld(it, 24, 1048575)) nch)
      (Nat.ble (fld(it, 44, 1048575) + fld(it, 64, 1048575)) nch))))))))) = true at h
  simp only [sideOK_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
  exact h

theorem plan_sound {F : Fix} {T : Tab} {KT TH OCT DU1 : Nat} (hd : dataOK F T KT TH OCT DU1 = true)
    (words : ℕ → List Native.Gen) (hL : ∀ σ, ∀ g ∈ words σ, letterOK g = true) (S : ℕ → St)
    (wit : ℕ → Native.DVec)
    (hinit : ∀ x < 3, Rep (wit x) (S x)) (CH : ℕ → ℕ) (nch : ℕ) (IT : List ℕ)
    (hplan : planOK words CH nch IT = true) (hch : ∀ k < nch, chunkOK F T words S (CH k) = true)
    (t : ℕ) (ht : t < IT.length) :
    (∀ g ∈ words (2 * t), g.validB = true) ∧ (∀ g ∈ words (2 * t + 1), g.validB = true) ∧
    (IT[t]! / 4 % 2 = 0 → Cong5D (Native.evalWord (words (2 * t)) (wit (IT[t]! % 4)))
      (Native.evalWord (words (2 * t + 1)) (wit (IT[t]! % 4)))) ∧
    (IT[t]! / 4 % 2 = 1 → ∃ k < 196884,
      DVec.res5 (Native.evalWord (words (2 * t)) (wit (IT[t]! % 4))) k ≠ DVec.res5 (Native.evalWord (words (2 * t + 1)) (wit (IT[t]! % 4))) k) := by
  have hit := planFold_item IT 0 hplan t ht
  rw [zero_add, ← getElem!_pos IT t ht] at hit
  generalize IT[t]! = it at hit ⊢
  obtain ⟨⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hf2, hf3, hf4, hx, hf5, hfn, hab, hbb⟩ := itemOK_spec hit
  have hx4 : Nat.land it 3 = it % 4 := Nat.and_two_pow_sub_one_eq_mod it 2
  rw [hx4] at hA1 hA2 hB1 hB2 hf3 hf4 hx
  obtain ⟨vA, rA⟩ := side_sound hd (hL _) _ (hinit _ hx) _ (fun k hk => hch _ (by omega)) hA1
  obtain ⟨vB, rB⟩ := side_sound hd (hL _) _ (hinit _ hx) _ (fun k hk => hch _ (by omega)) hB1
  rw [wlen_eq] at hA2 hB2
  rw [List.take_of_length_le hA2] at vA rA
  rw [List.take_of_length_le hB2] at vB rB
  have hfc := hch _ hfn
  rw [bitN_eq] at hf5
  refine ⟨vA, vB, fun hb => ?_, fun hb => ?_⟩
  · have hc := chunk_kind0 hfc (by rw [hf5]; exact hb)
    rw [hf2, run_len_zero, hf3, hf4] at hc
    intro k hk
    rw [res5_eq, res5_eq]
    exact congrArg to5 (rep_unique (stEq_rep hc rA) rB hk)
  · obtain ⟨hp, hne⟩ := chunk_kind1 hfc (by rw [hf5]; exact hb)
    rw [hf3, hf4] at hne
    exact res5_sep rA rB hne hp

theorem tabOK_of_entries (F : Fix) (T : Tab)
    (h : ∀ k < T.arrs.length, entryOK F T (T.arrs.getD k []) k = true) : tabOK F T = true := by
  have key : ∀ (L : List (List ℕ)) (k₀ : ℕ),
      (∀ j < L.length, entryOK F T (L.getD j []) (k₀ + j) = true) →
      List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun l _ ih k => andB (entryOK F T l k) (ih (k + 1))) L k₀ = true := by
    intro L
    induction L with
    | nil => intro _ _; rfl
    | cons l L ih =>
      intro k₀ hL
      change andB (entryOK F T l k₀) (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
        (fun l _ ih k => andB (entryOK F T l k) (ih (k + 1))) L (k₀ + 1)) = true
      rw [andB_eq, Bool.and_eq_true]
      refine ⟨by simpa using hL 0 (by simp), ih _ fun j hj => ?_⟩
      have := hL (j + 1) (by simpa using hj)
      rwa [List.getD_cons_succ, (by omega : k₀ + (j + 1) = k₀ + 1 + j)] at this
  exact key T.arrs 0 (fun j hj => by simpa using h j hj)

end CFSG.KC.KDense

end
