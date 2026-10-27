module

public import CFSG.Certificates.Kernel.KDenseP.StepSound
public import CFSG.Certificates.Kernel.KDense.Glue
public import Certificates.Data.Kernel.KDenseP.Plan
public import Certificates.Data.Kernel.KDenseP.Val

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense CFSG.Monster.AxisCount

theorem repN_succ (S n m : ℕ) : repN S (n + 1) m = repN S n m ||| m <<< (n * S) := rfl

theorem repN_lt {S m : ℕ} (hm : m < 2 ^ S) (n : ℕ) : repN S n m < 2 ^ (n * S) := by
  induction n with
  | zero =>
    change 0 < 2 ^ (0 * S)
    positivity
  | succ n ih =>
    rw [repN_succ]
    refine Nat.or_lt_two_pow (lt_of_lt_of_le ih
      (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right S (Nat.le_succ n)))) ?_
    rw [Nat.shiftLeft_eq, (by ring : (n + 1) * S = S + n * S), pow_add]
    exact Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos _)

theorem testBit_repN {S m : ℕ} (hm : m < 2 ^ S) {p : ℕ} (hp : p < S) {n b : ℕ} (hb : b < n) :
    (repN S n m).testBit (b * S + p) = m.testBit p := by
  induction n with
  | zero => exact absurd hb (Nat.not_lt_zero _)
  | succ n ih =>
    rw [repN_succ, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge b n with hb' | hb'
    · have h1 := Nat.mul_le_mul_right S (hb' : b + 1 ≤ n)
      rw [Nat.succ_mul] at h1
      have h2 : ¬ b * S + p ≥ n * S := by omega
      simp [ih hb', h2]
    · obtain rfl : b = n := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (repN_lt hm b)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp

@[expose] noncomputable def maskN (S n x : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (ones S) (fun b acc => Nat.land acc (planeN S b x)) n

theorem normN_eq (S n x : ℕ) : normN S n x = x ^^^ repN S n (maskN S n x) := rfl

theorem maskN_lt (S n x : ℕ) : maskN S n x < 2 ^ S := by
  cases n with
  | zero => exact ones_lt S
  | succ n =>
    change (maskN S n x &&& ((x >>> (n * S)) &&& ones S)) < 2 ^ S
    exact Nat.and_lt_two_pow _ (Nat.and_lt_two_pow _ (ones_lt S))

theorem testBit_maskN {S p : ℕ} (hp : p < S) (n x : ℕ) :
    (maskN S n x).testBit p = true ↔ ∀ b < n, x.testBit (b * S + p) = true := by
  induction n with
  | zero =>
    change (ones S).testBit p = true ↔ _
    simp [testBit_ones hp]
  | succ n ih =>
    change (maskN S n x &&& ((x >>> (n * S)) &&& ones S)).testBit p = true ↔ _
    rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones hp, Bool.and_true,
      Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ b hb
      rcases Nat.lt_or_ge b n with hb' | hb'
      · exact h1 b hb'
      · obtain rfl : b = n := by omega
        exact h2
    · intro h
      exact ⟨fun b hb => h b (by omega), h n (by omega)⟩

theorem sum_two_pow (n : ℕ) : ∑ b ∈ Finset.range n, 2 ^ b = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

theorem resPN_normN {S p : ℕ} (hp : p < S) (n x : ℕ) :
    resPN n S (normN S n x) p = resPN n S x p := by
  have hb : ∀ b < n, (normN S n x).testBit (b * S + p) =
      (x.testBit (b * S + p) ^^ (maskN S n x).testBit p) := fun b hb => by
    rw [normN_eq, Nat.testBit_xor, testBit_repN (maskN_lt S n x) hp hb]
  unfold resPN
  by_cases hm : (maskN S n x).testBit p = true
  · have hx := (testBit_maskN hp n x).1 hm
    have e1 : ∑ b ∈ Finset.range n, 2 ^ b * (normN S n x / 2 ^ (b * S + p) % 2) = 0 :=
      Finset.sum_eq_zero fun b h => by
        rw [← Nat.toNat_testBit, hb b (Finset.mem_range.1 h), hm, hx b (Finset.mem_range.1 h)]
        simp
    have e2 : ∑ b ∈ Finset.range n, 2 ^ b * (x / 2 ^ (b * S + p) % 2) = 2 ^ n - 1 := by
      rw [← sum_two_pow]
      refine Finset.sum_congr rfl fun b h => ?_
      rw [← Nat.toNat_testBit, hx b (Finset.mem_range.1 h)]
      simp
    rw [e1, e2, Nat.cast_zero, ZMod.natCast_self]
  · rw [Bool.not_eq_true] at hm
    congr 1
    refine Finset.sum_congr rfl fun b h => ?_
    rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, hb b (Finset.mem_range.1 h), hm, Bool.xor_false]

theorem normN_lt {S n x : ℕ} (hx : x < 2 ^ (n * S)) : normN S n x < 2 ^ (n * S) := by
  rw [normN_eq]
  exact Nat.xor_lt_two_pow hx (repN_lt (maskN_lt S n x) n)

theorem lt_of_normN {S n x : ℕ} (hx : normN S n x < 2 ^ (n * S)) : x < 2 ^ (n * S) := by
  rw [normN_eq] at hx
  have e := Nat.xor_lt_two_pow hx (repN_lt (maskN_lt S n x) n)
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at e

theorem resPN_congr {n S x y p : ℕ} (hp : p < S) (h : normN S n x = normN S n y) :
    resPN n S y p = resPN n S x p := by
  rw [← resPN_normN hp, ← h, resPN_normN hp]

theorem stEqN_iff (n : ℕ) (f X A W f' X' A' W' : _) : stEqN n (f, X, A, W) (f', X', A', W') = true ↔
    f = true ∧ f' = true ∧ normN SX n X = normN SX n X' ∧ normN SA n A = normN SA n A' ∧
      normN SX n W = normN SX n W' := by
  change andB f (andB f' (andB (Nat.beq (normN SX n X) (normN SX n X'))
    (andB (Nat.beq (normN SA n A) (normN SA n A')) (Nat.beq (normN SX n W) (normN SX n W'))))) =
      true ↔ _
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq]

theorem stEqN_flag {n : ℕ} {s t : St} (h : stEqN n s t = true) : s.1 = true := by
  obtain ⟨f, X, A, W⟩ := s
  obtain ⟨f', X', A', W'⟩ := t
  exact ((stEqN_iff _ _ _ _ _ _ _ _ _).1 h).1

theorem stEqN_rep {n : ℕ} {v : Native.DVec} {s t : St} (h : stEqN n s t = true) (hs : RepN n v s) :
    RepN n v t := by
  obtain ⟨f, X, A, W⟩ := s
  obtain ⟨f', X', A', W'⟩ := t
  obtain ⟨-, -, hX, hA, hW⟩ := (stEqN_iff _ _ _ _ _ _ _ _ _).1 h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, ?_, fun i hi j hj => ?_, fun p hp hq => ?_, ?_,
    fun r hr j hj => ?_, fun p hp hq => ?_, ?_⟩
  · rw [resPN_congr (xposK_lt hq) hX]
    exact h1 q hq
  · rw [resPN_congr hp hX]
    exact h2 p hp hq
  · exact lt_of_normN (hX ▸ normN_lt h3)
  · rw [resPN_congr (by rw [SA_eq]; omega) hA]
    exact h4 i hi j hj
  · rw [resPN_congr hp hA]
    exact h5 p hp hq
  · exact lt_of_normN (hA ▸ normN_lt h6)
  · rw [resPN_congr (by rw [SX_eq]; omega) hW]
    exact h7 r hr j hj
  · rw [resPN_congr hp hW]
    exact h8 p hp hq
  · exact lt_of_normN (hW ▸ normN_lt h9)

theorem two_mul_two_pow_pred {n : ℕ} (hn : 1 ≤ n) : (2 : ZMod (2 ^ n - 1)) * 2 ^ (n - 1) = 1 := by
  have h : ((2 ^ n - 1 : ℕ) : ZMod (2 ^ n - 1)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_sub Nat.one_le_two_pow] at h
  push_cast at h
  rw [sub_eq_zero] at h
  rw [← pow_succ', Nat.sub_add_cancel hn, h]

theorem resN_halve {n : ℕ} (hn : 1 ≤ n) {v : Native.DVec} (he : 0 < v.e)
    (hD : ∀ x ∈ v.D, x % 2 = 0) (k : ℕ) : resN n ⟨v.e - 1, v.D.map (· / 2)⟩ k = resN n v k := by
  obtain ⟨e, D⟩ := v
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt he
  simp only [resN, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases hk : D[k]? with _ | x
  · simp
  · have hx : x % 2 = 0 := hD x (Array.mem_of_getElem? hk)
    obtain ⟨y, rfl⟩ : 2 ∣ x := Int.dvd_of_emod_eq_zero hx
    have h2 := two_mul_two_pow_pred hn
    simp only [Option.map_some, Option.getD_some, Nat.add_sub_cancel, zero_add,
      Int.mul_ediv_cancel_left _ two_ne_zero]
    push_cast
    linear_combination (-(y : ZMod (2 ^ n - 1)) * (2 ^ (n - 1)) ^ e) * h2

theorem resN_reduceN {n : ℕ} (hn : 1 ≤ n) (m : ℕ) (v : Native.DVec) (k : ℕ) :
    resN n (Native.reduceN m v) k = resN n v k := by
  induction m generalizing v with
  | zero => rfl
  | succ m ih =>
    rw [Native.reduceN]
    split_ifs with h
    · simp only [Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true_iff_forall_mem,
        beq_iff_eq] at h
      rw [ih, resN_halve hn h.1 h.2]
    · rfl

theorem rep_reduceN {n : ℕ} (hn : 1 ≤ n) {v : Native.DVec} {s : St} (h : RepN n v s) :
    RepN n v.reduce s := by
  have e : resN n v.reduce = resN n v := funext (resN_reduceN hn v.e v)
  unfold RepN at h ⊢
  rw [e]
  exact h

theorem stepN_flag {n lg : ℕ} {F : Fix} {T : MonoTab} (g : Native.Gen) (s : St)
    (h : (stepN n lg F T g s).1 = true) : s.1 = true := by
  obtain ⟨f, X, A, W⟩ := s
  cases g with
  | rho q =>
    obtain ⟨qs, qa, qd⟩ := q
    have e : (stepN n lg F T (.rho (qs, qa, qd)) (f, X, A, W)).1 = andB f true := rfl
    rw [e, andB_eq, Bool.and_true] at h
    exact h
  | perm arr =>
    have e : (stepN n lg F T (.perm arr) (f, X, A, W)).1 =
      andB f (findIdx (arrList arr) T.keys).1 := rfl
    rw [e, andB_eq, Bool.and_eq_true] at h
    exact h.1
  | sign a =>
    have e : (stepN n lg F T (.sign a) (f, X, A, W)).1 = andB f (findIdx [a] T.keys).1 := rfl
    rw [e, andB_eq, Bool.and_eq_true] at h
    exact h.1
  | xi => exact h
  | tau => exact h

theorem runN_cons {n lg : ℕ} {F : Fix} {T : MonoTab} (g : Native.Gen) (w : List Native.Gen)
    (i m : ℕ) (s : St) :
    runN n lg F T (g :: w) i m s = Bool.rec (motive := fun _ => St)
      (Bool.rec (motive := fun _ => St) (runN n lg F T w i (m - 1) (stepN n lg F T g s)) s
        (Nat.beq m 0))
      (runN n lg F T w (i - 1) m s) (Nat.blt 0 i) := by
  rw [← forceSt_eq (stepN n lg F T g s) (fun t' => runN n lg F T w i (m - 1) t')]
  rfl

theorem runN_pos {n lg : ℕ} {F : Fix} {T : MonoTab} (g : Native.Gen) (w : List Native.Gen) {i : ℕ}
    (hi : 0 < i) (m : ℕ) (s : St) : runN n lg F T (g :: w) i m s = runN n lg F T w (i - 1) m s := by
  rw [runN_cons, (Nat.blt_eq.mpr hi : Nat.blt 0 i = true)]

theorem runN_zero_succ {n lg : ℕ} {F : Fix} {T : MonoTab} (g : Native.Gen) (w : List Native.Gen)
    (m : ℕ) (s : St) :
    runN n lg F T (g :: w) 0 (m + 1) s = runN n lg F T w 0 m (stepN n lg F T g s) := by
  rw [runN_cons]
  rfl

theorem runN_len_zero {n lg : ℕ} {F : Fix} {T : MonoTab} (w : List Native.Gen) (i : ℕ) (s : St) :
    runN n lg F T w i 0 s = s := by
  induction w generalizing i with
  | nil => rfl
  | cons g w ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rfl
    · rw [runN_pos g w hi, ih]

theorem runN_flag {n lg : ℕ} {F : Fix} {T : MonoTab} (w : List Native.Gen) (i m : ℕ) (s : St)
    (h : (runN n lg F T w i m s).1 = true) : s.1 = true := by
  induction w generalizing i m s with
  | nil => exact h
  | cons g w ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases m with _ | m
      · exact h
      · rw [runN_zero_succ] at h
        exact stepN_flag g s (ih 0 m _ h)
    · rw [runN_pos g w hi] at h
      exact ih _ _ _ h

theorem runN_rep {n lg : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} {T : MonoTab}
    {KT TH OCT DU1 : Nat} (hd : dataOKP F T KT TH OCT DU1 = true) (w : List Native.Gen)
    (hL : ∀ g ∈ w, letterOK g = true) (i m : ℕ)
    (v : Native.DVec) (s : St) (hs : RepN n v s) (hf : (runN n lg F T w i m s).1 = true) :
    (∀ g ∈ (w.drop i).take m, g.validB = true) ∧
      RepN n (Native.evalWordC (Native.mkCtx ()) ((w.drop i).take m) v)
        (runN n lg F T w i m s) := by
  induction w generalizing i m v s with
  | nil =>
    refine ⟨by simp, ?_⟩
    simp only [List.drop_nil, List.take_nil]
    exact hs
  | cons g w ih =>
    have hL' : ∀ g ∈ w, letterOK g = true := fun g' hg' => hL g' (List.mem_cons_of_mem _ hg')
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rcases m with _ | m
      · exact ⟨by simp, hs⟩
      · rw [runN_zero_succ] at hf ⊢
        obtain ⟨hv, hr⟩ :=
          stepN_sound hn hlg hd g (hL g List.mem_cons_self) v s hs (runN_flag w 0 m _ hf)
        obtain ⟨h1, h2⟩ := ih hL' 0 m _ _ (rep_reduceN (by omega) hr) hf
        simp only [List.drop_zero, List.take_succ_cons, List.mem_cons, forall_eq_or_imp] at h1 h2 ⊢
        exact ⟨⟨hv, h1⟩, h2⟩
    · rw [runN_pos g w hi] at hf ⊢
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hi
      simpa using ih hL' _ m v s hs hf

theorem rep_uniqueN {n : ℕ} {u v : Native.DVec} {s : St} (hu : RepN n u s) (hv : RepN n v s)
    {k : ℕ} (hk : k < 196884) : resN n u k = resN n v k := by
  by_cases h1 : k < 300
  · obtain ⟨i, hi, j, hj, rfl⟩ := aIdx_cover h1
    rw [← hu.2.2.2.1 i hi j hj, hv.2.2.2.1 i hi j hj]
  by_cases h2 : k < 98580
  · have e : k = 300 + (k - 300) := by omega
    rw [e, ← hu.1 _ (by omega), hv.1 _ (by omega)]
  · have e : k = 98580 + 24 * ((k - 98580) / 24) + (k - 98580) % 24 := by omega
    rw [e, ← hu.2.2.2.2.2.2.1 _ (by omega) _ (by omega),
      hv.2.2.2.2.2.2.1 _ (by omega) _ (by omega)]

theorem resAt_eq (S n x p : ℕ) :
    resAt S n x p = (∑ b ∈ Finset.range n, 2 ^ b * (x / 2 ^ (b * S + p) % 2)) % (2 ^ n - 1) := by
  have h : ∀ m, Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.add acc (Nat.shiftLeft (bitN x (Nat.add (Nat.mul b S) p)) b)) m =
      ∑ b ∈ Finset.range m, 2 ^ b * (x / 2 ^ (b * S + p) % 2) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      change _ + bitN x (m * S + p) <<< m = _
      rw [Nat.shiftLeft_eq, bitN_eq, Nat.mul_comm (x / 2 ^ (m * S + p) % 2)]
  change (Nat.rec (motive := fun _ => Nat) 0
      (fun b acc => Nat.add acc (Nat.shiftLeft (bitN x (Nat.add (Nat.mul b S) p)) b)) n) %
    (1 <<< n - 1) = _
  rw [h, Nat.one_shiftLeft]

theorem resAt_cast (S n x p : ℕ) : (resAt S n x p : ZMod (2 ^ n - 1)) = resPN n S x p := by
  rw [resAt_eq, ZMod.natCast_mod]
  rfl

theorem resXq_eq (n q : ℕ) (s : St) (p : ℕ) : resXq n q s p = resAt SX n s.2.1 p % q := by
  obtain ⟨f, X, A, W⟩ := s
  rfl

theorem resXq_cast {n q : ℕ} (hq : q ∣ 2 ^ n - 1) (s : St) (p : ℕ) :
    ((resXq n q s p : ℕ) : ZMod q) = ZMod.castHom hq (ZMod q) (resPN n SX s.2.1 p) := by
  rw [resXq_eq, ← resAt_cast, map_natCast, ZMod.natCast_mod]

theorem pos_of_dvd_two_pow_sub_one {n q : ℕ} (hn : 1 ≤ n) (hq : q ∣ 2 ^ n - 1) : 0 < q := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [h, zero_dvd_iff] at hq
  have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

theorem sepN {n q : ℕ} (hn : 1 ≤ n) (hq : q ∣ 2 ^ n - 1) {u v : Native.DVec} {s t : St}
    (hu : RepN n u s) (hv : RepN n v t) {p : ℕ} (hne : resXq n q s p ≠ resXq n q t p)
    (hp : p < SX) :
    ∃ k < 196884,
      ZMod.castHom hq (ZMod q) (resN n u k) ≠ ZMod.castHom hq (ZMod q) (resN n v k) := by
  by_cases hx : ∃ r < 98280, xposK r = p
  · obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨300 + r, by omega, fun e => hne ?_⟩
    rw [← hu.1 r hr, ← hv.1 r hr, ← resXq_cast, ← resXq_cast, ZMod.natCast_eq_natCast_iff'] at e
    have hlt : ∀ w : St, resXq n q w (xposK r) < q := fun w => by
      rw [resXq_eq]
      exact Nat.mod_lt _ (pos_of_dvd_two_pow_sub_one hn hq)
    rwa [Nat.mod_eq_of_lt (hlt s), Nat.mod_eq_of_lt (hlt t)] at e
  · push Not at hx
    have z : ∀ (w : Native.DVec) (r : St), RepN n w r → resXq n q r p = 0 := fun w r hr => by
      have h0 := hr.2.1 p hp hx
      rw [← resAt_cast, ZMod.natCast_eq_zero_iff] at h0
      rw [resXq_eq, Nat.mod_eq_zero_of_dvd (dvd_trans hq h0)]
    exact absurd ((z u s hu).trans (z v t hv).symm) hne

theorem listEq_eq : ∀ {l m : List ℕ}, listEq l m = true → l = m
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: l, y :: m, h => by
    change andB (Nat.beq x y) (listEq l m) = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, listEq_eq h.2]

theorem genEq_eq {g h : Native.Gen} (H : genEq g h = true) : g = h := by
  cases g <;> cases h <;> first | rfl | exact absurd H Bool.false_ne_true | skip
  · rename_i q q'
    obtain ⟨s, a, d⟩ := q
    obtain ⟨s', a', d'⟩ := q'
    change andB (Bool.rec (motive := fun _ => Bool) (notB s') s' s)
      (andB (Nat.beq a a') (Nat.beq d d')) = true at H
    rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.beq_eq] at H
    obtain ⟨hs, rfl, rfl⟩ := H
    cases s <;> cases s' <;> first | rfl | exact absurd hs (by decide)
  · rename_i arr arr'
    have e := listEq_eq H
    obtain ⟨l⟩ := arr
    obtain ⟨l'⟩ := arr'
    change l = l' at e
    rw [e]
  · rename_i a a'
    change Nat.beq a a' = true at H
    rw [Nat.beq_eq] at H
    rw [H]

theorem dropL_eq (o : ℕ) (w : List Native.Gen) : dropL o w = w.drop o := by
  induction o generalizing w with
  | zero => rfl
  | succ o ih =>
    change dropL o (List.rec (motive := fun _ => List Native.Gen) [] (fun _ t _ => t) w) = _
    cases w with
    | nil =>
      rw [ih]
      exact List.drop_nil.trans List.drop_nil.symm
    | cons g w =>
      rw [ih]
      rfl

theorem takeEq_eq {m : ℕ} {u v : List Native.Gen} (h : takeEq m u v = true) :
    u.take m = v.take m := by
  induction u generalizing m v with
  | nil =>
    change Nat.beq m 0 = true at h
    rw [Nat.beq_eq] at h
    subst h
    rfl
  | cons g u ih =>
    rcases m with _ | m
    · rfl
    · cases v with
      | nil => exact absurd h Bool.false_ne_true
      | cons g' v =>
        change andB (genEq g g') (takeEq m u v) = true at h
        rw [andB_eq, Bool.and_eq_true] at h
        rw [List.take_succ_cons, List.take_succ_cons, genEq_eq h.1, ih h.2]

theorem segEq_eq {u v : List Native.Gen} {o m : ℕ} (h : segEq u v o m = true) :
    (u.drop o).take m = (v.drop o).take m := by
  change takeEq m (dropL o u) (dropL o v) = true at h
  rw [dropL_eq, dropL_eq] at h
  exact takeEq_eq h

theorem seg_of {words : ℕ → List Native.Gen} {σ σ' o m : ℕ}
    (h : Bool.rec (motive := fun _ => Bool) (segEq (words σ') (words σ) o m) true
      (Nat.beq σ' σ) = true) :
    ((words σ').drop o).take m = ((words σ).drop o).take m := by
  cases hb : Nat.beq σ' σ
  · rw [hb] at h
    exact segEq_eq h
  · rw [Nat.eq_of_beq_eq_true hb]

theorem chunkN_kind0 {n lg q : ℕ} {F : Fix} {T : MonoTab} {words : ℕ → List Native.Gen} {S : ℕ → St}
    {c : ℕ} (h : chunkOKN n lg q F T words S c = true) (hk : f20 c 5 = 0) :
    stEqN n (runN n lg F T (words (f20 c 0)) (f20 c 1) (f20 c 2) (S (f20 c 3))) (S (f20 c 4)) =
      true := by
  have e : chunkOKN n lg q F T words S c = Bool.rec (motive := fun _ => Bool)
      (stEqN n (runN n lg F T (words (f20 c 0)) (f20 c 1) (f20 c 2) (S (f20 c 3))) (S (f20 c 4)))
      (andB (Nat.blt (f20 c 1) SX) (andB (flagOf (S (f20 c 3))) (andB (flagOf (S (f20 c 4)))
        (notB (Nat.beq (resXq n q (S (f20 c 3)) (f20 c 1)) (resXq n q (S (f20 c 4)) (f20 c 1)))))))
      (Nat.beq (f20 c 5) 1) := rfl
  rw [e, hk] at h
  exact h

theorem chunkN_kind1 {n lg q : ℕ} {F : Fix} {T : MonoTab} {words : ℕ → List Native.Gen} {S : ℕ → St}
    {c : ℕ} (h : chunkOKN n lg q F T words S c = true) (hk : f20 c 5 = 1) :
    f20 c 1 < SX ∧ resXq n q (S (f20 c 3)) (f20 c 1) ≠ resXq n q (S (f20 c 4)) (f20 c 1) := by
  have e : chunkOKN n lg q F T words S c = Bool.rec (motive := fun _ => Bool)
      (stEqN n (runN n lg F T (words (f20 c 0)) (f20 c 1) (f20 c 2) (S (f20 c 3))) (S (f20 c 4)))
      (andB (Nat.blt (f20 c 1) SX) (andB (flagOf (S (f20 c 3))) (andB (flagOf (S (f20 c 4)))
        (notB (Nat.beq (resXq n q (S (f20 c 3)) (f20 c 1)) (resXq n q (S (f20 c 4)) (f20 c 1)))))))
      (Nat.beq (f20 c 5) 1) := rfl
  rw [e, hk] at h
  change andB _ _ = true at h
  simp only [andB_eq, notB_eq, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
  exact ⟨h.1, Nat.ne_of_beq_eq_false h.2.2.2⟩

@[expose] noncomputable def sideFoldP (words : ℕ → List Native.Gen) (CH : ℕ → ℕ) (σ x a n : ℕ) :
    (Bool × ℕ) × ℕ :=
  Nat.rec (motive := fun _ => (Bool × ℕ) × ℕ) ((true, 0), x)
    (fun k ih => (fun c => ((andB ih.1.1 (andB
        (Bool.rec (motive := fun _ => Bool) (segEq (words (f20 c 0)) (words σ) ih.1.2 (f20 c 2))
          true (Nat.beq (f20 c 0) σ))
        (andB (Nat.beq (f20 c 1) ih.1.2) (andB (Nat.beq (f20 c 3) ih.2) (Nat.beq (f20 c 5) 0)))),
      ih.1.2 + f20 c 2), f20 c 4)) (CH (a + k))) n

theorem sideOKP_eq (words : ℕ → List Native.Gen) (CH : ℕ → ℕ) (σ len x a n : ℕ) :
    sideOKP words CH σ len x a n =
      (andB (sideFoldP words CH σ x a n).1.1 (Nat.ble len (sideFoldP words CH σ x a n).1.2),
        (sideFoldP words CH σ x a n).2) := rfl

theorem sideFoldP_succ (words : ℕ → List Native.Gen) (CH : ℕ → ℕ) (σ x a n : ℕ) :
    sideFoldP words CH σ x a (n + 1) =
      ((andB (sideFoldP words CH σ x a n).1.1 (andB
        (Bool.rec (motive := fun _ => Bool) (segEq (words (f20 (CH (a + n)) 0)) (words σ)
          (sideFoldP words CH σ x a n).1.2 (f20 (CH (a + n)) 2)) true
          (Nat.beq (f20 (CH (a + n)) 0) σ))
        (andB (Nat.beq (f20 (CH (a + n)) 1) (sideFoldP words CH σ x a n).1.2)
        (andB (Nat.beq (f20 (CH (a + n)) 3) (sideFoldP words CH σ x a n).2)
          (Nat.beq (f20 (CH (a + n)) 5) 0)))),
        (sideFoldP words CH σ x a n).1.2 + f20 (CH (a + n)) 2), f20 (CH (a + n)) 4) := rfl

theorem sideP_sound {n lg q : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} {T : MonoTab}
    {KT TH OCT DU1 : Nat} (hd : dataOKP F T KT TH OCT DU1 = true) {words : ℕ → List Native.Gen}
    (hL : ∀ σ, ∀ g ∈ words σ, letterOK g = true)
    {S : ℕ → St} {CH : ℕ → ℕ} {σ x a : ℕ} (v : Native.DVec) (hx : RepN n v (S x)) (m : ℕ)
    (hch : ∀ k < m, chunkOKN n lg q F T words S (CH (a + k)) = true)
    (h : (sideFoldP words CH σ x a m).1.1 = true) :
    (∀ g ∈ (words σ).take (sideFoldP words CH σ x a m).1.2, g.validB = true) ∧
      RepN n (Native.evalWordC (Native.mkCtx ())
        ((words σ).take (sideFoldP words CH σ x a m).1.2) v) (S (sideFoldP words CH σ x a m).2) := by
  induction m with
  | zero =>
    refine ⟨fun g hg => ?_, hx⟩
    change g ∈ (words σ).take 0 at hg
    simp at hg
  | succ m ih =>
    rw [sideFoldP_succ] at h ⊢
    simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨hr, hs, h1, h3, h5⟩ := h
    obtain ⟨iv, ir⟩ := ih (fun k hk => hch k (by omega)) hr
    have hc := chunkN_kind0 (hch m (by omega)) h5
    rw [h1, h3] at hc
    obtain ⟨jv, jr⟩ := runN_rep hn hlg hd _ (hL _) _ _ _ _ ir (stEqN_flag hc)
    rw [seg_of hs] at jv jr
    rw [List.take_add, evalWordC_append]
    refine ⟨fun g hg => ?_, stEqN_rep hc jr⟩
    rcases List.mem_append.1 hg with hg | hg
    · exact iv g hg
    · exact jv g hg

@[expose] noncomputable def planFoldP (words : ℕ → List Native.Gen) (CH : ℕ → ℕ) (nch : ℕ)
    (IT : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun it _ ih t => andB (itemOKP words CH nch it t) (ih (t + 1))) IT

theorem planFoldP_item {words : ℕ → List Native.Gen} {CH : ℕ → ℕ} {nch : ℕ} (IT : List ℕ)
    (t₀ : ℕ) (h : planFoldP words CH nch IT t₀ = true) (j : ℕ) (hj : j < IT.length) :
    itemOKP words CH nch IT[j] (t₀ + j) = true := by
  induction IT generalizing t₀ j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons it IT ih =>
    change andB (itemOKP words CH nch it t₀) (planFoldP words CH nch IT (t₀ + 1)) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rcases j with _ | j
    · exact h.1
    · rw [List.getElem_cons_succ, (by omega : t₀ + (j + 1) = t₀ + 1 + j)]
      exact ih _ h.2 j (by simpa using hj)

theorem itemOKP_spec {words : ℕ → List Native.Gen} {CH : ℕ → ℕ} {nch it t : ℕ}
    (h : itemOKP words CH nch it t = true) :
    ((sideFoldP words CH (2 * t) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).1.1 =
        true ∧
      wlen (words (2 * t)) ≤
        (sideFoldP words CH (2 * t) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).1.2) ∧
    ((sideFoldP words CH (2 * t + 1) (Nat.land it 3) fld(it, 44, 1048575)
        fld(it, 64, 1048575)).1.1 = true ∧
      wlen (words (2 * t + 1)) ≤ (sideFoldP words CH (2 * t + 1) (Nat.land it 3)
        fld(it, 44, 1048575) fld(it, 64, 1048575)).1.2) ∧
    f20 (CH fld(it, 84, 1048575)) 2 = 0 ∧
    f20 (CH fld(it, 84, 1048575)) 3 =
      (sideFoldP words CH (2 * t) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).2 ∧
    f20 (CH fld(it, 84, 1048575)) 4 = (sideFoldP words CH (2 * t + 1) (Nat.land it 3)
      fld(it, 44, 1048575) fld(it, 64, 1048575)).2 ∧
    Nat.land it 3 < 3 ∧ f20 (CH fld(it, 84, 1048575)) 5 = bitN it 2 ∧
    fld(it, 84, 1048575) < nch ∧ fld(it, 4, 1048575) + fld(it, 24, 1048575) ≤ nch ∧
    fld(it, 44, 1048575) + fld(it, 64, 1048575) ≤ nch := by
  change andB (sideOKP words CH (2 * t) (wlen (words (2 * t))) (Nat.land it 3) fld(it, 4, 1048575)
      fld(it, 24, 1048575)).1
    (andB (sideOKP words CH (2 * t + 1) (wlen (words (2 * t + 1))) (Nat.land it 3)
      fld(it, 44, 1048575) fld(it, 64, 1048575)).1
    (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 2) 0)
    (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 3) (sideOKP words CH (2 * t)
      (wlen (words (2 * t))) (Nat.land it 3) fld(it, 4, 1048575) fld(it, 24, 1048575)).2)
    (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 4) (sideOKP words CH (2 * t + 1)
      (wlen (words (2 * t + 1))) (Nat.land it 3) fld(it, 44, 1048575) fld(it, 64, 1048575)).2)
    (andB (Nat.blt (Nat.land it 3) 3) (andB (Nat.beq (f20 (CH fld(it, 84, 1048575)) 5) (bitN it 2))
    (andB (Nat.blt fld(it, 84, 1048575) nch)
    (andB (Nat.ble (fld(it, 4, 1048575) + fld(it, 24, 1048575)) nch)
      (Nat.ble (fld(it, 44, 1048575) + fld(it, 64, 1048575)) nch))))))))) = true at h
  simp only [sideOKP_eq, andB_eq, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
  exact h

theorem itemP_sound {n lg q : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} {T : MonoTab}
    {KT TH OCT DU1 : Nat} (hd : dataOKP F T KT TH OCT DU1 = true)
    (words : ℕ → List Native.Gen) (hL : ∀ σ, ∀ g ∈ words σ, letterOK g = true) (S : ℕ → St)
    (wit : ℕ → Native.DVec)
    (hinit : ∀ x < 3, RepN n (wit x) (S x)) (CH : ℕ → ℕ) (nch : ℕ) (IT : List ℕ)
    (hplan : planOKP words CH nch IT = true)
    (hch : ∀ k < nch, chunkOKN n lg q F T words S (CH k) = true) (t : ℕ) (ht : t < IT.length) :
    (∀ g ∈ words (2 * t), g.validB = true) ∧ (∀ g ∈ words (2 * t + 1), g.validB = true) ∧
    RepN n (Native.evalWord (words (2 * t)) (wit (IT[t]! % 4)))
      (S (f20 (CH fld(IT[t]!, 84, 1048575)) 3)) ∧
    RepN n (Native.evalWord (words (2 * t + 1)) (wit (IT[t]! % 4)))
      (S (f20 (CH fld(IT[t]!, 84, 1048575)) 4)) ∧
    f20 (CH fld(IT[t]!, 84, 1048575)) 2 = 0 ∧
    f20 (CH fld(IT[t]!, 84, 1048575)) 5 = IT[t]! / 4 % 2 ∧ fld(IT[t]!, 84, 1048575) < nch := by
  have hit := planFoldP_item IT 0 hplan t ht
  rw [zero_add, ← getElem!_pos IT t ht] at hit
  generalize IT[t]! = it at hit ⊢
  obtain ⟨⟨hA1, hA2⟩, ⟨hB1, hB2⟩, hf2, hf3, hf4, hx, hf5, hfn, hab, hbb⟩ := itemOKP_spec hit
  have hx4 : Nat.land it 3 = it % 4 := Nat.and_two_pow_sub_one_eq_mod it 2
  rw [hx4] at hA1 hA2 hB1 hB2 hf3 hf4 hx
  obtain ⟨vA, rA⟩ :=
    sideP_sound hn hlg hd hL _ (hinit _ hx) _ (fun k hk => hch _ (by omega)) hA1
  obtain ⟨vB, rB⟩ :=
    sideP_sound hn hlg hd hL _ (hinit _ hx) _ (fun k hk => hch _ (by omega)) hB1
  rw [wlen_eq] at hA2 hB2
  rw [List.take_of_length_le hA2] at vA rA
  rw [List.take_of_length_le hB2] at vB rB
  rw [bitN_eq] at hf5
  rw [← hf3] at rA
  rw [← hf4] at rB
  exact ⟨vA, vB, rA, rB, hf2, hf5, hfn⟩

theorem planP_rep {n lg q : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) {F : Fix} {T : MonoTab}
    {KT TH OCT DU1 : Nat} (hd : dataOKP F T KT TH OCT DU1 = true)
    (words : ℕ → List Native.Gen) (hL : ∀ σ, ∀ g ∈ words σ, letterOK g = true) (S : ℕ → St)
    (wit : ℕ → Native.DVec)
    (hinit : ∀ x < 3, RepN n (wit x) (S x)) (CH : ℕ → ℕ) (nch : ℕ) (IT : List ℕ)
    (hplan : planOKP words CH nch IT = true)
    (hch : ∀ k < nch, chunkOKN n lg q F T words S (CH k) = true) (t : ℕ) (ht : t < IT.length) :
    RepN n (Native.evalWord (words (2 * t)) (wit (IT[t]! % 4)))
      (S (f20 (CH fld(IT[t]!, 84, 1048575)) 3)) ∧
    RepN n (Native.evalWord (words (2 * t + 1)) (wit (IT[t]! % 4)))
      (S (f20 (CH fld(IT[t]!, 84, 1048575)) 4)) :=
  let h := itemP_sound hn hlg hd words hL S wit hinit CH nch IT hplan hch t ht
  ⟨h.2.2.1, h.2.2.2.1⟩

theorem planP_sound {n lg q : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) (hq : q ∣ 2 ^ n - 1) {F : Fix}
    {T : MonoTab} {KT TH OCT DU1 : Nat} (hd : dataOKP F T KT TH OCT DU1 = true)
    (words : ℕ → List Native.Gen) (hL : ∀ σ, ∀ g ∈ words σ, letterOK g = true) (S : ℕ → St)
    (wit : ℕ → Native.DVec)
    (hinit : ∀ x < 3, RepN n (wit x) (S x)) (CH : ℕ → ℕ) (nch : ℕ) (IT : List ℕ)
    (hplan : planOKP words CH nch IT = true)
    (hch : ∀ k < nch, chunkOKN n lg q F T words S (CH k) = true) (t : ℕ) (ht : t < IT.length) :
    (∀ g ∈ words (2 * t), g.validB = true) ∧ (∀ g ∈ words (2 * t + 1), g.validB = true) ∧
    (IT[t]! / 4 % 2 = 0 → ∀ k < 196884,
      resN n (Native.evalWord (words (2 * t)) (wit (IT[t]! % 4))) k =
        resN n (Native.evalWord (words (2 * t + 1)) (wit (IT[t]! % 4))) k) ∧
    (IT[t]! / 4 % 2 = 1 → ∃ k < 196884,
      ZMod.castHom hq (ZMod q) (resN n (Native.evalWord (words (2 * t)) (wit (IT[t]! % 4))) k) ≠
        ZMod.castHom hq (ZMod q)
          (resN n (Native.evalWord (words (2 * t + 1)) (wit (IT[t]! % 4))) k)) := by
  obtain ⟨vA, vB, rA, rB, hf2, hf5, hfn⟩ :=
    itemP_sound hn hlg hd words hL S wit hinit CH nch IT hplan hch t ht
  have hfc := hch _ hfn
  refine ⟨vA, vB, fun hb => ?_, fun hb => ?_⟩
  · have hc := chunkN_kind0 hfc (by rw [hf5]; exact hb)
    rw [hf2, runN_len_zero] at hc
    intro k hk
    exact rep_uniqueN (stEqN_rep hc rA) rB hk
  · obtain ⟨hp, hne⟩ := chunkN_kind1 hfc (by rw [hf5]; exact hb)
    exact sepN (by omega) hq rA rB hne hp

theorem valOK_spec {n : ℕ} {s : St} {t u : ℕ} (h : valOK n s t u = true) :
    s.1 = true ∧ trRes n s.2.2.1 = t ∧ resAt SX n s.2.1 114689 = u := by
  obtain ⟨f, X, A, W⟩ := s
  change andB f (andB (Nat.beq (trRes n A) t) (Nat.beq (resAt SX n X 114689) u)) = true at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem xposK_zero : xposK 0 = 114689 := by decide +kernel

theorem resAt_rStar {n : ℕ} {v : Native.DVec} {s : St} (hs : RepN n v s) :
    (resAt SX n s.2.1 114689 : ZMod (2 ^ n - 1)) = resN n v 300 := by
  rw [resAt_cast, ← xposK_zero, hs.1 0 (by norm_num)]

theorem trRes_eq (n A : ℕ) : trRes n A = (∑ i ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
    resAt SA n A (32 * i + j) * resAt SA n A (32 * i + j)) % (2 ^ n - 1) := by
  have hi : ∀ i acc m, Nat.rec (motive := fun _ => Nat) acc
      (fun j acc2 => (fun r => Nat.add acc2 (Nat.mul r r))
        (resAt SA n A (Nat.add (Nat.mul (nat_lit 32) i) j))) m =
      acc + ∑ j ∈ Finset.range m, resAt SA n A (32 * i + j) * resAt SA n A (32 * i + j) := by
    intro i acc m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero, add_zero]
      rfl
    | succ m ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ← ih]
      rfl
  have ho : ∀ m, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.rec (motive := fun _ => Nat) acc
        (fun j acc2 => (fun r => Nat.add acc2 (Nat.mul r r))
          (resAt SA n A (Nat.add (Nat.mul (nat_lit 32) i) j))) (nat_lit 24)) m =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range 24,
        resAt SA n A (32 * i + j) * resAt SA n A (32 * i + j) := by
    intro m
    induction m with
    | zero =>
      rw [Finset.sum_range_zero]
      rfl
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih, ← hi]
      rfl
  have e : Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1) = 2 ^ n - 1 := by
    change 1 <<< n - 1 = _
    rw [Nat.one_shiftLeft]
  exact congrArg₂ Nat.mod (ho (nat_lit 24)) e

theorem trRes_cast {n : ℕ} {v : Native.DVec} {s : St} (hs : RepN n v s) :
    (trRes n s.2.2.1 : ZMod (2 ^ n - 1)) =
      ∑ i ∈ Finset.range 24, ∑ j ∈ Finset.range 24, resN n v (Native.aIdx i j) ^ 2 := by
  rw [trRes_eq, ZMod.natCast_mod]
  push_cast
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [resAt_cast, hs.2.2.2.1 i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj), sq]

theorem valOK_sound {n : ℕ} {v : Native.DVec} {s : St} {t u : ℕ} (hs : RepN n v s)
    (h : valOK n s t u = true) :
    (t : ZMod (2 ^ n - 1)) =
        ∑ i ∈ Finset.range 24, ∑ j ∈ Finset.range 24, resN n v (Native.aIdx i j) ^ 2 ∧
      (u : ZMod (2 ^ n - 1)) = resN n v 300 := by
  obtain ⟨-, ht, hu⟩ := valOK_spec h
  rw [← ht, ← hu]
  exact ⟨trRes_cast hs, resAt_rStar hs⟩

end CFSG.KC.KDenseP

end
