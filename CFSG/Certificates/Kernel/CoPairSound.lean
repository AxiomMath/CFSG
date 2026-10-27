module

public import Certificates.Data.Kernel.CoPair

public section

namespace CFSG.KC.CoPair

open CFSG.Monster.Existence.CoPair.Native CFSG.Monster.VisCert.Native

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem ifB_eq (c t e : Bool) : ifB c t e = if c = true then t else e := by cases c <;> rfl

theorem letB_eq (y : Nat) (k : Nat → Bool) : letB y k = k y := by cases y <;> rfl

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (f n) (allN n f) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem allR_iff (lo n : Nat) (f : Nat → Bool) :
    allR lo n f = true ↔ ∀ i, lo ≤ i → i < lo + n → f i = true := by
  unfold allR
  rw [allN_iff]
  constructor
  · intro h i h1 h2
    have := h (i - lo) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h1] at this
  · intro h i hi
    exact h _ (Nat.le_add_right lo i) (by rw [Nat.add_eq]; omega)

theorem all_of_allR {f : Nat → Bool} {lo n : Nat} (h1 : ∀ i < lo, f i = true)
    (h2 : allR lo n f = true) : ∀ i < lo + n, f i = true := by
  intro i hi
  by_cases h : i < lo
  · exact h1 i h
  · exact (allR_iff lo n f).1 h2 i (by omega) hi

theorem all_of_chunks {f : Nat → Bool} {c K : Nat} (h : ∀ k < K, allR (c * k) c f = true) :
    ∀ i < c * K, f i = true := by
  intro i hi
  have hc : 0 < c := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hi
  have hk : i / c < K := (Nat.div_lt_iff_lt_mul hc).2 (by rw [Nat.mul_comm]; exact hi)
  refine (allR_iff _ _ _).1 (h (i / c) hk) i (Nat.mul_div_le i c) ?_
  have := Nat.lt_mul_div_succ i hc
  rw [Nat.left_distrib, Nat.mul_one] at this
  exact this

theorem f24_lt (X i : Nat) : f24 X i < 2 ^ 24 :=
  Nat.and_lt_two_pow _ (by decide)

theorem actGo_acc (rows : Array Nat) (v : Nat) :
    ∀ n acc, actGo rows v n acc = acc ^^^ actGo rows v n 0
  | 0, acc => by simp [actGo]
  | n + 1, acc => by
    simp only [actGo]
    rw [actGo_acc rows v n, actGo_acc rows v n (if v.testBit n then 0 ^^^ rows[n]! else 0)]
    split <;> simp [Nat.xor_assoc]

theorem xor_xor_xor (a b c d : Nat) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [Nat.xor_assoc, ← Nat.xor_assoc b, Nat.xor_comm b c, Nat.xor_assoc c, ← Nat.xor_assoc]

theorem actGo_xor (rows : Array Nat) (a b : Nat) :
    ∀ n, actGo rows (a ^^^ b) n 0 = actGo rows a n 0 ^^^ actGo rows b n 0
  | 0 => by simp [actGo]
  | n + 1 => by
    simp only [actGo]
    rw [actGo_acc rows (a ^^^ b) n, actGo_acc rows a n, actGo_acc rows b n, actGo_xor rows a b n,
      Nat.testBit_xor, xor_xor_xor]
    congr 1
    cases a.testBit n <;> cases b.testBit n <;> simp

theorem actRows_xor (rows : Array Nat) (a b : Nat) :
    actRows rows (a ^^^ b) = actRows rows a ^^^ actRows rows b :=
  actGo_xor rows a b 24

theorem actLetters_xor : ∀ (w : List Nat) (a b : Nat),
    actLetters w (a ^^^ b) = actLetters w a ^^^ actLetters w b
  | [], _, _ => rfl
  | l :: w, a, b => by
    simp only [actLetters]
    rw [actRows_xor, actLetters_xor w]

@[expose] def bitsX (v : Nat) (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bitsX v g n ^^^ (if v.testBit n then g n else 0)

theorem bitsX_congr_v {v u : Nat} (g : Nat → Nat) :
    ∀ n, (∀ i < n, v.testBit i = u.testBit i) → bitsX v g n = bitsX u g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bitsX]
    rw [bitsX_congr_v g n (fun i hi => h i (by omega)), h n (by omega)]

theorem bitsX_congr_g (v : Nat) {g g' : Nat → Nat} :
    ∀ n, (∀ i < n, g i = g' i) → bitsX v g n = bitsX v g' n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bitsX]
    rw [bitsX_congr_g v n (fun i hi => h i (by omega)), h n (by omega)]

theorem bitsX_xor (a b : Nat) (g : Nat → Nat) :
    ∀ n, bitsX (a ^^^ b) g n = bitsX a g n ^^^ bitsX b g n
  | 0 => by simp [bitsX]
  | n + 1 => by
    simp only [bitsX]
    rw [bitsX_xor a b g n, Nat.testBit_xor, xor_xor_xor]
    congr 1
    cases a.testBit n <;> cases b.testBit n <;> simp

theorem expand (f : Nat → Nat) (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) :
    ∀ n v, v < 2 ^ n → f v = bitsX v (fun i => f (2 ^ i)) n := by
  have f0 : f 0 = 0 := by
    have h := hf 0 0
    rw [Nat.xor_self, Nat.xor_self] at h
    exact h
  intro n
  induction n with
  | zero =>
    intro v hv
    have : v = 0 := by simpa using hv
    subst this
    simp [bitsX, f0]
  | succ n ih =>
    intro v hv
    have hu : v % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
    have hdec : v = v % 2 ^ n ^^^ (if v.testBit n then 2 ^ n else 0) := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_xor, Nat.testBit_mod_two_pow]
      by_cases hj : j < n
      · have : (if v.testBit n then 2 ^ n else 0).testBit j = false := by
          split
          · rw [Nat.testBit_two_pow]
            simp only [decide_eq_false_iff_not]
            omega
          · exact Nat.zero_testBit j
        simp [hj, this]
      · by_cases hjn : j = n
        · subst hjn
          cases h : v.testBit j <;> simp
        · have h1 : v.testBit j = false := Nat.testBit_lt_two_pow
            (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
          have h2 : (if v.testBit n then 2 ^ n else 0).testBit j = false := by
            split
            · rw [Nat.testBit_two_pow]
              simp only [decide_eq_false_iff_not]
              omega
            · exact Nat.zero_testBit j
          simp [hj, h1, h2]
    have hc : f (if v.testBit n then 2 ^ n else 0) = if v.testBit n then f (2 ^ n) else 0 := by
      split
      · rfl
      · exact f0
    have hb : bitsX v (fun i => f (2 ^ i)) n = bitsX (v % 2 ^ n) (fun i => f (2 ^ i)) n :=
      bitsX_congr_v _ n fun i hi => by rw [Nat.testBit_mod_two_pow]; simp [hi]
    calc f v = f (v % 2 ^ n ^^^ (if v.testBit n then 2 ^ n else 0)) := by rw [← hdec]
      _ = f (v % 2 ^ n) ^^^ (if v.testBit n then f (2 ^ n) else 0) := by rw [hf, hc]
      _ = bitsX v (fun i => f (2 ^ i)) (n + 1) := by
        rw [ih _ hu, bitsX, hb]

theorem blt_land_shiftLeft (v i : Nat) : Nat.blt 0 (Nat.land v (Nat.shiftLeft 1 i)) = v.testBit i := by
  have h : v &&& 1 <<< i = if v.testBit i then 2 ^ i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    split
    · rename_i hv
      rw [Nat.testBit_two_pow]
      by_cases hij : i = j
      · subst hij
        simp [hv]
      · simp [hij]
    · rename_i hv
      rw [Nat.zero_testBit]
      by_cases hij : i = j
      · subst hij
        simp [hv]
      · simp [hij]
  change Nat.blt 0 (v &&& 1 <<< i) = _
  rw [h]
  split
  · rename_i hv
    rw [hv]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos i)
  · rename_i hv
    simp only [Bool.not_eq_true] at hv
    rw [hv]
    rfl

theorem actM_eq (M v : Nat) : actM M v = bitsX v (f24 M) 24 := by
  unfold actM
  generalize 24 = n
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.xor _ _ = _
    rw [ih, bitsX, blt_land_shiftLeft]
    cases v.testBit n <;> rfl

theorem actM_xor (M a b : Nat) : actM M (a ^^^ b) = actM M a ^^^ actM M b := by
  rw [actM_eq, actM_eq, actM_eq, bitsX_xor]

theorem rows_sound {M : Nat} {w : List Nat} (h : rowsOK M w = true) :
    ∀ v < 2 ^ 24, actLetters w v = actM M v := by
  have hr := (allN_iff _ _).1 h
  intro v hv
  rw [expand (actLetters w) (actLetters_xor w) 24 v hv, actM_eq]
  refine bitsX_congr_g v 24 fun i hi => ?_
  have := hr i hi
  rw [Nat.beq_eq, show Nat.shiftLeft 1 i = 2 ^ i from Nat.one_shiftLeft i] at this
  exact this.symm

theorem split24 {v : Nat} (hv : v < 2 ^ 24) :
    v &&& 255 ^^^ ((v >>> 8 &&& 255) <<< 8 ^^^ (v >>> 16 &&& 255) <<< 16) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h255 : (255 : Nat) = 2 ^ 8 - 1 := rfl
  simp only [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, h255,
    Nat.testBit_two_pow_sub_one]
  by_cases h1 : j < 8
  · simp [h1, show ¬ j ≥ 8 by omega, show ¬ j ≥ 16 by omega]
  by_cases h2 : j < 16
  · simp [h1, show j ≥ 8 by omega, show j - 8 < 8 by omega, show ¬ j ≥ 16 by omega,
      show 8 + (j - 8) = j by omega]
  by_cases h3 : j < 24
  · simp [h1, show j ≥ 8 by omega, show ¬ j - 8 < 8 by omega, show j ≥ 16 by omega,
      show j - 16 < 8 by omega, show 16 + (j - 16) = j by omega]
  · have : v.testBit j = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h1, show ¬ j - 8 < 8 by omega, show ¬ j - 16 < 8 by omega, this]

theorem tab_get {M T : Nat} (h : tabOK M T = true) {k x : Nat} (hk : k < 3) (hx : x < 256) :
    f24 T (256 * k + x) = actM M (x <<< (8 * k)) := by
  have := (allN_iff _ _).1 h (256 * k + x) (by omega)
  rw [Nat.beq_eq] at this
  rw [this]
  change actM M (((256 * k + x) &&& 255) <<< (8 * ((256 * k + x) >>> 8))) = _
  have e1 : (256 * k + x) &&& 255 = x := by
    rw [show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e2 : (256 * k + x) >>> 8 = k := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  rw [e1, e2]

theorem tab_sound {M T : Nat} (h : tabOK M T = true) : ∀ v < 2 ^ 24, bact T v = actM M v := by
  intro v hv
  have hx : v &&& 255 < 256 := Nat.and_lt_two_pow _ (by decide : 255 < 2 ^ 8)
  have hy : v >>> 8 &&& 255 < 256 := Nat.and_lt_two_pow _ (by decide : 255 < 2 ^ 8)
  have hz : v >>> 16 &&& 255 < 256 := Nat.and_lt_two_pow _ (by decide : 255 < 2 ^ 8)
  have t0 := tab_get h (k := 0) (by decide) hx
  have t1 := tab_get h (k := 1) (by decide) hy
  have t2 := tab_get h (k := 2) (by decide) hz
  simp only [Nat.mul_zero, Nat.zero_add, Nat.shiftLeft_zero, Nat.mul_one] at t0 t1 t2
  change f24 T (v &&& 255) ^^^ (f24 T (256 + (v >>> 8 &&& 255)) ^^^ f24 T (512 + (v >>> 16 &&& 255)))
    = _
  rw [t0, t1, show 512 + (v >>> 16 &&& 255) = 256 * 2 + (v >>> 16 &&& 255) from rfl, t2,
    ← actM_xor, ← actM_xor, split24 hv]

theorem bact_eq {M T : Nat} {w : List Nat} (hr : rowsOK M w = true) (ht : tabOK M T = true) :
    ∀ v < 2 ^ 24, bact T v = actLetters w v := fun v hv => by
  rw [tab_sound ht v hv, rows_sound hr v hv]

inductive Reach2 (f g : Nat → Nat) (a : Nat) : Nat → Prop
  | base : Reach2 f g a a
  | left {x : Nat} : Reach2 f g a x → Reach2 f g a (f x)
  | right {x : Nat} : Reach2 f g a x → Reach2 f g a (g x)

theorem orbPt_spec {TX TY P E N s i : Nat} (h : orbPt TX TY P E N s i = true) :
    r16 (f64 E i) 0 < N ∧ f24 P (r16 (f64 E i) 0) = bact TX (f24 P i) ∧
    r16 (f64 E i) 1 < N ∧ f24 P (r16 (f64 E i) 1) = bact TY (f24 P i) ∧
    (i + 1 < N → f24 P i < f24 P (i + 1)) ∧
    (r16 (f64 E i) 3 = 0 → i = s) ∧
    (r16 (f64 E i) 3 ≠ 0 → r16 (f64 E i) 2 < N ∧
      r16 (f64 E (r16 (f64 E i) 2)) 3 < r16 (f64 E i) 3 ∧
      (r16 (f64 E (r16 (f64 E i) 2)) 0 = i ∨ r16 (f64 E (r16 (f64 E i) 2)) 1 = i)) := by
  unfold orbPt at h
  simp only [letB_eq, andB_eq, ifB_eq, orB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  refine ⟨h0, h1, h2, h3, fun hi => ?_, fun hz => ?_, fun hz => ?_⟩
  · simpa [Nat.succ_eq_add_one, hi] using h4
  · simpa [hz] using h5
  · simpa [hz] using h5

theorem orbOK_sound {wx wy : List Nat} {seed N : Nat} {D : OrbData}
    (h : orbOK wx wy seed N D = true) :
    D.s < N ∧ f24 D.P D.s = seed ∧
    (∀ i j, i < j → j < N → f24 D.P i < f24 D.P j) ∧
    (∀ i < N, ∃ j < N, f24 D.P j = actLetters wx (f24 D.P i)) ∧
    (∀ i < N, ∃ j < N, f24 D.P j = actLetters wy (f24 D.P i)) ∧
    (∀ i < N, Reach2 (actLetters wx) (actLetters wy) seed (f24 D.P i)) := by
  unfold orbOK at h
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hrx, hry, htx, hty, hs, hseed, hall⟩ := h
  have hpt := fun i hi => orbPt_spec ((allN_iff _ _).1 hall i hi)
  have hX : ∀ v < 2 ^ 24, bact D.TX v = actLetters wx v := bact_eq hrx htx
  have hY : ∀ v < 2 ^ 24, bact D.TY v = actLetters wy v := bact_eq hry hty
  refine ⟨hs, hseed, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      have hstep := (hpt j (by omega)).2.2.2.2.1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact Nat.lt_trans (ih h' (by omega)) hstep
      · exact hstep
  · obtain ⟨h0, h1, -⟩ := hpt i hi
    exact ⟨_, h0, by rw [h1, hX _ (f24_lt _ _)]⟩
  · obtain ⟨-, -, h2, h3, -⟩ := hpt i hi
    exact ⟨_, h2, by rw [h3, hY _ (f24_lt _ _)]⟩
  · have key : ∀ m i, i < N → r16 (f64 D.E i) 3 = m →
        Reach2 (actLetters wx) (actLetters wy) seed (f24 D.P i) := by
      intro m
      induction m using Nat.strongRecOn with
      | _ m ih =>
        intro i hi hm
        obtain ⟨-, -, -, -, -, hz, hnz⟩ := hpt i hi
        by_cases h0 : r16 (f64 D.E i) 3 = 0
        · rw [hz h0, hseed]
          exact Reach2.base
        · obtain ⟨hp, hlt, hedge⟩ := hnz h0
          have hr := ih _ (by omega) _ hp rfl
          obtain ⟨-, hp1, -, hp3, -⟩ := hpt _ hp
          rcases hedge with he | he
          · rw [he] at hp1
            rw [hp1, hX _ (f24_lt _ _)]
            exact Reach2.left hr
          · rw [he] at hp3
            rw [hp3, hY _ (f24_lt _ _)]
            exact Reach2.right hr
    exact fun i hi => key _ i hi rfl

theorem orbOK_intro {wx wy : List Nat} {seed N : Nat} {D : OrbData} (hrx : rowsOK D.MX wx = true)
    (hry : rowsOK D.MY wy = true) (htx : tabOK D.MX D.TX = true) (hty : tabOK D.MY D.TY = true)
    (hs : D.s < N) (hseed : f24 D.P D.s = seed)
    (hall : ∀ i < N, orbPt D.TX D.TY D.P D.E N D.s i = true) : orbOK wx wy seed N D = true := by
  unfold orbOK
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
  exact ⟨hrx, hry, htx, hty, hs, hseed, (allN_iff _ _).2 hall⟩

end CFSG.KC.CoPair

end
