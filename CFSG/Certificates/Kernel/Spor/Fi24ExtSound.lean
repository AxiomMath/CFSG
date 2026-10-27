module

public import Certificates.Data.Kernel.Spor.Fi24Ext
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound
public import CFSG.Certificates.Kernel.Spor.Mat3Sound

public section

namespace CFSG.KC.Fi24ExtS

open CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK CFSG.KC.Fi24FixS CFSG.KC.Fi24Ext CFSG.KS.Mat3

theorem letB_eq' (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by cases v <;> rfl

theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem andB_iff' {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem nrec_eq (a b : ℕ) (c : Bool) :
    Bool.rec (motive := fun _ => ℕ) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem digV_eq (CT : ℕ → ℕ) (c0 w : ℕ) (id : Bool) (i j : ℕ) :
    digV CT c0 w id i j = if j < c0 then (if id = true ∧ i = j then 1 else 0)
      else if j < c0 + w then CT ((w * i + (j - c0)) / 4) / 3 ^ ((w * i + (j - c0)) % 4) % 3
      else 0 := by
  unfold digV
  have ht : ∀ x t, trit x (Nat.mod t 4) = x / 3 ^ (t % 4) % 3 :=
    fun x t => trit_eq x _ (Nat.mod_lt t (by decide))
  rw [nrec_eq, nrec_eq, nrec_eq, strictN_eq', ht]
  simp only [Nat.blt_eq, andB_iff', Nat.beq_eq]
  rfl

theorem digRowsOK_spec {P1 P2 : ℕ} {CT : ℕ → ℕ} {c0 w : ℕ} {id : Bool} {lo m hi : ℕ}
    (h : digRowsOK P1 P2 CT c0 w id lo m hi = true) (hm : m ≤ 64 * hi) :
    ∀ i, lo ≤ i → i < lo + m → ∀ j < 781,
      P1.testBit (781 * i + j) = decide (digV CT c0 w id i j = 1) ∧
        P2.testBit (781 * i + j) = decide (digV CT c0 w id i j = 2) := by
  intro i hi1 hi2 j hj
  have h1 := allBelow_spec h hm (i - lo) (by omega)
  simp only [letB_eq'] at h1
  have e : Nat.add lo (i - lo) = i := by change lo + (i - lo) = i; omega
  rw [e] at h1
  have h2 := allBelow_spec h1 (by decide) j hj
  obtain ⟨a, b⟩ := entOK_spec h2
  rw [testBit_row _ _ _ hj] at a b
  exact ⟨a, b⟩

theorem zeroFromOK_spec {P1 P2 r : ℕ} (h : zeroFromOK P1 P2 r = true) :
    ∀ t, 781 * r ≤ t → P1.testBit t = false ∧ P2.testBit t = false := by
  intro t ht
  unfold zeroFromOK at h
  rw [andB_iff', Nat.beq_eq, Nat.beq_eq] at h
  have key : ∀ P : ℕ, Nat.shiftRight P (Nat.mul 781 r) = 0 → P.testBit t = false := by
    intro P hP
    have := congrArg (fun z => Nat.testBit z (t - 781 * r)) hP
    simp only [Nat.zero_testBit] at this
    change (P >>> (781 * r)).testBit (t - 781 * r) = false at this
    rwa [Nat.testBit_shiftRight, Nat.add_sub_cancel' ht] at this
  exact ⟨key P1 h.1, key P2 h.2⟩

theorem RS_eq : RS = 2 ^ 253 - 1 := pow_sub_one_eq 253

theorem shr_land_zero {Z L N s t : ℕ} (hL : L = 2 ^ N - 1)
    (h : Nat.shiftRight (Nat.land Z L) s = 0) (hst : s ≤ t) (htN : t < N) : Z.testBit t = false := by
  have := congrArg (fun z => Nat.testBit z (t - s)) h
  simp only [Nat.zero_testBit] at this
  change ((Z &&& L) >>> s).testBit (t - s) = false at this
  rw [Nat.testBit_shiftRight, Nat.testBit_and, hL, Nat.testBit_two_pow_sub_one,
    Nat.add_sub_cancel' hst] at this
  simpa [htN] using this

theorem testBit_rowS (P o j : ℕ) :
    (Nat.land (Nat.shiftRight P o) RS).testBit j = (decide (j < 253) && P.testBit (o + j)) := by
  change ((P >>> o) &&& RS).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, RS_eq, Nat.testBit_two_pow_sub_one, Bool.and_comm]

theorem padOK_spec {X Z : ℕ} (h : padOK X Z = true) : ∀ i < 781, ∀ j < 781,
    Z.testBit (781 * i + j) = (decide (i < 253 ∧ j < 253) && X.testBit (253 * i + j)) ∧
      Z.testBit (609961 + (781 * i + j)) =
        (decide (i < 253 ∧ j < 253) && X.testBit (64009 + (253 * i + j))) := by
  intro i hi j hj
  unfold padOK at h
  rw [andB_iff', andB_iff', andB_iff', Nat.beq_eq, Nat.beq_eq, Nat.beq_eq] at h
  obtain ⟨hrows, hz1, hz2, -⟩ := h
  by_cases hi' : i < 253
  · have hr := allBelow_spec hrows (by decide) i hi'
    rw [andB_iff', Nat.beq_eq, Nat.beq_eq] at hr
    obtain ⟨r1, r2⟩ := hr
    have b1 := congrArg (fun z => Nat.testBit z j) r1
    have b2 := congrArg (fun z => Nat.testBit z j) r2
    simp only [] at b1 b2
    rw [testBit_rowS, testBit_row _ _ _ hj] at b1 b2
    have e1 : Nat.mul 781 i = 781 * i := rfl
    have e2 : Nat.mul 253 i = 253 * i := rfl
    have e3 : Nat.add 609961 (781 * i) + j = 609961 + (781 * i + j) := by
      change 609961 + 781 * i + j = _; omega
    have e4 : Nat.add 64009 (253 * i) + j = 64009 + (253 * i + j) := by
      change 64009 + 253 * i + j = _; omega
    rw [e1, e2] at b1 b2
    rw [e3, e4] at b2
    refine ⟨?_, ?_⟩
    · rw [← b1]
      by_cases hj' : j < 253 <;> simp [hi', hj']
    · rw [← b2]
      by_cases hj' : j < 253 <;> simp [hi', hj']
  · have hlt : ¬(i < 253 ∧ j < 253) := fun h => hi' h.1
    rw [decide_eq_false hlt, Bool.false_and, Bool.false_and]
    have c2 := congrArg (fun z => Nat.testBit z (781 * i + j - 197593)) hz2
    simp only [Nat.zero_testBit] at c2
    change (Z >>> 807554).testBit (781 * i + j - 197593) = false at c2
    rw [Nat.testBit_shiftRight, show 807554 + (781 * i + j - 197593) = 609961 + (781 * i + j) by
      omega] at c2
    exact ⟨shr_land_zero (pow_sub_one_eq 609961) hz1 (by change 197593 ≤ _; omega) (by omega), c2⟩

theorem mat3_pad {X Z : ℕ} (h : padOK X Z = true) (i j : Fin 781) :
    mat3 781 609961 Z i j =
      if h : i.val < 253 ∧ j.val < 253 then mat3 253 64009 X ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0 := by
  obtain ⟨a, b⟩ := padOK_spec h i.val i.isLt j.val j.isLt
  unfold mat3
  rw [a, b]
  by_cases hij : i.val < 253 ∧ j.val < 253
  · rw [dif_pos hij, decide_eq_true hij, Bool.true_and, Bool.true_and]
  · rw [dif_neg hij, decide_eq_false hij, Bool.false_and, Bool.false_and]
    rfl

theorem add_tbl : ∀ x1 x2 y1 y2 : Bool, (x1 && x2) = false → (y1 && y2) = false →
    (((x2 || y2) ^^ ((x1 || y2) ^^ (x2 || y1))) && ((x1 || y1) ^^ ((x1 || y2) ^^ (x2 || y1)))) =
        false ∧
      bv ((x2 || y2) ^^ ((x1 || y2) ^^ (x2 || y1))) ((x1 || y1) ^^ ((x1 || y2) ^^ (x2 || y1))) =
        bv x1 x2 + bv y1 y2 := by
  decide

theorem lt_of_bits {z N : ℕ} (h : ∀ t, N ≤ t → z.testBit t = false) : z < 2 ^ N :=
  Nat.lt_pow_two_of_testBit _ h

theorem addM3_sound {d N X Y : ℕ} (hN : N = d * d) (hX : Canon3 N X) (hY : Canon3 N Y) :
    Canon3 N (addM3 N (2 ^ N - 1) X Y) ∧
      mat3 d N (addM3 N (2 ^ N - 1) X Y) = mat3 d N X + mat3 d N Y := by
  have hx1 : ∀ t, (X &&& (2 ^ N - 1)).testBit t = (decide (t < N) && X.testBit t) := fun t => lo_bit
  have hx2 : ∀ t, (X >>> N).testBit t = X.testBit (N + t) := fun t => Nat.testBit_shiftRight _
  have hy1 : ∀ t, (Y &&& (2 ^ N - 1)).testBit t = (decide (t < N) && Y.testBit t) := fun t => lo_bit
  have hy2 : ∀ t, (Y >>> N).testBit t = Y.testBit (N + t) := fun t => Nat.testBit_shiftRight _
  have hhi : ∀ {Z : ℕ}, Canon3 N Z → ∀ t, N ≤ t → Z.testBit (N + t) = false := by
    intro Z hZ t ht
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hZ.1 (Nat.pow_le_pow_right (by decide)
      (by omega)))
  have hdj : ∀ {Z : ℕ}, Canon3 N Z → ∀ t, (Z.testBit t && Z.testBit (N + t)) = false := by
    intro Z hZ t
    cases h : Z.testBit t
    · rfl
    · rw [hZ.2 t h]; rfl
  set z1 := ((X >>> N) ||| (Y >>> N)) ^^^
    (((X &&& (2 ^ N - 1)) ||| (Y >>> N)) ^^^ ((X >>> N) ||| (Y &&& (2 ^ N - 1)))) with hz1
  set z2 := ((X &&& (2 ^ N - 1)) ||| (Y &&& (2 ^ N - 1))) ^^^
    (((X &&& (2 ^ N - 1)) ||| (Y >>> N)) ^^^ ((X >>> N) ||| (Y &&& (2 ^ N - 1)))) with hz2
  have e : addM3 N (2 ^ N - 1) X Y = z1 + (z2 <<< N) := rfl
  have hb1 : ∀ t, z1.testBit t = ((X.testBit (N + t) || Y.testBit (N + t)) ^^
      ((decide (t < N) && X.testBit t || Y.testBit (N + t)) ^^
        (X.testBit (N + t) || decide (t < N) && Y.testBit t))) := by
    intro t
    simp only [hz1, Nat.testBit_xor, Nat.testBit_or, hx1, hx2, hy1, hy2]
  have hb2 : ∀ t, z2.testBit t = ((decide (t < N) && X.testBit t || decide (t < N) && Y.testBit t) ^^
      ((decide (t < N) && X.testBit t || Y.testBit (N + t)) ^^
        (X.testBit (N + t) || decide (t < N) && Y.testBit t))) := by
    intro t
    simp only [hz2, Nat.testBit_xor, Nat.testBit_or, hx1, hx2, hy1, hy2]
  have hz1N : ∀ t, N ≤ t → z1.testBit t = false := by
    intro t ht
    rw [hb1, hhi hX t ht, hhi hY t ht, decide_eq_false (by omega)]
    simp
  have hz2N : ∀ t, N ≤ t → z2.testBit t = false := by
    intro t ht
    rw [hb2, hhi hX t ht, hhi hY t ht, decide_eq_false (by omega)]
    simp
  have hsum : ∀ t, (z1 + (z2 <<< N)).testBit t =
      (decide (t < N) && z1.testBit t || decide (N ≤ t) && z2.testBit (t - N)) := by
    intro t
    rw [testBit_add_disj (fun p hp => by
      rw [Nat.testBit_shiftLeft] at hp
      have := hz1N p (by simp at hp; omega)
      rw [this] at hp
      exact absurd hp.1 (by simp))]
    rw [Nat.testBit_shiftLeft]
    by_cases ht : t < N
    · simp [ht, show ¬(N ≤ t) by omega]
    · simp [ht, show N ≤ t by omega, hz1N t (by omega)]
  have hlow : ∀ t < N, (z1.testBit t && z2.testBit t) = false ∧
      bv (z1.testBit t) (z2.testBit t) = bv (X.testBit t) (X.testBit (N + t)) +
        bv (Y.testBit t) (Y.testBit (N + t)) := by
    intro t ht
    rw [hb1, hb2, decide_eq_true ht, Bool.true_and, Bool.true_and]
    exact add_tbl _ _ _ _ (hdj hX t) (hdj hY t)
  rw [e]
  refine ⟨⟨?_, fun t ht => ?_⟩, ?_⟩
  · have : z1 + (z2 <<< N) < 2 ^ (N + N) := by
      apply Nat.lt_pow_two_of_testBit
      intro t ht
      rw [hsum, decide_eq_false (by omega), Bool.false_and, Bool.false_or,
        decide_eq_true (by omega), Bool.true_and, hz2N _ (by omega)]
    exact this
  · rw [hsum] at ht ⊢
    by_cases htN : t < N
    · rw [decide_eq_true htN, Bool.true_and, decide_eq_false (by omega), Bool.false_and,
        Bool.or_false] at ht
      rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, decide_eq_true (by omega),
        Bool.true_and, Nat.add_sub_cancel_left]
      have := (hlow t htN).1
      rw [ht] at this
      simpa using this
    · rw [decide_eq_false (by omega), Bool.false_and, Bool.false_or, decide_eq_true (by omega),
        Bool.true_and, hz2N _ (by omega)]
  · funext i j
    have hp : d * i.val + j.val < N := hN ▸ idx_lt3 i.isLt j.isLt
    change bv _ _ = bv _ _ + bv _ _
    rw [hsum, hsum, decide_eq_true hp, Bool.true_and, decide_eq_false (by omega), Bool.false_and,
      Bool.or_false, decide_eq_false (by omega), Bool.false_and, Bool.false_or,
      decide_eq_true (by omega), Bool.true_and, Nat.add_sub_cancel_left]
    exact (hlow _ hp).2

end CFSG.KC.Fi24ExtS

end
