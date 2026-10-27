module

public import Certificates.Data.Kernel.Co2JRank
public import CFSG.Certificates.Kernel.Co2Cls.Sound

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2JRank

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.TabMatGrp
  CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native

section F2

variable {M : Type*} [Monoid M]

@[expose] def xP (f : ℕ → M) : ℕ → ℕ → M
  | 0, _ => 1
  | k + 1, u => (if u.testBit k then f k else 1) * xP f k u

theorem xP_zero (f : ℕ → M) : ∀ k, xP f k 0 = 1
  | 0 => rfl
  | k + 1 => by rw [xP, Nat.zero_testBit, if_neg Bool.false_ne_true, one_mul, xP_zero f k]

theorem xP_congr (f : ℕ → M) : ∀ k {u w : ℕ}, (∀ i < k, u.testBit i = w.testBit i) →
    xP f k u = xP f k w
  | 0, _, _, _ => rfl
  | k + 1, _, _, h => by
    rw [xP, xP, h k (by omega), xP_congr f k fun i hi => h i (by omega)]

theorem xP_two_pow (f : ℕ → M) : ∀ k j, j < k → xP f k (2 ^ j) = f j
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, j, h => by
    rw [xP]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [Nat.testBit_two_pow_of_ne (by omega), if_neg Bool.false_ne_true, one_mul,
        xP_two_pow f k j h]
    · rw [Nat.testBit_two_pow_self, if_pos rfl,
        xP_congr f j (w := 0) fun i hi => by
          rw [Nat.testBit_two_pow_of_ne (by omega), Nat.zero_testBit],
        xP_zero, mul_one]

theorem xP_commute (f : ℕ → M) {a : M} : ∀ k u, (∀ i < k, Commute (f i) a) →
    Commute (xP f k u) a
  | 0, _, _ => Commute.one_left a
  | k + 1, u, h => by
    rw [xP]
    refine Commute.mul_left ?_ (xP_commute f k u fun i hi => h i (by omega))
    split_ifs
    · exact h k (by omega)
    · exact Commute.one_left a

theorem xP_mem (f : ℕ → M) {S : Submonoid M} : ∀ k u, (∀ i < k, f i ∈ S) → xP f k u ∈ S
  | 0, _, _ => S.one_mem
  | k + 1, u, h => by
    rw [xP]
    refine S.mul_mem ?_ (xP_mem f k u fun i hi => h i (by omega))
    split_ifs
    · exact h k (by omega)
    · exact S.one_mem

variable {f : ℕ → M} {k : ℕ}

theorem xP_xor (hc : ∀ i < k, ∀ j < k, Commute (f i) (f j)) (hs : ∀ i < k, f i * f i = 1)
    (s t : ℕ) : xP f k (s ^^^ t) = xP f k s * xP f k t := by
  induction k with
  | zero => exact (mul_one 1).symm
  | succ k ih =>
    have ih' := ih (fun i hi j hj => hc i (by omega) j (by omega)) fun i hi => hs i (by omega)
    have hcs : Commute (f k) (xP f k s) :=
      (xP_commute f k s fun i hi => hc i (by omega) k (by omega)).symm
    rw [xP, xP, xP, Nat.testBit_xor, ih']
    cases s.testBit k <;> cases t.testBit k
    · simp only [Bool.xor_false, Bool.false_eq_true, if_false, one_mul]
    · simp only [Bool.false_xor, if_true, Bool.false_eq_true, if_false, one_mul]
      rw [← mul_assoc, ← mul_assoc, hcs.eq]
    · simp only [Bool.xor_false, if_true, Bool.false_eq_true, if_false, one_mul]
      rw [mul_assoc]
    · simp only [Bool.xor_self, Bool.false_eq_true, if_false, if_true, one_mul]
      rw [← mul_assoc, mul_assoc (f k) (xP f k s) (f k), ← hcs.eq, ← mul_assoc,
        hs k (by omega), one_mul]

theorem mem_closure_iff (hc : ∀ i < k, ∀ j < k, Commute (f i) (f j))
    (hs : ∀ i < k, f i * f i = 1) {x : M} :
    x ∈ Submonoid.closure (Set.range fun j : Fin k => f j) ↔ ∃ u < 2 ^ k, xP f k u = x := by
  constructor
  · intro hx
    induction hx using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨2 ^ j.val, Nat.pow_lt_pow_right (by norm_num) j.isLt, xP_two_pow f k j j.isLt⟩
    | one => exact ⟨0, Nat.two_pow_pos k, xP_zero f k⟩
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs2, rfl⟩ := hx
      obtain ⟨t, ht2, rfl⟩ := hy
      exact ⟨s ^^^ t, Nat.xor_lt_two_pow hs2 ht2, xP_xor hc hs s t⟩
  · rintro ⟨u, -, rfl⟩
    exact xP_mem f k u fun i hi => Submonoid.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem xP_injOn (hc : ∀ i < k, ∀ j < k, Commute (f i) (f j)) (hs : ∀ i < k, f i * f i = 1)
    (hne : ∀ u, 0 < u → u < 2 ^ k → xP f k u ≠ 1) {s t : ℕ} (hs2 : s < 2 ^ k) (ht2 : t < 2 ^ k)
    (e : xP f k s = xP f k t) : s = t := by
  by_contra hst
  have h0 : 0 < s ^^^ t := by
    refine Nat.pos_of_ne_zero fun h => hst ?_
    have := congrArg (· ^^^ t) h
    simpa [Nat.xor_assoc] using this
  refine hne _ h0 (Nat.xor_lt_two_pow hs2 ht2) ?_
  rw [xP_xor hc hs, e, ← xP_xor hc hs, Nat.xor_self, xP_zero]

theorem card_closure (hc : ∀ i < k, ∀ j < k, Commute (f i) (f j)) (hs : ∀ i < k, f i * f i = 1)
    (hne : ∀ u, 0 < u → u < 2 ^ k → xP f k u ≠ 1) :
    Nat.card (Submonoid.closure (Set.range fun j : Fin k => f j)) = 2 ^ k := by
  let F : Fin (2 ^ k) → Submonoid.closure (Set.range fun j : Fin k => f j) := fun u =>
    ⟨xP f k u, (mem_closure_iff hc hs).2 ⟨u, u.isLt, rfl⟩⟩
  have hF : Function.Bijective F := by
    refine ⟨fun a b e => Fin.ext (xP_injOn hc hs hne a.isLt b.isLt (congrArg Subtype.val e)),
      fun x => ?_⟩
    obtain ⟨u, hu, e⟩ := (mem_closure_iff hc hs).1 x.2
    exact ⟨⟨u, hu⟩, Subtype.ext e⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

end F2

@[expose] noncomputable def xM (G : Nat → Nat) : ℕ → ℕ → Matrix (Fin 22) (Fin 22) (ZMod 2) :=
  xP fun i => MatP 22 (G i)

theorem testBit_top {u k : ℕ} (h : u < 2 ^ (k + 1)) : u.testBit k = decide (2 ^ k ≤ u) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h2 : u / 2 ^ k < 2 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
    rw [pow_succ] at h
    rw [Nat.mul_comm]
    exact h
  rw [Nat.mod_eq_of_lt h2]
  have e : u / 2 ^ k = 1 ↔ 2 ^ k ≤ u := by
    constructor
    · intro e
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).1 (le_of_eq e.symm)
      omega
    · intro e
      have := (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).2 (by omega : 1 * 2 ^ k ≤ u)
      omega
  exact decide_eq_decide.2 e

theorem walkJ_sound {G : Nat → Nat} {pt : Nat → Nat → Bool} : ∀ k X v, walkJ G pt k X v = true →
    ∀ u < 2 ^ k, ∃ Y, MatP 22 Y = MatP 22 X * xM G k u ∧ pt Y (v + u) = true := by
  intro k
  induction k with
  | zero =>
    intro X v h u hu
    have hu0 : u = 0 := by omega
    subst hu0
    exact ⟨X, (mul_one _).symm, h⟩
  | succ k ih =>
    intro X v h u hu
    have h' : andK (walkJ G pt k X v)
        (letB (mulV X (G k)) fun X' => walkJ G pt k X' (Nat.add v (Nat.shiftLeft 1 k))) = true :=
      h
    rw [andK_eq, Bool.and_eq_true, letB_eq] at h'
    obtain ⟨h1, h2⟩ := h'
    have ht := testBit_top hu
    by_cases hb : 2 ^ k ≤ u
    · obtain ⟨u', rfl⟩ := Nat.exists_eq_add_of_le hb
      have hu' : u' < 2 ^ k := by
        rw [pow_succ] at hu
        omega
      obtain ⟨Y, hY, hp⟩ := ih _ _ h2 u' hu'
      refine ⟨Y, ?_, ?_⟩
      · rw [hY, MatP_mulV, xM, xP, ht, decide_eq_true hb, if_pos rfl, mul_assoc]
        congr 2
        exact xP_congr _ k fun i hi => (Nat.testBit_two_pow_add_gt hi u').symm
      · have e : Nat.add v (Nat.shiftLeft 1 k) + u' = v + (2 ^ k + u') := by
          change v + 1 <<< k + u' = _
          rw [Nat.shiftLeft_eq, one_mul]
          omega
        rwa [e] at hp
    · have hu' : u < 2 ^ k := by omega
      obtain ⟨Y, hY, hp⟩ := ih _ _ h1 u hu'
      refine ⟨Y, ?_, hp⟩
      rw [hY, xM, xP, ht, decide_eq_false hb, if_neg Bool.false_ne_true, one_mul]

theorem kAt_le (T v : Nat) : kAt T v ≤ 15 := by
  unfold kAt
  exact Nat.and_le_right

theorem MatP_xorI (X : Nat) : MatP 22 (Nat.xor X IDP) = MatP 22 X + 1 := by
  rw [← MatP_IDP]
  exact MatP_xor X IDP

theorem pt1_sound {CR : Nat → Nat} {K1 X v : Nat} (h : pt1 CR K1 X v = true) :
    (MatP 22 X + 1).rank = kAt K1 v := by
  have := rankL_sound (by have := kAt_le K1 v; omega) h
  rwa [MatP_xorI] at this

theorem ptJ_sound {CR : Nat → Nat} {K1 K3 R vr X v : Nat} (h : ptJ CR K1 K3 R vr X v = true) :
    (MatP 22 X + 1).rank = kAt K1 v ∧ (kAt K1 v = 10 → kAt K1 (v ^^^ vr) = 10 →
      ((MatP 22 R + 1) * (MatP 22 X + 1)).rank = kAt K3 v) := by
  unfold ptJ at h
  rw [andK_eq, Bool.and_eq_true, implK_eq] at h
  refine ⟨pt1_sound h.1, fun ha hb => ?_⟩
  have hc : andK (Nat.beq (kAt K1 v) 10) (Nat.beq (kAt K1 (Nat.xor v vr)) 10) = true := by
    have hb' : kAt K1 (Nat.xor v vr) = 10 := hb
    rw [andK_eq, ha, hb']
    rfl
  rw [hc, if_pos rfl] at h
  have := rankL_sound (by have := kAt_le K3 v; omega) h.2
  rwa [MatP_mulV, MatP_xorI, MatP_xorI] at this

theorem walk1_ranks {G CR : Nat → Nat} {K1 n : Nat} (h : walkJ G (pt1 CR K1) n IDP 0 = true) :
    ∀ u < 2 ^ n, (xM G n u + 1).rank = kAt K1 u := by
  intro u hu
  obtain ⟨Y, hY, hp⟩ := walkJ_sound n IDP 0 h u hu
  rw [MatP_IDP, one_mul] at hY
  rw [Nat.zero_add] at hp
  rw [← hY]
  exact pt1_sound hp

theorem allBelow_spec {m hi : Nat} {f : Nat → Bool} (h : allBelow m hi f = true) :
    ∀ i < m, i < 64 * hi → f i = true := by
  have inner : ∀ (hh : Nat) (n : Nat), Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) n = true →
      ∀ l < n, Nat.add (Nat.shiftLeft hh 6) l < m → f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro hh n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl hlm
      have hn' := hn
      change Bool.rec (motive := fun _ => Bool) false _ _ = true at hn'
      rw [bAnd_eq, Bool.and_eq_true] at hn'
      obtain ⟨h1, h2⟩ := hn'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
      · exact ih h2 l hl hlm
      · have hb : Nat.blt (Nat.add (Nat.shiftLeft hh 6) l) m = true := Nat.blt_eq.mpr hlm
        change Bool.rec (motive := fun _ => Bool) true _ (Nat.blt _ m) = true at h1
        rw [hb] at h1
        exact h1
  have outer : ∀ n, Nat.rec (motive := fun _ => Bool) true (fun hh ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
        bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft hh 6) l), ih2)) 64,
        ih)) n = true → ∀ hh < n, ∀ l < 64, Nat.add (Nat.shiftLeft hh 6) l < m →
          f (Nat.add (Nat.shiftLeft hh 6) l) = true := by
    intro n
    induction n with
    | zero => intro _ hh hhh; omega
    | succ n ih =>
      intro hn hh hhh l hl hlm
      have hn' := hn
      change Bool.rec (motive := fun _ => Bool) false _ _ = true at hn'
      rw [bAnd_eq, Bool.and_eq_true] at hn'
      obtain ⟨h1, h2⟩ := hn'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hhh with hhh | rfl
      · exact ih h2 hh hhh l hl hlm
      · exact inner _ 64 h1 l hl hlm
  intro i him hih
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have := outer hi h (i / 64) (by omega) (i % 64) (Nat.mod_lt _ (by norm_num)) (by rw [e]; exact him)
  rwa [e] at this

theorem nzK_sound {K1 N hi : Nat} (h : nzK K1 N hi = true) (hN : N ≤ 64 * hi) :
    ∀ v, 0 < v → v < N → 0 < kAt K1 v := by
  intro v hv hvN
  have e := allBelow_spec h v hvN (by omega)
  rw [implK_eq, if_pos (blt_iff.2 hv)] at e
  exact blt_iff.1 e

theorem ne_one_of_rank {A : Matrix (Fin 22) (Fin 22) (ZMod 2)} (h : 0 < (A + 1).rank) : A ≠ 1 := by
  rintro rfl
  have e : (1 + 1 : Matrix (Fin 22) (Fin 22) (ZMod 2)) = 0 := by
    ext i j
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  rw [e, Matrix.rank_zero] at h
  exact Nat.lt_irrefl 0 h

theorem xM_ne_one {G CR : Nat → Nat} {K1 n N hi : Nat} (h : walkJ G (pt1 CR K1) n IDP 0 = true)
    (hz : nzK K1 N hi = true) (hN : N ≤ 64 * hi) (hn : 2 ^ n ≤ N) :
    ∀ u, 0 < u → u < 2 ^ n → xM G n u ≠ 1 := by
  intro u hu hun
  refine ne_one_of_rank ?_
  rw [walk1_ranks h u hun]
  exact nzK_sound hz hN u hu (by omega)

theorem card_genJ {G CR : Nat → Nat} {K1 n N hi : Nat}
    (hc : ∀ i < n, ∀ j < n, Commute (MatP 22 (G i)) (MatP 22 (G j)))
    (hs : ∀ i < n, MatP 22 (G i) * MatP 22 (G i) = 1)
    (h : walkJ G (pt1 CR K1) n IDP 0 = true) (hz : nzK K1 N hi = true) (hN : N ≤ 64 * hi)
    (hn : 2 ^ n ≤ N) :
    Nat.card (genMonN n G) = 2 ^ n := by
  have hne : ∀ u, 0 < u → u < 2 ^ n → xP (fun i => MatP 22 (G i)) n u ≠ 1 :=
    xM_ne_one h hz hN hn
  unfold genMonN
  exact card_closure (f := fun i => MatP 22 (G i)) hc hs hne

theorem mem_genJ {G : Nat → Nat} {n : Nat}
    (hc : ∀ i < n, ∀ j < n, Commute (MatP 22 (G i)) (MatP 22 (G j)))
    (hs : ∀ i < n, MatP 22 (G i) * MatP 22 (G i) = 1) {x : Matrix (Fin 22) (Fin 22) (ZMod 2)} :
    x ∈ genMonN n G ↔ ∃ u < 2 ^ n, xM G n u = x := by
  unfold genMonN xM
  refine mem_closure_iff (f := fun i => MatP 22 (G i)) ?_ ?_
  · exact hc
  · exact hs

end CFSG.KC.Co2JRank

end
