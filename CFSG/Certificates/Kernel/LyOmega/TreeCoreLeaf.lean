module

public import Certificates.Data.Kernel.LyOmega.Tree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.LyOm.TreeCore

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop

@[expose] noncomputable def recL (PT : ℕ → ℕ) (b r : ℕ) : ℕ :=
  fldW (PT b) (Nat.mul (nat_lit 21) r) (nat_lit 21)

@[expose] noncomputable def labL (PT : ℕ → ℕ) (b r : ℕ) : ℕ :=
  Nat.shiftRight (recL PT b r) (nat_lit 20)

@[expose] noncomputable def parL (PT : ℕ → ℕ) (b r : ℕ) : ℕ :=
  Nat.land (recL PT b r) (nat_lit 1048575)

@[expose] noncomputable def cntL (PT : ℕ → ℕ) (n b s r : ℕ) : ℕ :=
  ((Finset.range r).filter (fun r' => isChild n (64 * b + r') = true ∧ labL PT b r' = s)).card

@[expose] def ChildOK (C : Consts) (PT : ℕ → ℕ) (n b Y0 Y1 XC r : ℕ) : Prop :=
  parL PT b r < 64 * b + r ∧ Nat.land (rows7 XC r) C.MASK7 = C.ONE7 ∧
    (labL PT b r = 0 →
      mul7 C (rows7 Y0 (cntL PT n b 0 r)) (rows7 XC r) = rows7 Y0 (cntL PT n b 0 r)) ∧
    (labL PT b r = 1 →
      mul7 C (rows7 Y1 (cntL PT n b 1 r)) (rows7 XC r) = rows7 Y1 (cntL PT n b 1 r))

private theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

private theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by cases v <;> rfl

private theorem bAnd_iff {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

private theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := by rw [Nat.beq_eq]

private theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

private theorem fldW_eq (r o w : ℕ) : fldW r o w = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (1 <<< w - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem lo_eq (b r : ℕ) : Nat.add (Nat.shiftLeft b (nat_lit 6)) r = 64 * b + r := by
  change b <<< 6 + r = _
  rw [Nat.shiftLeft_eq]
  omega

theorem labL_lt (PT : ℕ → ℕ) (b r : ℕ) : labL PT b r < 2 := by
  unfold labL recL
  change fldW (PT b) (21 * r) 21 >>> 20 < 2
  rw [fldW_eq, Nat.shiftRight_eq_div_pow]
  have := Nat.mod_lt (PT b / 2 ^ (21 * r)) (Nat.two_pow_pos 21)
  omega

theorem getRec_lt (KX : ℕ → ℕ) (j : ℕ) : getRec KX 2331 j < 2 ^ 2331 := by
  unfold getRec
  rw [strictN_eq, fldW_eq]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem cnt_succ (PT : ℕ → ℕ) (n b s r : ℕ) :
    cntL PT n b s (r + 1) = cntL PT n b s r +
      if isChild n (64 * b + r) = true ∧ labL PT b r = s then 1 else 0 := by
  unfold cntL
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · rfl

private theorem cnt_mono (PT : ℕ → ℕ) (n b s : ℕ) {r r' : ℕ} (h : r ≤ r') :
    cntL PT n b s r ≤ cntL PT n b s r' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem cntL_le (PT : ℕ → ℕ) (n b s r : ℕ) : cntL PT n b s r ≤ r :=
  (Finset.card_filter_le _ _).trans (by simp)

private def LcStep (C : Consts) (PT : ℕ → ℕ) (n b Y0 Y1 XC : ℕ)
    (step : ℕ → (ℕ → ℕ → Bool) → ℕ → ℕ → Bool) : Prop :=
  ∀ k ih c0 c1, step k ih c0 c1 =
      bIf(isChild n (64 * b + (63 - k)),
        bAnd(Nat.blt (parL PT b (63 - k)) (64 * b + (63 - k)),
        bAnd(Nat.beq (Nat.land (rows7 XC (63 - k)) C.MASK7) C.ONE7,
          bIf(Nat.beq (labL PT b (63 - k)) 0,
            bAnd(Nat.beq (mul7 C (rows7 Y0 c0) (rows7 XC (63 - k))) (rows7 Y0 c0), ih (c0 + 1) c1),
            bAnd(Nat.beq (mul7 C (rows7 Y1 c1) (rows7 XC (63 - k))) (rows7 Y1 c1),
              ih c0 (c1 + 1))))),
        ih c0 c1)

private theorem lc_walk (C : Consts) (PT : ℕ → ℕ) (n b Y0 Y1 XC : ℕ)
    (step : ℕ → (ℕ → ℕ → Bool) → ℕ → ℕ → Bool) (hs : LcStep C PT n b Y0 Y1 XC step) :
    ∀ m, m ≤ 64 →
    ∀ c0 c1, c0 = cntL PT n b 0 (64 - m) → c1 = cntL PT n b 1 (64 - m) →
    Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true) step m c0 c1 = true →
    ∀ r, 64 - m ≤ r → r < 64 → isChild n (64 * b + r) = true → ChildOK C PT n b Y0 Y1 XC r
  | 0, _, _, _, _, _, _, r, h1, h2, _ => absurd h2 (by omega)
  | m + 1, hm, c0, c1, hc0, hc1, h, r, h1, h2, hch => by
    have ih := lc_walk C PT n b Y0 Y1 XC step hs m (by omega)
    have hr0 : 64 - (m + 1) = 63 - m := by omega
    have hr1 : 64 - m = 63 - m + 1 := by omega
    rw [hr0] at hc0 hc1
    rw [hr1] at ih
    change step m (Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true) step m) c0 c1 = true
      at h
    rw [hs] at h
    by_cases hc : isChild n (64 * b + (63 - m)) = true
    · rw [hc] at h
      obtain ⟨hp, hmask⟩ := bAnd_iff.1 h
      obtain ⟨hmask, hrest⟩ := bAnd_iff.1 hmask
      by_cases hl : labL PT b (63 - m) = 0
      · have hb : Nat.beq (labL PT b (63 - m)) 0 = true := beq_iff.2 hl
        rw [hb] at hrest
        obtain ⟨hmul, hnext⟩ := bAnd_iff.1 hrest
        rcases Nat.eq_or_lt_of_le (show 63 - m ≤ r by omega) with hr | hr
        · subst hr
          refine ⟨blt_iff.1 hp, beq_iff.1 hmask, fun _ => ?_, fun h1 => absurd (hl ▸ h1) (by norm_num)⟩
          rw [← hc0]
          exact beq_iff.1 hmul
        · refine ih (c0 + 1) c1 ?_ ?_ hnext r (by omega) h2 hch
          · rw [cnt_succ, if_pos ⟨hc, hl⟩, hc0]
          · rw [cnt_succ, if_neg (fun h => by rw [hl] at h; exact absurd h.2 (by norm_num)), hc1,
              Nat.add_zero]
      · have hl1 : labL PT b (63 - m) = 1 := by have := labL_lt PT b (63 - m); omega
        have hb : Nat.beq (labL PT b (63 - m)) 0 = false :=
          Bool.eq_false_iff.2 fun hh => hl (beq_iff.1 hh)
        rw [hb] at hrest
        obtain ⟨hmul, hnext⟩ := bAnd_iff.1 hrest
        rcases Nat.eq_or_lt_of_le (show 63 - m ≤ r by omega) with hr | hr
        · subst hr
          refine ⟨blt_iff.1 hp, beq_iff.1 hmask, fun h0 => absurd h0 hl, fun _ => ?_⟩
          rw [← hc1]
          exact beq_iff.1 hmul
        · refine ih c0 (c1 + 1) ?_ ?_ hnext r (by omega) h2 hch
          · rw [cnt_succ, if_neg (fun h => hl h.2), hc0, Nat.add_zero]
          · rw [cnt_succ, if_pos ⟨hc, hl1⟩, hc1]
    · have hcf : isChild n (64 * b + (63 - m)) = false := by simpa using hc
      rw [hcf] at h
      rcases Nat.eq_or_lt_of_le (show 63 - m ≤ r by omega) with hr | hr
      · subst hr
        exact absurd hch hc
      · refine ih c0 c1 ?_ ?_ h r (by omega) h2 hch
        · rw [cnt_succ, if_neg (fun h => hc h.1), hc0, Nat.add_zero]
        · rw [cnt_succ, if_neg (fun h => hc h.1), hc1, Nat.add_zero]

theorem leafCmp_walk {C : Consts} {PT : ℕ → ℕ} {n b Y0 Y1 XC : ℕ}
    (h : leafCmp C PT n b Y0 Y1 XC = true) :
    ∀ r < 64, isChild n (64 * b + r) = true → ChildOK C PT n b Y0 Y1 XC r := by
  intro r hr hc
  unfold leafCmp at h
  rw [letB_eq, letB_eq] at h
  generalize hN : (nat_lit 64) = N at h
  have hN' : N = 64 := hN.symm
  refine lc_walk C PT n b Y0 Y1 XC _ (fun k ih c0 c1 => ?_) N (by omega) (nat_lit 0) (nat_lit 0)
    (by rw [hN']; simp [cntL]) (by rw [hN']; simp [cntL]) h r (by omega) hr hc
  simp only [letB_eq]
  rw [lo_eq]
  rfl

private def GStep (KX PT : ℕ → ℕ) (n b s : ℕ) (step : ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ) : Prop :=
  ∀ k ih acc cnt, step k ih acc cnt =
      if isChild n (64 * b + (63 - k)) = true ∧ labL PT b (63 - k) = s then
        ih (Nat.lor acc (Nat.shiftLeft (getRec KX 2331 (parL PT b (63 - k))) (Nat.mul 2331 cnt)))
          (cnt + 1)
      else ih acc cnt

private theorem or_eq {a K W c : ℕ} (ha : a < 2 ^ (W * c)) :
    Nat.lor a (Nat.shiftLeft K (Nat.mul W c)) = a + K * 2 ^ (W * c) := by
  change a ||| K <<< (W * c) = _
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt ha, Nat.shiftLeft_eq, Nat.add_comm]

private theorem blk_lo {a K W c c' : ℕ} (ha : a < 2 ^ (W * c)) (hc : c' < c) :
    (a + K * 2 ^ (W * c)) / 2 ^ (W * c') % 2 ^ W = a / 2 ^ (W * c') % 2 ^ W := by
  have e : K * 2 ^ (W * c) = 2 ^ (W * c') * (K * 2 ^ (W * (c - c'))) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (W * c')), Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    rw [← Nat.mul_add]
    congr 1
    omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have e2 : K * 2 ^ (W * (c - c')) = 2 ^ W * (K * 2 ^ (W * (c - c' - 1))) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ W), Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    have : c - c' = (c - c' - 1) + 1 := by omega
    rw [this, Nat.mul_add, Nat.mul_one, Nat.add_comm]
    simp
  rw [e2, Nat.add_mul_mod_self_left]

private theorem blk_hi {a K W c : ℕ} (ha : a < 2 ^ (W * c)) (hK : K < 2 ^ W) :
    (a + K * 2 ^ (W * c)) / 2 ^ (W * c) % 2 ^ W = K := by
  rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt ha, Nat.zero_add,
    Nat.mod_eq_of_lt hK]

private def GInv (KX PT : ℕ → ℕ) (n b s A r : ℕ) : Prop :=
  A < 2 ^ (2331 * cntL PT n b s r) ∧
    (∀ r' < r, isChild n (64 * b + r') = true → labL PT b r' = s →
      A / 2 ^ (2331 * cntL PT n b s r') % 2 ^ 2331 = getRec KX 2331 (parL PT b r')) ∧
    (∀ c < cntL PT n b s r, ∃ j < n, A / 2 ^ (2331 * c) % 2 ^ 2331 = getRec KX 2331 j)

private theorem g_walk (KX PT : ℕ → ℕ) (n b s : ℕ)
    (hpar : ∀ r < 64, isChild n (64 * b + r) = true → parL PT b r < n)
    (step : ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ) (hs : GStep KX PT n b s step) : ∀ m, m ≤ 64 →
    ∀ A, GInv KX PT n b s A (64 - m) →
      GInv KX PT n b s (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun acc _ => acc) step m A
        (cntL PT n b s (64 - m))) 64
  | 0, _, A, h => h
  | m + 1, hm, A, h => by
    have ih := g_walk KX PT n b s hpar step hs m (by omega)
    have hr0 : 64 - (m + 1) = 63 - m := by omega
    have hr1 : 64 - m = 63 - m + 1 := by omega
    rw [hr0] at h ⊢
    rw [hr1] at ih
    change GInv KX PT n b s (step m (Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun acc _ => acc) step m)
      A (cntL PT n b s (63 - m))) 64
    rw [hs]
    obtain ⟨hA, hblk, hex⟩ := h
    split_ifs with hcs
    · have hcnt : cntL PT n b s (63 - m + 1) = cntL PT n b s (63 - m) + 1 := by
        rw [cnt_succ, if_pos hcs]
      rw [or_eq hA, ← hcnt]
      apply ih
      have hK := getRec_lt KX (parL PT b (63 - m))
      refine ⟨?_, fun r' hr' hc hl => ?_, fun c hc => ?_⟩
      · rw [hcnt, Nat.mul_add, Nat.mul_one, Nat.pow_add]
        calc A + getRec KX 2331 (parL PT b (63 - m)) * 2 ^ (2331 * cntL PT n b s (63 - m))
            < 2 ^ (2331 * cntL PT n b s (63 - m)) +
              getRec KX 2331 (parL PT b (63 - m)) * 2 ^ (2331 * cntL PT n b s (63 - m)) := by
              omega
          _ = (getRec KX 2331 (parL PT b (63 - m)) + 1) * 2 ^ (2331 * cntL PT n b s (63 - m)) := by
              ring
          _ ≤ 2 ^ 2331 * 2 ^ (2331 * cntL PT n b s (63 - m)) :=
              Nat.mul_le_mul_right _ hK
          _ = _ := Nat.mul_comm _ _
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | hr'
        · have hlt : cntL PT n b s r' < cntL PT n b s (63 - m) := by
            have h1 : cntL PT n b s (r' + 1) = cntL PT n b s r' + 1 := by
              rw [cnt_succ, if_pos ⟨hc, hl⟩]
            have := cnt_mono PT n b s (show r' + 1 ≤ 63 - m by omega)
            omega
          rw [blk_lo hA hlt]
          exact hblk r' hr' hc hl
        · subst hr'
          exact blk_hi hA hK
      · rw [hcnt] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | hc
        · rw [blk_lo hA hc]
          exact hex c hc
        · subst hc
          exact ⟨_, hpar _ (by omega) hcs.1, blk_hi hA hK⟩
    · have hcnt : cntL PT n b s (63 - m + 1) = cntL PT n b s (63 - m) := by
        rw [cnt_succ, if_neg hcs, Nat.add_zero]
      rw [← hcnt]
      apply ih
      refine ⟨hcnt ▸ hA, fun r' hr' hc hl => ?_, fun c hc => hex c (hcnt ▸ hc)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | hr'
      · exact hblk r' hr' hc hl
      · subst hr'
        exact absurd ⟨hc, hl⟩ hcs

private def GFin (KX PT : ℕ → ℕ) (n b s A : ℕ) : Prop := GInv KX PT n b s A 64

private theorem gather_core {KX PT : ℕ → ℕ} {n b s : ℕ}
    (hpar : ∀ r < 64, isChild n (64 * b + r) = true → parL PT b r < n)
    (step : ℕ → (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ) (hs : GStep KX PT n b s step) {N A : ℕ} (hN : N = 64)
    (h : Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun acc _ => acc) step N (nat_lit 0) (nat_lit 0) = A) :
    GFin KX PT n b s A := by
  subst h
  have h0 : cntL PT n b s (64 - N) = 0 := by rw [hN]; simp [cntL]
  have key := g_walk KX PT n b s hpar step hs N (by omega) (nat_lit 0)
    ⟨by rw [h0]; norm_num, fun r' hr' => absurd hr' (by omega), fun c hc => absurd hc (by rw [h0]; omega)⟩
  rw [h0] at key
  exact key

theorem gather_spec {KX PT : ℕ → ℕ} {n b : ℕ} (s : ℕ)
    (hpar : ∀ r < 64, isChild n (64 * b + r) = true → parL PT b r < n) :
    gather KX PT n b s < 2 ^ (2331 * cntL PT n b s 64) ∧
      (∀ r < 64, isChild n (64 * b + r) = true → labL PT b r = s →
        gather KX PT n b s / 2 ^ (2331 * cntL PT n b s r) % 2 ^ 2331 =
          getRec KX 2331 (parL PT b r)) ∧
      (∀ c < cntL PT n b s 64, ∃ j < n,
        gather KX PT n b s / 2 ^ (2331 * c) % 2 ^ 2331 = getRec KX 2331 j) := by
  suffices H : GFin KX PT n b s (gather KX PT n b s) from H
  obtain ⟨A, hA⟩ : ∃ A, gather KX PT n b s = A := ⟨_, rfl⟩
  rw [hA]
  unfold gather at hA
  rw [strictN_eq] at hA
  generalize hN : (nat_lit 64) = N at hA
  refine gather_core hpar _ (fun k ih acc cnt => ?_) hN.symm hA
  simp only [strictN_eq]
  change Bool.rec (motive := fun _ => ℕ) _ _ (Bool.rec (motive := fun _ => Bool) false
    (Nat.beq (labL PT b (63 - k)) s) (isChild n (Nat.add (Nat.shiftLeft b (nat_lit 6)) (63 - k)))) = _
  rw [lo_eq]
  by_cases hc : isChild n (64 * b + (63 - k)) = true
  · by_cases hl : labL PT b (63 - k) = s
    · rw [if_pos ⟨hc, hl⟩, hc, beq_iff.2 hl]
      rfl
    · have hb : Nat.beq (labL PT b (63 - k)) s = false :=
        Bool.eq_false_iff.2 fun hh => hl (beq_iff.1 hh)
      rw [if_neg (fun h => hl h.2), hc, hb]
  · have hcf : isChild n (64 * b + (63 - k)) = false := by simpa using hc
    rw [if_neg (fun h => hc h.1), hcf]

end CFSG.KS.LyOm.TreeCore

end
