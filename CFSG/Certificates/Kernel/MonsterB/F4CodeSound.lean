
module

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408PointsInputs
import all CFSG.Fischer.F4
public import Certificates.Data.Kernel.MonsterB.Orb14

public section

namespace CFSG.KC.Orb14

open CFSG.Fischer CFSG.Monster.B.TwoA.Unitary CFSG.KLie.CT CFSG.KC.U6Orb
open CFSG.Monster.B.Classical.UnitarySix (bar)
open Matrix

theorem testBit_nland (x y i : ℕ) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) :=
  Nat.testBit_and x y i

theorem testBit_nxor (x y i : ℕ) : (Nat.xor x y).testBit i = (x.testBit i ^^ y.testBit i) :=
  Nat.testBit_xor x y i

theorem testBit_nlor (x y i : ℕ) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) :=
  Nat.testBit_or x y i

@[expose] def fb (x : F4) (s : ℕ) : Bool := x.code.val.testBit s

theorem f4_ext : ∀ {x y : F4}, fb x 0 = fb y 0 → fb x 1 = fb y 1 → x = y := by decide

theorem fb_add : ∀ x y : F4, fb (x + y) 0 = (fb x 0 ^^ fb y 0) ∧ fb (x + y) 1 = (fb x 1 ^^ fb y 1) := by
  decide

theorem fb_mul : ∀ x y : F4, fb (x * y) 0 = ((fb x 0 && fb y 0) ^^ (fb x 1 && fb y 1)) ∧
    fb (x * y) 1 = ((fb x 0 && fb y 1) ^^ (fb x 1 && (fb y 0 ^^ fb y 1))) := by
  decide

theorem fb_bar : ∀ x : F4, fb (bar x) 0 = (fb x 0 ^^ fb x 1) ∧ fb (bar x) 1 = fb x 1 := by
  decide

theorem inv_eq_bar : ∀ x : F4, x⁻¹ = bar x := by decide

theorem fb_zero : ∀ x : F4, x = 0 ↔ (fb x 0 = false ∧ fb x 1 = false) := by decide

theorem fb_zero' (s : ℕ) : fb 0 s = false := by
  change (0 : ℕ).testBit s = false
  exact Nat.zero_testBit s

theorem fb_add' (x y : F4) {s : ℕ} (hs : s < 2) : fb (x + y) s = (fb x s ^^ fb y s) := by
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · exact (fb_add x y).1
  · exact (fb_add x y).2

theorem fb_vec6 (n : ℕ) (t : Fin 6) {s : ℕ} (hs : s < 2) : fb (vec6 n t) s = n.testBit (2 * t + s) := by
  change (n / 4 ^ (t : ℕ) % 4).testBit s = _
  have h4 : (4 : ℕ) ^ (t : ℕ) = 2 ^ (2 * (t : ℕ)) := by rw [pow_mul]; rfl
  have h4' : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4, h4', Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hs, Nat.add_comm]

theorem vec6_inj {a b : ℕ} (ha : a < 4096) (hb : b < 4096) (h : vec6 a = vec6 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro c
  by_cases hc : c < 12
  · have e : fb (vec6 a ⟨c / 2, by omega⟩) (c % 2) = fb (vec6 b ⟨c / 2, by omega⟩) (c % 2) := by
      rw [h]
    rw [fb_vec6 _ _ (by omega), fb_vec6 _ _ (by omega)] at e
    have e2 : 2 * (c / 2) + c % 2 = c := by omega
    simpa only [e2] using e
  · have hle : 4096 ≤ 2 ^ c := le_trans (by decide : 4096 ≤ 2 ^ 12)
      (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

theorem enc6_eq (v : V6) : enc6 v = (v 0).code.val * 1 + ((v 1).code.val * 4 + ((v 2).code.val * 16 +
    ((v 3).code.val * 64 + ((v 4).code.val * 256 + ((v 5).code.val * 1024 + 0))))) := by
  simp [enc6, List.finRange_succ]

theorem vec6_enc6 (v : V6) : vec6 (enc6 v) = v ∧ enc6 v < 4096 := by
  have h0 := (v 0).code.isLt
  have h1 := (v 1).code.isLt
  have h2 := (v 2).code.isLt
  have h3 := (v 3).code.isLt
  have h4 := (v 4).code.isLt
  have h5 := (v 5).code.isLt
  rw [enc6_eq]
  refine ⟨funext fun t => ?_, by omega⟩
  change (⟨⟨_, _⟩⟩ : F4) = v t
  cases ht : v t with
  | mk c =>
    congr 1
    apply Fin.ext
    simp only
    fin_cases t <;> simp_all <;> omega

theorem testBit_enc6 (v : V6) (t : Fin 6) {s : ℕ} (hs : s < 2) :
    (enc6 v).testBit (2 * t + s) = fb (v t) s := by
  rw [← fb_vec6 _ _ hs, (vec6_enc6 v).1]

theorem finRange6 : List.finRange 6 = [0, 1, 2, 3, 4, 5] := by decide

theorem piv_eq (v : V6) : piv v = if v 0 ≠ 0 then 0 else if v 1 ≠ 0 then 1 else if v 2 ≠ 0 then 2
    else if v 3 ≠ 0 then 3 else if v 4 ≠ 0 then 4 else if v 5 ≠ 0 then 5 else 0 := by
  unfold piv
  rw [finRange6]
  by_cases h0 : v 0 = 0 <;> by_cases h1 : v 1 = 0 <;> by_cases h2 : v 2 = 0 <;>
    by_cases h3 : v 3 = 0 <;> by_cases h4 : v 4 = 0 <;> by_cases h5 : v 5 = 0 <;>
    simp [List.find?, h0, h1, h2, h3, h4, h5]

theorem fget2_eq (r : ℕ) (t : Fin 6) : fget r t 2 = (vec6 r t).code.val := by
  rw [fget_eq]
  change r >>> ((t : ℕ) * 2) % 2 ^ 2 = r / 4 ^ (t : ℕ) % 4
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm, pow_mul]
  rfl

theorem f4_eq_zero_iff : ∀ x : F4, x = 0 ↔ x.code.val = 0 := by decide

theorem vec6_ne_zero (r : ℕ) (t : Fin 6) : vec6 r t ≠ 0 ↔ 0 < fget r t 2 := by
  rw [fget2_eq, Ne, f4_eq_zero_iff]
  omega

theorem pivK_eq (r : ℕ) : pivK r = (piv (vec6 r) : ℕ) := by
  have hb : ∀ (t : ℕ) (ht : t < 6), Nat.blt 0 (fget r t 2) = decide (vec6 r ⟨t, ht⟩ ≠ 0) :=
    fun t ht => by rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff, vec6_ne_zero]
  simp only [pivK]
  rw [hb 0 (by decide), hb 1 (by decide), hb 2 (by decide), hb 3 (by decide), hb 4 (by decide),
    hb 5 (by decide), piv_eq]
  by_cases h0 : vec6 r 0 = 0 <;> by_cases h1 : vec6 r 1 = 0 <;> by_cases h2 : vec6 r 2 = 0 <;>
    by_cases h3 : vec6 r 3 = 0 <;> by_cases h4 : vec6 r 4 = 0 <;> by_cases h5 : vec6 r 5 = 0 <;>
    simp [h0, h1, h2, h3, h4, h5]

theorem testBit_sel (c : Bool) (x i : ℕ) : (sel c x).testBit i = (c && x.testBit i) := by
  cases c <;> simp [sel]

theorem xorB_eq (a b : Bool) : xorB a b = (a ^^ b) := by cases a <;> cases b <;> rfl

theorem cb_eq (x t s : ℕ) : cb x t s = x.testBit (t + t + s) := bit_eq _ _

theorem testBit_xorK_zero (f : ℕ → ℕ) (i : ℕ) : (xorK 0 f).testBit i = false := Nat.zero_testBit i

theorem combTerm_bit {x y : F4} {A0 A1 i s : ℕ} (hs : s < 2) (h0 : A0.testBit i = fb x 0)
    (h1 : A1.testBit i = fb x 1) {b0 b1 : Bool} (e0 : b0 = fb y 0)
    (e1 : b1 = fb y 1) :
    (nIf(Nat.beq s 0, Nat.xor (sel b0 A0) (sel b1 A1),
      Nat.xor (sel b1 A0) (sel (xorB b0 b1) A1))).testBit i = fb (x * y) s := by
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · change (Nat.xor (sel b0 A0) (sel b1 A1)).testBit i = _
    rw [(fb_mul x y).1]
    change ((sel b0 A0) ^^^ (sel b1 A1)).testBit i = _
    rw [Nat.testBit_xor, testBit_sel, testBit_sel, h0, h1, e0, e1]
    cases fb x 0 <;> cases fb x 1 <;> cases fb y 0 <;> cases fb y 1 <;> rfl
  · change (Nat.xor (sel b1 A0) (sel (xorB b0 b1) A1)).testBit i = _
    rw [(fb_mul x y).2]
    change ((sel b1 A0) ^^^ (sel (xorB b0 b1) A1)).testBit i = _
    rw [Nat.testBit_xor, testBit_sel, testBit_sel, h0, h1, xorB_eq, e0, e1]
    cases fb x 0 <;> cases fb x 1 <;> cases fb y 0 <;> cases fb y 1 <;> rfl

theorem combPl_bit {A : ℕ → ℕ → ℕ} {m : ℕ → ℕ} {a : ℕ → F4} {i : ℕ} (t : Fin 6) {s : ℕ}
    (hs : s < 2) : ∀ n, (∀ r < n, ∀ s' < 2, (A r s').testBit i = fb (a r) s') →
    (combPl n A m t s).testBit i = fb (∑ r ∈ Finset.range n, a r * vec6 (m r) t) s
  | 0, _ => by
    rw [Finset.sum_range_zero, fb_zero']
    exact Nat.zero_testBit i
  | n + 1, hA => by
    have ih := combPl_bit (m := m) t hs n (fun r hr => hA r (Nat.lt_succ_of_lt hr))
    change (_ ^^^ combPl n A m t s).testBit i = _
    rw [Nat.testBit_xor, ih, Finset.sum_range_succ, fb_add' _ _ hs, Bool.xor_comm]
    congr 1
    refine combTerm_bit hs (hA n (Nat.lt_succ_self n) 0 (by decide))
      (hA n (Nat.lt_succ_self n) 1 (by decide)) ?_ ?_
    · rw [cb_eq, fb_vec6 _ _ (by decide), two_mul]
    · rw [cb_eq, fb_vec6 _ _ (by decide), two_mul]

@[expose] def barB (f : Bool) (v : V6) : V6 := if f then barV v else v

@[expose] def PlanesAt (X i : ℕ) (v : V6) : Prop :=
  ∀ (t : Fin 6) (s : ℕ), s < 2 → (xp X (t + t + s)).testBit i = fb (v t) s

theorem frPl_bit {X i : ℕ} {v : V6} (hX : PlanesAt X i v) (f : Bool) (t : Fin 6) {s : ℕ}
    (hs : s < 2) : (frPl X f t s).testBit i = fb (barB f v t) s := by
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> cases f
  · exact hX t 0 (by decide)
  · change ((xp X (t + t + 0)) ^^^ (xp X (t + t + 1))).testBit i = _
    rw [Nat.testBit_xor, hX t 0 (by decide), hX t 1 (by decide)]
    exact (fb_bar (v t)).1.symm
  · exact hX t 1 (by decide)
  · exact (hX t 1 (by decide)).trans (fb_bar (v t)).2.symm

@[expose] def vN (u : V6) (r : ℕ) : F4 := if h : r < 6 then u ⟨r, h⟩ else 0

theorem vecMul_apply6 (u : V6) (M : ℕ → ℕ) (t : Fin 6) :
    (u ᵥ* Matrix.of (fun r : Fin 6 => vec6 (M r))) t = ∑ r ∈ Finset.range 6, vN u r * vec6 (M r) t := by
  rw [← Fin.sum_univ_eq_sum_range (fun r => vN u r * vec6 (M r) t) 6]
  simp [Matrix.vecMul, dotProduct, vN]

theorem imPl_bit {X i : ℕ} {v : V6} (hX : PlanesAt X i v) (f : Bool) (M : ℕ → ℕ) (t : Fin 6)
    {s : ℕ} (hs : s < 2) : (combPl 6 (frPl X f) M t s).testBit i =
      fb ((barB f v ᵥ* Matrix.of (fun r : Fin 6 => vec6 (M r))) t) s := by
  rw [vecMul_apply6, combPl_bit t hs 6]
  intro r hr s' hs'
  rw [frPl_bit hX f ⟨r, hr⟩ hs']
  simp [vN, hr]

theorem testBit_maskN {w i : ℕ} : (maskN w).testBit i = decide (i < w) := by
  change (Nat.sub (pw2 w) 1).testBit i = _
  rw [pw2_eq]
  exact Nat.testBit_two_pow_sub_one w i

theorem testBit_orN' {n i : ℕ} {f : ℕ → ℕ} : (orN n f).testBit i = true ↔ ∃ t < n, (f t).testBit i = true := by
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

theorem testBit_xorK_single {i p : ℕ} {f : ℕ → ℕ} : ∀ {n : ℕ}, p < n →
    (∀ t < n, t ≠ p → (f t).testBit i = false) → (xorK n f).testBit i = (f p).testBit i
  | 0, hp, _ => absurd hp (Nat.not_lt_zero _)
  | n + 1, hp, h => by
    rw [xorK_succ, Nat.testBit_xor]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
    · rw [h n (Nat.lt_succ_self n) (by omega), testBit_xorK_single hp
        (fun t ht htp => h t (Nat.lt_succ_of_lt ht) htp), Bool.false_xor]
    · rw [testBit_xorK_none (fun t ht => h t (Nat.lt_succ_of_lt ht) (by omega)), Bool.xor_false]
  where
    testBit_xorK_none {i : ℕ} {f : ℕ → ℕ} : ∀ {n : ℕ}, (∀ t < n, (f t).testBit i = false) →
        (xorK n f).testBit i = false
      | 0, _ => Nat.zero_testBit i
      | n + 1, h => by
        rw [xorK_succ, Nat.testBit_xor, h n (Nat.lt_succ_self n),
          testBit_xorK_none (fun t ht => h t (Nat.lt_succ_of_lt ht)), Bool.false_xor]

theorem piv_least (w : V6) (hw : w ≠ 0) : w (piv w) ≠ 0 ∧ ∀ t : Fin 6, t < piv w → w t = 0 := by
  have hw' : ∃ t, w t ≠ 0 := by
    by_contra hc
    exact hw (funext fun t => by
      by_contra h
      exact hc ⟨t, h⟩)
  obtain ⟨t0, ht0⟩ := hw'
  rw [piv_eq]
  by_cases h0 : w 0 = 0 <;> by_cases h1 : w 1 = 0 <;> by_cases h2 : w 2 = 0 <;>
    by_cases h3 : w 3 = 0 <;> by_cases h4 : w 4 = 0 <;> by_cases h5 : w 5 = 0 <;>
    simp [h0, h1, h2, h3, h4, h5] <;>
    first
    | (intro t ht; fin_cases t <;> simp_all)
    | (fin_cases t0 <;> simp_all)

theorem piv_zero (w : V6) (hw : w = 0) : w (piv w) = 0 := by rw [hw]; rfl

@[expose] def WAt (W : ℕ → ℕ → ℕ) (i : ℕ) (w : V6) : Prop :=
  ∀ (t : ℕ) (ht : t < 6) (s : ℕ), s < 2 → (W t s).testBit i = fb (w ⟨t, ht⟩) s

theorem nz_bit {W : ℕ → ℕ → ℕ} {i : ℕ} {w : V6} (hW : WAt W i w) (t : ℕ) (ht : t < 6) :
    (Nat.lor (W t 0) (W t 1)).testBit i = decide (w ⟨t, ht⟩ ≠ 0) := by
  change ((W t 0) ||| (W t 1)).testBit i = _
  rw [Nat.testBit_or, hW t ht 0 (by decide), hW t ht 1 (by decide)]
  have := fb_zero (w ⟨t, ht⟩)
  cases h0 : fb (w ⟨t, ht⟩) 0 <;> cases h1 : fb (w ⟨t, ht⟩) 1 <;> simp_all

theorem firstPl_bit {W : ℕ → ℕ → ℕ} {i : ℕ} (hi : i < 693) {w : V6} (hW : WAt W i w) (t : ℕ)
    (ht : t < 6) : (firstPl W t).testBit i =
      (decide (w ⟨t, ht⟩ ≠ 0) && !decide (∃ s, ∃ hs : s < t, w ⟨s, by omega⟩ ≠ 0)) := by
  unfold firstPl
  change (_ &&& (maskN 693 ^^^ _)).testBit i = _
  rw [Nat.testBit_and, Nat.testBit_xor, nz_bit hW t ht, testBit_maskN, decide_eq_true hi,
    Bool.true_xor]
  congr 1
  congr 1
  rw [Bool.eq_iff_iff, testBit_orN', decide_eq_true_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [nz_bit hW s (by omega)] at h
    exact ⟨s, hs, of_decide_eq_true h⟩
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, by rw [nz_bit hW s (by omega)]; exact decide_eq_true h⟩

theorem leadPl_bit {W : ℕ → ℕ → ℕ} {i : ℕ} (hi : i < 693) {w : V6} (hW : WAt W i w) {s : ℕ}
    (hs : s < 2) : (leadPl W s).testBit i = fb (w (piv w)) s := by
  unfold leadPl
  by_cases hw : w = 0
  · rw [piv_zero w hw, fb_zero', testBit_xorK_single.testBit_xorK_none]
    intro t ht
    rw [testBit_nland, firstPl_bit hi hW t ht]
    simp [hw]
  · obtain ⟨hp1, hp2⟩ := piv_least w hw
    have hfirst : ∀ (t : ℕ) (ht : t < 6), (firstPl W t).testBit i = decide (t = piv w) := by
      intro t ht
      rw [firstPl_bit hi hW t ht]
      rcases lt_trichotomy t (piv w) with h | h | h
      · have : w ⟨t, ht⟩ = 0 := hp2 ⟨t, ht⟩ h
        simp [this, show t ≠ (piv w : ℕ) by omega]
      · have e : (⟨t, ht⟩ : Fin 6) = piv w := Fin.ext h
        have h1 : w ⟨t, ht⟩ ≠ 0 := by rw [e]; exact hp1
        have h2 : ¬ ∃ s', ∃ hs' : s' < t, w ⟨s', by omega⟩ ≠ 0 := by
          rintro ⟨s', hs', h'⟩
          exact h' (hp2 ⟨s', by omega⟩ (show s' < (piv w : ℕ) by omega))
        rw [decide_eq_true h1, decide_eq_false h2, decide_eq_true h]
        rfl
      · simp only [show t ≠ (piv w : ℕ) by omega, decide_false]
        have : ∃ s', ∃ hs' : s' < t, w ⟨s', by omega⟩ ≠ 0 := ⟨piv w, h, by simpa using hp1⟩
        simp [this]
    rw [testBit_xorK_single (p := piv w) (piv w).2 (fun t ht htp => by
      rw [testBit_nland, hfirst t ht, decide_eq_false htp, Bool.false_and]),
      testBit_nland, hfirst _ (piv w).2, decide_eq_true (rfl : (piv w : ℕ) = piv w), Bool.true_and,
      hW _ (piv w).2 s hs]

theorem normPl_bit {W : ℕ → ℕ → ℕ} {i : ℕ} (hi : i < 693) {w : V6} (hW : WAt W i w) (t : ℕ)
    (ht : t < 6) {s : ℕ} (hs : s < 2) :
    (normPl W t s).testBit i = fb (((w (piv w))⁻¹ • w) ⟨t, ht⟩) s := by
  rw [Pi.smul_apply, smul_eq_mul, inv_eq_bar]
  have l0 := leadPl_bit hi hW (s := 0) (by decide)
  have l1 := leadPl_bit hi hW (s := 1) (by decide)
  have w0 := hW t ht 0 (by decide)
  have w1 := hW t ht 1 (by decide)
  have b := fb_bar (w (piv w))
  have m := fb_mul (bar (w (piv w))) (w ⟨t, ht⟩)
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · have e : normPl W t 0 = ((leadPl W 0 ^^^ leadPl W 1) &&& W t 0) ^^^ (leadPl W 1 &&& W t 1) :=
      rfl
    rw [e, m.1, b.1, b.2]
    simp only [Nat.testBit_xor, Nat.testBit_and, l0, l1, w0, w1]
  · have e : normPl W t 1 = (leadPl W 1 &&& W t 0) ^^^
        (((leadPl W 0 ^^^ leadPl W 1) ^^^ leadPl W 1) &&& W t 1) := rfl
    rw [e, m.2, b.1, b.2]
    simp only [Nat.testBit_xor, Nat.testBit_and, l0, l1, w0, w1]
    cases fb (w (piv w)) 0 <;> cases fb (w (piv w)) 1 <;> cases fb (w ⟨t, ht⟩) 0 <;>
      cases fb (w ⟨t, ht⟩) 1 <;> rfl

@[expose] def imV (f : Bool) (rows : ℕ → ℕ) (v : V6) : V6 :=
  barB f v ᵥ* Matrix.of (fun r : Fin 6 => vec6 (rows r))

@[expose] def normV (w : V6) : V6 := (w (piv w))⁻¹ • w

theorem singU_bit {X M F k i : ℕ} (hi : i < 693) {v : V6} (hX : PlanesAt X i v) (t : ℕ) (ht : t < 6)
    {s : ℕ} (hs : s < 2) :
    (singU X M F k t s).testBit i = fb (normV (imV (bit F k) (fun r => permTab 6 12 M r k) v) ⟨t, ht⟩) s := by
  unfold singU normV
  exact normPl_bit hi (fun t' ht' s' hs' =>
    imPl_bit hX (bit F k) (fun r => permTab 6 12 M r k) ⟨t', ht'⟩ hs') t ht hs

theorem xor_true_of_ne {a b : Bool} (h : a ≠ b) : (a ^^ b) = true := by
  cases a <;> cases b <;> simp_all

theorem planeD_bit {X i : ℕ} {v : V6} (hX : PlanesAt X i v) (R : ℕ → ℕ) :
    (planeD X R).testBit i = true ↔
      (fun t : Fin 6 => ∑ b ∈ Finset.range 3, v (piv (vec6 (R b))) * vec6 (R b) t) ≠ v := by
  have hA : ∀ b < 3, ∀ s' < 2, (xp X (Nat.add (Nat.add (pivK (R b)) (pivK (R b))) s')).testBit i =
      fb (v (piv (vec6 (R b)))) s' := by
    intro b _ s' hs'
    have h := hX (piv (vec6 (R b))) s' hs'
    rw [← pivK_eq] at h
    exact h
  have key : ∀ (t : ℕ) (ht : t < 6) (s : ℕ), s < 2 →
      (Nat.xor (combPl 3 (fun b s' => xp X (Nat.add (Nat.add (pivK (R b)) (pivK (R b))) s')) R t s)
        (xp X (Nat.add (Nat.add t t) s))).testBit i =
      (fb (∑ b ∈ Finset.range 3, v (piv (vec6 (R b))) * vec6 (R b) ⟨t, ht⟩) s ^^ fb (v ⟨t, ht⟩) s) := by
    intro t ht s hs
    rw [testBit_nxor]
    have h1 := combPl_bit (A := fun b s' => xp X (Nat.add (Nat.add (pivK (R b)) (pivK (R b))) s'))
      (m := R) (a := fun b => v (piv (vec6 (R b)))) (i := i) ⟨t, ht⟩ hs 3 hA
    have h2 := hX ⟨t, ht⟩ s hs
    exact congrArg₂ (· ^^ ·) h1 h2
  unfold planeD
  rw [testBit_orN']
  constructor
  · rintro ⟨t, ht, h⟩ e
    rw [testBit_orN'] at h
    obtain ⟨s, hs, h⟩ := h
    rw [key t ht s hs] at h
    have e2 : ∑ b ∈ Finset.range 3, v (piv (vec6 (R b))) * vec6 (R b) ⟨t, ht⟩ = v ⟨t, ht⟩ :=
      congrFun e ⟨t, ht⟩
    rw [e2] at h
    simp at h
  · intro hne
    have ⟨t, ht⟩ : ∃ t : Fin 6,
        ∑ b ∈ Finset.range 3, v (piv (vec6 (R b))) * vec6 (R b) t ≠ v t := by
      by_contra hc
      exact hne (funext fun t => by
        by_contra h
        exact hc ⟨t, h⟩)
    have hb : fb (∑ b ∈ Finset.range 3, v (piv (vec6 (R b))) * vec6 (R b) t) 0 ≠ fb (v t) 0 ∨
        fb (∑ b ∈ Finset.range 3, v (piv (vec6 (R b))) * vec6 (R b) t) 1 ≠ fb (v t) 1 := by
      by_contra hc
      rw [not_or, not_not, not_not] at hc
      exact ht (f4_ext hc.1 hc.2)
    refine ⟨t, t.2, ?_⟩
    rw [testBit_orN']
    rcases hb with h | h
    · exact ⟨0, by decide, by rw [key t t.2 0 (by decide)]; exact xor_true_of_ne h⟩
    · exact ⟨1, by decide, by rw [key t t.2 1 (by decide)]; exact xor_true_of_ne h⟩

end CFSG.KC.Orb14

end
