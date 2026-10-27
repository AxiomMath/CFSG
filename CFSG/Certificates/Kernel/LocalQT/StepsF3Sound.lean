module

public import Certificates.Data.Kernel.LocalQT.SecF3
public import CFSG.Certificates.Kernel.LocalQT.Steps
import all CFSG.Certificates.Kernel.LocalQT.Steps
public import CFSG.Certificates.Kernel.LocalCompOps3Snd.Bridge
public import CFSG.Certificates.Kernel.Spor.F3LaneSound
import CFSG.Certificates.Kernel.SporSch.LyMatLemmas

public section

namespace CFSG.KC.LQT.F3S

open CFSG.KC.LQT CFSG.KC.Ord CFSG.KS.Ord CFSG.F3.Native CFSG.KS.F3L
open CFSG.KS.SporSch.LyM (canon_ext canon_ent eq_of_cast ordMat_apply testBit_ent andB_true' cfacts)
open CFSG.KC.LocalComp.Ops3Snd (mat3 mat3_mul)

theorem sl_one (i : Nat) : Nat.shiftLeft 1 i = 2 ^ i := by
  change 1 <<< i = _
  rw [Nat.one_shiftLeft]

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.LQT.strictB y k = k y := by
  cases y <;> rfl

theorem blkMask_testBit {P g : Nat} (hg : g ≤ P) (k q : Nat) :
    (blkMask P g k).testBit q = decide (q < P * 2 ^ k ∧ q % P < g) := by
  induction k generalizing q with
  | zero =>
    change (Nat.shiftLeft 1 g - 1).testBit q = _
    rw [sl_one, Nat.testBit_two_pow_sub_one, pow_zero, mul_one, Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨by omega, by rw [Nat.mod_eq_of_lt (by omega)]; exact h⟩
    · rintro ⟨h1, h2⟩
      rwa [Nat.mod_eq_of_lt h1] at h2
  | succ i ih =>
    change (blkMask P g i ||| blkMask P g i <<< (P * Nat.shiftLeft 1 i)).testBit q = _
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, ih, ih, sl_one, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    have e2 : P * 2 ^ (i + 1) = P * 2 ^ i + P * 2 ^ i := by ring
    rw [e2]
    by_cases hq : q < P * 2 ^ i
    · constructor
      · rintro (h | ⟨h1, -⟩)
        · exact ⟨by omega, h.2⟩
        · omega
      · rintro ⟨-, h2⟩
        exact Or.inl ⟨hq, h2⟩
    · have hm : (q - P * 2 ^ i) % P = q % P := Nat.sub_mul_mod (by omega)
      rw [hm]
      constructor
      · rintro (h | ⟨-, h1, h2⟩)
        · omega
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        exact Or.inr ⟨by omega, by omega, h2⟩

theorem dm {D q a c : Nat} (h : q = D * a + c) (hc : c < D) : q / D = a ∧ q % D = c := by
  subst h
  have hD : 0 < D := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hD, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem stage_bits {g D : Nat} (hg : 0 < g) (hD : 2 * g ≤ D) (b f : Nat → Bool)
    (hf : ∀ y, f y = (decide (y % D < g) && b (g * (y / D) + y % D))) (q : Nat) :
    ((f q && decide (q % (2 * D) < g)) ||
        (f (D - g + q) && !decide ((D - g + q) % (2 * D) < g))) =
      (decide (q % (2 * D) < 2 * g) && b (2 * g * (q / (2 * D)) + q % (2 * D))) := by
  have hD0 : 0 < 2 * D := by omega
  obtain ⟨k, r, hr, hq⟩ : ∃ k r, r < 2 * D ∧ q = 2 * D * k + r :=
    ⟨q / (2 * D), q % (2 * D), Nat.mod_lt _ hD0, (Nat.div_add_mod q (2 * D)).symm⟩
  obtain ⟨hk2, hr2⟩ := dm hq hr
  have e1 : 2 * D * k = D * (2 * k) := by ring
  have e2 : 2 * g * k = g * (2 * k) := by ring
  have e3 : D * (2 * k + 1) = 2 * D * k + D := by ring
  have e4 : D * (2 * (k + 1)) = 2 * D * k + 2 * D := by ring
  have e5 : g * (2 * k + 1) = 2 * g * k + g := by ring
  rw [hf, hf, hk2, hr2]
  rcases Nat.lt_or_ge r D with hrD | hrD
  · obtain ⟨a1, c1⟩ := dm (D := D) (q := q) (a := 2 * k) (c := r) (by rw [hq, e1]) hrD
    rw [a1, c1]
    rcases Nat.lt_or_ge r g with hrg | hrg
    · obtain ⟨-, c2⟩ := dm (D := D) (q := D - g + q) (a := 2 * k) (c := r + (D - g))
        (by rw [hq, e1]; omega) (by omega)
      obtain ⟨-, c3⟩ := dm (D := 2 * D) (q := D - g + q) (a := k) (c := r + (D - g))
        (by rw [hq]; omega) (by omega)
      rw [c2, c3, e2]
      simp [hrg, show ¬ r + (D - g) < g by omega, show r < 2 * g by omega]
    · obtain ⟨a2, c2⟩ := dm (D := D) (q := D - g + q) (a := 2 * k + 1) (c := r - g)
        (by rw [hq, e3]; omega) (by omega)
      obtain ⟨-, c3⟩ := dm (D := 2 * D) (q := D - g + q) (a := k) (c := r + (D - g))
        (by rw [hq]; omega) (by omega)
      rw [a2, c2, c3, show g * (2 * k + 1) + (r - g) = 2 * g * k + r by rw [e5]; omega]
      by_cases h2 : r < 2 * g
      · simp [h2, show ¬ r < g by omega, show r - g < g by omega,
          show ¬ r + (D - g) < g by omega]
      · simp [h2, show ¬ r < g by omega, show ¬ r - g < g by omega]
  · simp only [show ¬ r < g by omega, show ¬ r < 2 * g by omega, decide_false, Bool.and_false,
      Bool.false_or, Bool.false_and]
    rcases Nat.lt_or_ge r (D + g) with hrg | hrg
    · obtain ⟨-, c2⟩ := dm (D := D) (q := D - g + q) (a := 2 * k + 1) (c := r - g)
        (by rw [hq, e3]; omega) (by omega)
      rw [c2]
      simp [show ¬ r - g < g by omega]
    · obtain ⟨-, c2⟩ := dm (D := D) (q := D - g + q) (a := 2 * (k + 1)) (c := r - D - g)
        (by rw [hq, e4]; omega) (by omega)
      obtain ⟨-, c3⟩ := dm (D := 2 * D) (q := D - g + q) (a := k + 1) (c := r - D - g)
        (by rw [hq]; ring_nf; omega) (by omega)
      rw [c2, c3]
      by_cases h3 : r - D - g < g <;> simp [h3]

@[expose] def Inv (w s : Nat) (b : Nat → Bool) (x : Nat) : Prop :=
  ∀ q, x.testBit q =
    (decide (q % (w * 2 ^ s) < 2 ^ s) && b (2 ^ s * (q / (w * 2 ^ s)) + q % (w * 2 ^ s)))

theorem gStage_inv {w K s : Nat} (hw : 2 ≤ w) (hs : s < K) {b : Nat → Bool}
    (hb : ∀ t, 2 ^ K ≤ t → b t = false) {x : Nat} (hx : Inv w s b x) :
    Inv w (s + 1) b (gStage w K s x) := by
  unfold Inv at hx ⊢
  have hg : 0 < 2 ^ s := Nat.two_pow_pos s
  have hD : 2 * 2 ^ s ≤ w * 2 ^ s := Nat.mul_le_mul_right _ hw
  have hDpos : 0 < w * 2 ^ s := by positivity
  have hspan : 2 * (w * 2 ^ s) * 2 ^ (K - (s + 1)) = w * 2 ^ K := by
    have e : K = (s + 1) + (K - (s + 1)) := by omega
    conv_rhs => rw [e, pow_add, pow_succ]
    ring
  have hxb : ∀ q, w * 2 ^ K ≤ q → x.testBit q = false := by
    intro q hq
    rw [hx q]
    have h1 : 2 ^ (K - s) ≤ q / (w * 2 ^ s) := by
      rw [Nat.le_div_iff_mul_le hDpos]
      have e : 2 ^ (K - s) * (w * 2 ^ s) = w * 2 ^ K := by
        have e' : K = s + (K - s) := by omega
        conv_rhs => rw [e', pow_add]
        ring
      omega
    have h2 : 2 ^ K ≤ 2 ^ s * (q / (w * 2 ^ s)) := by
      calc 2 ^ K = 2 ^ s * 2 ^ (K - s) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_left _ h1
    rw [hb _ (by omega), Bool.and_false]
  have hM := blkMask_testBit (P := 2 * (w * 2 ^ s)) (g := 2 ^ s) (by omega) (K - (s + 1))
  have ha : ∀ q, (x &&& blkMask (2 * (w * 2 ^ s)) (2 ^ s) (K - (s + 1))).testBit q =
      (x.testBit q && decide (q % (2 * (w * 2 ^ s)) < 2 ^ s)) := by
    intro q
    rw [Nat.testBit_and, hM, hspan]
    by_cases hq : q < w * 2 ^ K
    · simp [hq]
    · rw [hxb q (by omega)]
      simp
  intro q
  have eg : gStage w K s x = (x &&& blkMask (2 * (w * 2 ^ s)) (2 ^ s) (K - (s + 1)) |||
      (x ^^^ (x &&& blkMask (2 * (w * 2 ^ s)) (2 ^ s) (K - (s + 1)))) >>>
        (w * 2 ^ s - 2 ^ s)) := by
    unfold gStage
    rw [strictT_eq, sl_one]
    rfl
  have ex : ∀ a c : Bool, (a ^^ (a && c)) = (a && !c) := by decide
  rw [eg, Nat.testBit_or, Nat.testBit_shiftRight, Nat.testBit_xor, ha, ha, ex,
    show w * 2 ^ (s + 1) = 2 * (w * 2 ^ s) by ring, show 2 ^ (s + 1) = 2 * 2 ^ s by ring]
  exact stage_bits hg hD b x.testBit hx q

theorem gath_init {w K : Nat} (hw : 0 < w) (X : Nat) :
    Inv w 0 (fun t => X.testBit (w * t) && decide (t < 2 ^ K)) (X &&& blkMask w 1 K) := by
  unfold Inv
  intro q
  rw [Nat.testBit_and, blkMask_testBit (by omega)]
  simp only [pow_zero, mul_one, one_mul]
  rcases Nat.eq_zero_or_pos (q % w) with h0 | h0
  · have hq : w * (q / w) = q := by
      have := Nat.div_add_mod q w
      omega
    have hlt : q < w * 2 ^ K ↔ q / w < 2 ^ K := by
      rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]
    rw [h0, Nat.add_zero, hq]
    simp [hlt]
  · simp [show ¬ q % w < 1 by omega]

theorem gath_inv {w K : Nat} (hw : 2 ≤ w) (X : Nat) : ∀ s, s ≤ K →
    Inv w s (fun t => X.testBit (w * t) && decide (t < 2 ^ K))
      (Nat.rec (motive := fun _ => Nat) (Nat.land X (blkMask w (nat_lit 1) K))
        (fun s acc => strictT acc fun a => gStage w K s a) s)
  | 0, _ => gath_init (by omega) X
  | s + 1, h => by
    change Inv w (s + 1) _ (strictT (Nat.rec (motive := fun _ => Nat)
      (Nat.land X (blkMask w (nat_lit 1) K)) (fun s acc => strictT acc fun a => gStage w K s a) s)
      fun a => gStage w K s a)
    rw [strictT_eq]
    exact gStage_inv hw (by omega) (fun t ht => by simp; omega) (gath_inv hw X s (by omega))

theorem gathN_testBit {w : Nat} (hw : 2 ≤ w) (K X t : Nat) :
    (gathN w K X).testBit t = (X.testBit (w * t) && decide (t < 2 ^ K)) := by
  have h := gath_inv hw X K (Nat.le_refl K) t
  unfold gathN
  rw [h]
  have hW : 0 < w * 2 ^ K := by positivity
  by_cases ht : t < 2 ^ K
  · have ht' : t < w * 2 ^ K := by nlinarith [Nat.two_pow_pos K]
    rw [Nat.mod_eq_of_lt ht', Nat.div_eq_of_lt ht']
    simp [ht]
  · by_cases h1 : t % (w * 2 ^ K) < 2 ^ K
    · have ht2 : w * 2 ^ K ≤ t := by
        by_contra hc
        rw [Nat.mod_eq_of_lt (by omega)] at h1
        omega
      have h3 : 1 ≤ t / (w * 2 ^ K) := (Nat.le_div_iff_mul_le hW).2 (by omega)
      have h4 : 2 ^ K ≤ 2 ^ K * (t / (w * 2 ^ K)) := Nat.le_mul_of_pos_right _ h3
      simp [ht, show ¬ 2 ^ K * (t / (w * 2 ^ K)) + t % (w * 2 ^ K) < 2 ^ K by omega]
    · simp [ht, h1]

theorem gath3_p (w K X : Nat) : (gath3 w K X).p = gathN w K X := rfl

theorem gath3_m (w K X : Nat) : (gath3 w K X).m = gathN w K (X >>> 1) := rfl

theorem bit_lane {w : Nat} (hw : 2 ≤ w) (X t : Nat) :
    X.testBit (w * t) = (lane w X t).testBit 0 ∧ X.testBit (1 + w * t) = (lane w X t).testBit 1 := by
  unfold lane
  rw [testBit_ent, testBit_ent, Nat.zero_add]
  simp [show 0 < w by omega, show 1 < w by omega]

theorem bitVal_lane {v : Nat} (h : v < 3) :
    bitVal (v.testBit 0) (v.testBit 1) = ((v : Nat) : ZMod 3) := by
  interval_cases v <;> decide

theorem toMat_gath {d w K : Nat} (hw : 2 ≤ w) (hK : d * d ≤ 2 ^ K) {X : Nat}
    (hX : Canon 3 d w X) : toMat d (unlane d (gath3 w K X)) = ordMat 3 d w (d * w) X := by
  ext i j
  have ht : d * i.val + j.val < d * d := by nlinarith [i.isLt, j.isLt]
  rw [toMat_apply, unlane_get _ i.isLt, V.val_eq_bitVal, blk_p, blk_m, ordMat_apply, gath3_p,
    gath3_m, gathN_testBit hw, gathN_testBit hw, Nat.testBit_shiftRight]
  simp only [decide_eq_true j.isLt, decide_eq_true (Nat.lt_of_lt_of_le ht hK), Bool.true_and,
    Bool.and_true]
  rw [(bit_lane hw X _).1, (bit_lane hw X _).2, bitVal_lane (hX.2 _ ht)]
  unfold lane
  congr 3
  ring

theorem gath_wf {d w K : Nat} (hw : 2 ≤ w) {X : Nat} (hX : Canon 3 d w X) :
    (gath3 w K X).wf = true := by
  apply V.wf_of_bits
  intro t
  rw [gath3_p, gath3_m, gathN_testBit hw, gathN_testBit hw, Nat.testBit_shiftRight]
  by_cases ht : t < d * d
  · have hl := hX.2 t ht
    have hb : ((lane w X t).testBit 0 && (lane w X t).testBit 1) = false := by
      generalize lane w X t = v at hl
      interval_cases v <;> decide
    rw [(bit_lane hw X t).1, (bit_lane hw X t).2]
    revert hb
    cases (lane w X t).testBit 0 <;> cases (lane w X t).testBit 1 <;> simp
  · have h0 : X.testBit (w * t) = false := Nat.testBit_eq_false_of_lt
      (Nat.lt_of_lt_of_le hX.1 (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ (by omega))))
    simp [h0]

theorem rowsWF_gath {d w K : Nat} (hw : 2 ≤ w) {X : Nat} (hX : Canon 3 d w X) :
    RowsWF (unlane d (gath3 w K X)) :=
  RowsWF.of_canonM (canonM_unlane d (gath_wf hw hX))

theorem canon_inj {d w X Y : Nat} (hX : Canon 3 d w X) (hY : Canon 3 d w Y)
    (h : ordMat 3 d w (d * w) X = ordMat 3 d w (d * w) Y) : X = Y :=
  canon_ext hX hY fun i hi j hj => by
    have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    rw [ordMat_apply, ordMat_apply] at e
    exact eq_of_cast (canon_ent hX hi hj) (canon_ent hY hi hj) e

theorem stepOK_of_F3 {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {K : Nat}
    (hK : c.d * c.d ≤ 2 ^ K) (hd : 0 < c.d) {V P : Nat → Nat} {n : Nat}
    (hV : ∀ k < n, Canon c.p c.d c.w (V k)) (h : stepF3 c K (spreadE c.d c.d) V P n = true) :
    stepOK c V P n = true ∧ Canon c.p c.d c.w (V n) := by
  obtain ⟨-, hS, -, hpw⟩ := cfacts hc
  have hw : 2 ≤ c.w := by
    rw [hp] at hpw
    rcases Nat.lt_or_ge c.w 2 with h2 | h2
    · interval_cases hcw : c.w <;> simp at hpw
    · exact h2
  unfold stepF3 at h
  simp only [strictB_eq] at h
  obtain ⟨ha, h⟩ := andB_true' h
  obtain ⟨hb, h⟩ := andB_true' h
  obtain ⟨hvn, heq⟩ := andB_true' h
  have ha' : Nat.land (P n) 1048575 < n := Nat.le_of_ble_eq_true ha
  have hb' : Nat.shiftRight (P n) 20 < n := Nat.le_of_ble_eq_true hb
  have hA := hV _ ha'
  have hB := hV _ hb'
  have hN : Canon c.p c.d c.w (V n) := validM_canon hc hvn
  unfold eqV at heq
  obtain ⟨h1, h2⟩ := andB_true' heq
  have hG := CFSG.KS.F3L.V.ext' (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2)
  have hmul := mat3_mul c hc hp hA hB
  unfold mat3 at hmul
  rw [hS] at hmul
  rw [hp] at hA hB hN
  have m1 := toMat_gath hw hK hN
  rw [hG, ← mul_unlane hd, toMat_mul (unlane_size _ _) (rowsWF_gath hw hA) (rowsWF_gath hw hB),
    toMat_gath hw hK hA, toMat_gath hw hK hB, ← hmul.2] at m1
  have hc3 := hmul.1
  rw [hp] at hc3
  have e := canon_inj hN hc3 m1.symm
  refine ⟨?_, hp ▸ hN⟩
  unfold stepOK
  simp only [strictB_eq]
  rw [ha, hb, e, Nat.beq_refl]
  rfl

theorem steps_of_F3 {c : Lay} (hc : c.ok = true) (hp : c.p = 3) {K : Nat}
    (hK : c.d * c.d ≤ 2 ^ K) (hd : 0 < c.d) {V P : Nat → Nat} {N : Nat}
    (h0 : Canon c.p c.d c.w (V 0)) (h1 : Canon c.p c.d c.w (V 1))
    (h2 : Canon c.p c.d c.w (V 2)) (hs : StepsTo (stepF3 c K (spreadE c.d c.d) V P) N) :
    StepsTo (stepOK c V P) N := by
  unfold StepsTo at hs ⊢
  have hV : ∀ k, k < N → Canon c.p c.d c.w (V k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 3 with h3 | h3
      · interval_cases k
        · exact h0
        · exact h1
        · exact h2
      · exact (stepOK_of_F3 hc hp hK hd (fun j hj => ih j hj (by omega)) (hs k h3 hk)).2
  intro n h3 hn
  exact (stepOK_of_F3 hc hp hK hd (fun j hj => hV j (by omega)) (hs n h3 hn)).1

end CFSG.KC.LQT.F3S

end
