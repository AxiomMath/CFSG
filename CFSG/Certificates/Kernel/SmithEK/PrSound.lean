module

public import Certificates.Data.Kernel.SmithEKPr
public import CFSG.LargeExtraspecial.S14SMICheck
public import CFSG.Certificates.Kernel.SmithEK.TSound
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE
open CFSG.LargeExtraspecial.S14.SMI (prodCols)

theorem pqStrict_eq (y : Nat) (f : Nat → Bool) : pqStrict y f = f y := by
  cases y <;> rfl

theorem pqApply_eq : ∀ (L : List Nat) (c : Nat), pqApply L c = applyL L c
  | [], _ => rfl
  | x :: L, c => by
    have e1 : pqApply (x :: L) c =
        Nat.xor (Nat.mul (Nat.land c 1) x) (pqApply L (Nat.shiftRight c 1)) := rfl
    have e2 : applyL (x :: L) c = (if c.testBit 0 then x else 0) ^^^ applyL L (c / 2) := rfl
    have h1 : Nat.shiftRight c 1 = c / 2 := by
      change c >>> 1 = _
      rw [Nat.shiftRight_eq_div_pow, pow_one]
    have h2 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
    rw [e1, e2, pqApply_eq L, h1, h2, Nat.testBit_zero]
    change c % 2 * x ^^^ _ = _
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h]

theorem pqNot_eq (B v : Nat) : pqNot B v = !B.testBit v := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e : Nat.land (Nat.shiftRight B v) 1 = B / 2 ^ v % 2 := by
    change (B >>> v) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold pqNot
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one (B / 2 ^ v) with h | h <;> rw [h] <;> rfl

theorem pqFld_eq (k X : Nat) : pqFld k X = fld k X := by
  unfold pqFld fld
  change (X >>> (20 * k)) &&& (2 ^ 20 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pqKeySet_sound (pr : Nat) : ∀ (P : List Nat) (X Y j : Nat), j < P.length →
    (pqKeySet pr P X Y).testBit (pqKey pr (fld j X) (fld j Y)) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | q :: P, X, Y, j, hj => by
    have e : pqKeySet pr (q :: P) X Y = (1 <<< pqKey pr (X % 1048576) (Y % 1048576)) |||
        pqKeySet pr P (X / 1048576) (Y / 1048576) := rfl
    rw [e, Nat.testBit_or]
    cases j with
    | zero =>
      rw [fld_zero_k, fld_zero_k, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.true_or]
    | succ j =>
      rw [fld_succ, fld_succ, pqKeySet_sound pr P _ _ j (by simpa using hj), Bool.or_true]

theorem pqLane_sound {K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl l X0 X2 : Nat} :
    ∀ (P : List Nat) (k : Nat), pqLane K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl l X0 X2 P k = true →
      ∀ i, k + i < l → i < P.length → pqPair K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl (P.getD i 0)
        (k + i) (fld (k + i) X0) (fld (k + i) X2) = true
  | [], _, _, i, _, hi => absurd hi (Nat.not_lt_zero i)
  | p :: P, k, h, i, hil, hi => by
    have e : pqLane K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl l X0 X2 (p :: P) k = (Nat.ble l k ||
        (pqPair K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl p k (pqFld k X0) (pqFld k X2) &&
          pqStrict (Nat.succ k) (pqLane K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl l X0 X2 P))) := rfl
    have hc0 : Nat.ble l k = false := by
      cases hb : Nat.ble l k
      · rfl
      · rw [Nat.ble_eq] at hb
        omega
    rw [e, hc0, Bool.false_or, Bool.and_eq_true, pqStrict_eq, pqFld_eq, pqFld_eq] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have ih := pqLane_sound P (k + 1) h.2 i (by omega) (by simpa using hi)
      rw [show k + 1 + i = k + (i + 1) by omega] at ih
      simpa using ih

theorem pqRows_sound {C P : List Nat} {K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 lo n : Nat} :
    ∀ (Q : List Nat) (r : Nat), pqRows C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 lo n Q r = true →
      ∀ i < Q.length, lo ≤ r + i → r + i < lo + n →
        pqRow C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 (r + i) (Q.getD i 0) = true
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | pl :: Q, r, h, i, hi, h1, h2 => by
    have e : pqRows C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 lo n (pl :: Q) r =
        ((Nat.blt r lo || Nat.ble (lo + n) r ||
          pqRow C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 r pl) &&
          pqStrict (r + 1) (pqRows C P K1 K2 K3 K4 A0 A2 A4 A8 A10 A16 A6 A12 lo n Q)) := rfl
    rw [e, Bool.and_eq_true, pqStrict_eq] at h
    cases i with
    | zero =>
      have hb1 : Nat.blt r lo = false := by
        cases hb : Nat.blt r lo
        · rfl
        · rw [Nat.blt_eq] at hb
          omega
      have hb2 : Nat.ble (lo + n) r = false := by
        cases hb : Nat.ble (lo + n) r
        · rfl
        · rw [Nat.ble_eq] at hb
          omega
      have := h.1
      rw [hb1, hb2, Bool.false_or, Bool.false_or] at this
      simpa using this
    | succ i =>
      have ih := pqRows_sound Q (r + 1) h.2 i (by simpa using hi) (by omega) (by omega)
      rw [show r + 1 + i = r + (i + 1) by omega] at ih
      simpa using ih

theorem pqChk_sound {C P : List Nat} {lo n : Nat} (h : pqChk C P lo n = true) {l : Nat}
    (h1 : lo ≤ l) (h2 : l < lo + n) (hl : l < P.length) {k : Nat} (hk : k < l) :
    pqPair (pqKeySet 65521 P (C.getD 0 0) (C.getD 2 0)) (pqKeySet 65519 P (C.getD 4 0) (C.getD 8 0))
      (pqKeySet 65497 P (C.getD 10 0) (C.getD 16 0)) (pqKeySet 65479 P (C.getD 6 0) (C.getD 12 0))
      (pqApply C (fld l (C.getD 4 0))) (pqApply C (fld l (C.getD 8 0)))
      (pqApply C (fld l (C.getD 10 0))) (pqApply C (fld l (C.getD 16 0)))
      (pqApply C (fld l (C.getD 6 0))) (pqApply C (fld l (C.getD 12 0)))
      (P.getD l 0) (P.getD k 0) k (fld k (pqApply C (fld l (C.getD 0 0))))
      (fld k (pqApply C (fld l (C.getD 2 0)))) = true := by
  unfold pqChk at h
  simp only [pqStrict_eq] at h
  have hr := pqRows_sound P 0 h l hl (by omega) (by omega)
  rw [Nat.zero_add] at hr
  unfold pqRow at hr
  simp only [pqStrict_eq] at hr
  have e := pqLane_sound P 0 hr k (by omega) (by omega)
  rwa [Nat.zero_add] at e

theorem pqPair_sound {K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl p k u0 u2 : Nat}
    (h : pqPair K1 K2 K3 K4 X4 X8 X10 X16 X6 X12 pl p k u0 u2 = true) :
    K1.testBit (pqKey 65521 u0 u2) = false ∨ K2.testBit (pqKey 65519 (fld k X4) (fld k X8)) = false ∨
      K3.testBit (pqKey 65497 (fld k X10) (fld k X16)) = false ∨
      K4.testBit (pqKey 65479 (fld k X6) (fld k X12)) = false ∨ 0 < hermC p pl := by
  unfold pqPair at h
  simp only [Bool.or_eq_true, pqNot_eq, Bool.not_eq_true', Nat.blt_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem tvArr_size : tvArr.size = 693 := by
  unfold tvArr
  exact Array.size_ofFn

theorem arr_get_of {A : Array (Array Nat)} {j : Nat} (h : j < A.size) : A[j]! = A[j] :=
  getElem!_pos A j h

theorem prodCols_get (A : Array Nat) (L : List Nat) {c : Nat} (hc : c < L.length) :
    (prodCols A L.toArray)[c]! = applyCols A (L.getD c 0) := by
  unfold prodCols
  rw [List.map_toArray, getElem!_toArray]
  simp [List.getD_eq_getElem?_getD, hc]

theorem map_fld_get (C : List Nat) (j : Nat) {c : Nat} (hc : c < C.length) :
    (C.map (fld j)).getD c 0 = fld j (C.getD c 0) := by
  simp [List.getD_eq_getElem?_getD, hc]

theorem chkProd_of {P C : List Nat} (hP : uPts () = P.toArray) (hPl : P.length = 693)
    (hCl : C.length = 20) (hT : ∀ k < 693, tvCols k = (C.map (fld k)).toArray)
    (h : ∀ c < 8, pqChk C P (87 * c) 87 = true) :
    CFSG.LargeExtraspecial.S14.SMI.chkProd = true := by
  unfold CFSG.LargeExtraspecial.S14.SMI.chkProd
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < 693 := List.mem_range.1 hk
  rw [List.all_eq_true]
  intro l hl
  have hl' : l < 693 := List.mem_range.1 hl
  rcases Nat.lt_or_ge k l with hkl | hkl
  swap
  · simp [hkl]
  have hkl' : ¬ l ≤ k := by omega
  simp only [hkl', decide_false, Bool.false_or]
  have hp := pqChk_sound (h (l / 87) (by omega)) (l := l) (Nat.mul_div_le l 87)
    (by have := Nat.lt_mul_div_succ l (show 0 < 87 by norm_num); omega) (by omega) hkl
  have hnot : ∀ (a b pr : Nat), a < 20 → b < 20 →
      (pqKeySet pr P (C.getD a 0) (C.getD b 0)).testBit
        (pqKey pr (fld k (pqApply C (fld l (C.getD a 0))))
          (fld k (pqApply C (fld l (C.getD b 0))))) = false →
      tvArr.contains (prodCols (tvCols k) (tvCols l)) = false := by
    intro a b pr ha hb hK
    by_contra hc
    rw [Bool.not_eq_false, Array.contains_iff_mem, Array.mem_iff_getElem] at hc
    obtain ⟨j, hj0, hje⟩ := hc
    have hj : j < 693 := by rw [tvArr_size] at hj0; exact hj0
    have hje' : tvCols j = prodCols (tvCols k) (tvCols l) :=
      (tvArr_get hj).symm.trans ((arr_get_of hj0).trans hje)
    have hcol : ∀ c < 20, fld j (C.getD c 0) = fld k (pqApply C (fld l (C.getD c 0))) := by
      intro c hc
      have e : (tvCols j)[c]! = (prodCols (tvCols k) (tvCols l))[c]! := by rw [hje']
      rw [hT j hj, getElem!_toArray, map_fld_get C j (by omega), hT l hl',
        prodCols_get _ _ (by simpa [hCl] using hc), map_fld_get C l (by omega),
        hT k hk', applyCols_toArray, ← applyL_fld, ← pqApply_eq] at e
      exact e
    have hs := pqKeySet_sound pr P (C.getD a 0) (C.getD b 0) j (by omega)
    rw [hcol a ha, hcol b hb, hK] at hs
    exact Bool.false_ne_true hs
  rw [tvArr_get hk', tvArr_get hl']
  rcases pqPair_sound hp with h1 | h1 | h1 | h1 | h1
  · rw [hnot 0 2 65521 (by norm_num) (by norm_num) h1]
    simp
  · rw [hnot 4 8 65519 (by norm_num) (by norm_num) h1]
    simp
  · rw [hnot 10 16 65497 (by norm_num) (by norm_num) h1]
    simp
  · rw [hnot 6 12 65479 (by norm_num) (by norm_num) h1]
    simp
  · rw [hP, getElem!_toArray, getElem!_toArray]
    have h1' : (hermC (P.getD k 0) (P.getD l 0) != 0) = true :=
      bne_iff_ne.mpr (Nat.pos_iff_ne_zero.mp h1)
    rw [h1', Bool.true_or]

end CFSG.SmithE.K
