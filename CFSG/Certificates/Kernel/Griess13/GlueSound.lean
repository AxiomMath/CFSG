module

public import Certificates.Data.Kernel.Griess13.Glue
public import CFSG.Certificates.Kernel.Griess13.PackedSound
import CFSG.Certificates.Kernel.Co1BInvSound

public section

namespace CFSG.KC.G13

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.Monster.GMS.Griess13.Co1Data CFSG.Sporadic.SmallF2.Native

theorem getD_unpackR (X : Nat) {k : Nat} (hk : k < 24) :
    (unpackR 24 X)[k]?.getD 0 = X / 2 ^ (24 * k) % 2 ^ 24 := by
  simp [unpackR, hk]

theorem ofBits_eq_ofBitsR (f : Nat → Bool) : ∀ d, ofBits d f = ofBitsR d f
  | 0 => rfl
  | d + 1 => by
    have h : ofBits (d + 1) f = if f d = true then ofBits d f ||| 1 <<< d else ofBits d f := by
      simp only [ofBits, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h, ofBits_eq_ofBitsR f d]
    change (if f d = true then ofBitsR d f ||| 1 <<< d else ofBitsR d f) =
      Bool.rec (motive := fun _ => Nat) (ofBitsR d f) (Nat.lor (ofBitsR d f) (Nat.shiftLeft 1 d)) (f d)
    cases f d <;> rfl

theorem eqMask_unpackR (X : Nat) {i j : Nat} (hi : i < 24) (hj : j < 24) :
    eqMask (unpackR 24 X) i j = eqMaskK X i j := by
  have hf : eqCoeff (unpackR 24 X) i j = fun a => ((a / 24 == i) && X.testBit (24 * (a % 24) + j)) !=
      ((a % 24 == j) && (decide (a / 24 < 24) && X.testBit (24 * i + a / 24))) := by
    funext a
    unfold eqCoeff
    rw [getD_unpackR X (Nat.mod_lt _ (by norm_num)), getD_unpackR X hi, testBit_field, testBit_field]
    simp [hj]
  unfold eqMask eqMaskK
  rw [hf, ofBits_eq_ofBitsR]

theorem eqsOf_map_unpackR {Xs E : List Nat} (hlen : Xs.length = 3) (hE : E.length = 1728)
    (h : ∀ r < 1728, eqMaskK (Xs.getD (r / 576) 0) (r % 576 / 24) (r % 24) = E.getD r 0) :
    eqsOf (Xs.map (unpackR 24)) = E.toArray := by
  apply Array.ext
  · simp [eqsOf, hE]
  · intro r h1 h2
    have hr : r < 1728 := by simpa [eqsOf] using h1
    have hq : r / 576 < Xs.length := by omega
    simp only [eqsOf, Array.getElem_ofFn, List.getElem_toArray]
    unfold eqAt
    rw [List.getD_eq_getElem _ _ (by simpa using hq), List.getElem_map,
      eqMask_unpackR _ (by omega) (Nat.mod_lt _ (by norm_num)), ← List.getD_eq_getElem _ 0 hq,
      h r hr, List.getD_eq_getElem _ _ (by omega)]

theorem foldXor_toArray_aux (μ : Nat) (E : List Nat) :
    ∀ (L : List Nat) (k acc : Nat), L = E.drop k →
      (List.range' k L.length).foldl
        (fun acc r => if μ.testBit r then acc ^^^ E.toArray[r]! else acc) acc =
      foldXorL μ L k acc
  | [], _, _, _ => rfl
  | e :: L, k, acc, hL => by
    have he : E.toArray[k]! = e := by
      have h0 : (E.drop k)[0]? = some e := by rw [← hL]; rfl
      rw [List.getElem?_drop, Nat.add_zero] at h0
      rw [getElem!_def, List.getElem?_toArray, h0]
    have hL' : L = E.drop (k + 1) := by
      rw [← List.drop_drop, ← hL]
      rfl
    rw [List.length_cons, List.range'_succ, List.foldl_cons, he,
      foldXor_toArray_aux μ E L (k + 1) _ hL']
    change _ = foldXorL μ L (k + 1) (Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc e) (Nat.testBit μ k))
    cases μ.testBit k <;> rfl

theorem foldXor_toArray (E : List Nat) (μ : Nat) : foldXor E.toArray μ = foldXorL μ E 0 0 := by
  unfold foldXor
  rw [List.size_toArray, List.range_eq_range']
  exact foldXor_toArray_aux μ E E 0 0 List.drop_zero.symm

theorem spanCheckWith_toArray (E : List Nat) (fmask : Nat) (cert : Nat → Nat × Nat) :
    spanCheckWith E.toArray fmask cert = spanCheckL E fmask cert := by
  simp only [spanCheckWith, spanCheckL, verifyCert, foldXor_toArray]

theorem field_xor (k x y : Nat) :
    (x ^^^ y) / 2 ^ k % 2 ^ 24 = (x / 2 ^ k % 2 ^ 24) ^^^ (y / 2 ^ k % 2 ^ 24) := by
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_xor]
  cases decide (b < 24) <;> simp

theorem comboRows_eq {T : List Nat} (hT : ∀ i < 8, trows i = unpackR 24 (T.getD i 0))
    (c : Fin 8 → ZMod 2) : comboRows c = unpackR 24 (comboK T c) := by
  unfold comboRows comboK
  conv_rhs => unfold unpackR
  congr 1
  funext a
  let f : Nat → Nat := fun x => x / 2 ^ (24 * a.val) % 2 ^ 24
  have H : ∀ (x : Nat) (i : Nat),
      (if cF c i = 1 then f x ^^^ ((trows i)[a.val]?.getD 0) else f x) =
        f (if cF c i = 1 then x ^^^ T.getD i 0 else x) := by
    intro x i
    by_cases hi : i < 8
    · rw [hT i hi, getD_unpackR _ a.isLt]
      split_ifs
      · exact (field_xor _ _ _).symm
      · rfl
    · have h0 : cF c i = 0 := by simp [cF, hi]
      simp [h0]
  have := List.foldl_hom (l := List.range 8) (init := 0)
    (g₁ := fun x i => if cF c i = 1 then x ^^^ T.getD i 0 else x)
    (g₂ := fun x i => if cF c i = 1 then x ^^^ ((trows i)[a.val]?.getD 0) else x) f H
  have h0 : f 0 = 0 := by simp [f]
  rw [h0] at this
  exact this

theorem powRows_unpackR (a : Nat) : ∀ n, powRows 24 (unpackR 24 a) n = unpackR 24 (powW a n)
  | 0 => CFSG.KC.F2W.unpackR_idF.symm
  | n + 1 => by
    change mulRows 24 (powRows 24 (unpackR 24 a) n) (unpackR 24 a) = unpackR 24 (mulWK (powW a n) a)
    rw [powRows_unpackR a n, mulWK_unpack]

theorem idRows_eq : idRows 24 = unpackR 24 oneK := CFSG.KC.F2W.unpackR_idF.symm

theorem eqRows_unpackR (a b : Nat) : eqRows (unpackR 24 a) (unpackR 24 b) = eqK a b :=
  toPR_eq a b

end CFSG.KC.G13

end
