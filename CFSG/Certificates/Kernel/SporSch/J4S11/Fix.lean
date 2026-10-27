module

public import Certificates.Data.Kernel.SporSch.J4S11
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Certificates.Kernel.SporSch.J4SFormSound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.SporSch.J4E.FixPf

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ
open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : CFSG.KC.J4Q.strictB y k = k y := by
  cases y <;> rfl

private theorem andB_true' {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

private theorem row_lt'' {X : Array Nat} (hX : WfN X) (i : Nat) : X[i]?.getD 0 < 2 ^ 112 := by
  by_cases h : i < X.size
  · have := hX.2 i (hX.1 ▸ h)
    rw [getElem!_pos X i h] at this
    rwa [getElem?_pos X i h, Option.getD_some]
  · rw [getElem?_neg X i h, Option.getD_none]
    exact Nat.two_pow_pos _

private theorem rowJ_eq {X : Array Nat} (hX : WfN X) {i : Nat} (hi : i < 112) :
    rowJ (2 ^ 112 - 1) (encN X) i = X[i]?.getD 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  change ((encN X >>> (i * 128)) &&& (2 ^ 112 - 1)).testBit q = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, encN_bit hX]
  by_cases hq : q < 112
  · have e1 : (i * 128 + q) / 128 = i := by omega
    have e2 : (i * 128 + q) % 128 = q := by omega
    simp [hq, e1, e2, hi]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (row_lt'' hX i)
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    simp [hq]

private theorem dRows_row (k : Nat) {i : Nat} (hi : i < 112) :
    (dRows k)[i]?.getD 0 = if i < k then 0 else 2 ^ i := by
  simp [dRows, hi, Nat.one_shiftLeft]

private theorem wf_of_rows' {X : Array Nat} (hs : X.size = 112)
    (h : ∀ i < 112, X[i]?.getD 0 < 2 ^ 112) : WfN X := ⟨hs, fun i hi => by
  have := h i hi
  rwa [getElem?_pos X i (hs ▸ hi), Option.getD_some, ← getElem!_pos X i (hs ▸ hi)] at this⟩

private theorem wf_dRows (k : Nat) : WfN (dRows k) := by
  have hsz : (dRows k).size = 112 := by simp only [dRows, Array.size_ofFn]
  refine wf_of_rows' hsz fun i hi => ?_
  rw [dRows_row k hi]
  split
  · exact Nat.two_pow_pos _
  · exact Nat.pow_lt_pow_right (by omega) hi

private theorem idRows_row {i : Nat} (hi : i < 112) : (idRows 112)[i]?.getD 0 = 2 ^ i := by
  simp [idRows, hi, Nat.one_shiftLeft]

private theorem dK_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (k : Nat) :
    encN (dRows k) = dK one k := by
  have hid := J4B.id_enc hK
  apply Nat.eq_of_testBit_eq
  intro p
  rw [encN_bit (wf_dRows k)]
  unfold dK
  change _ = ((one >>> (128 * k)) <<< (128 * k)).testBit p
  rw [Nat.testBit_shiftLeft, Nat.testBit_shiftRight, ← hid.2, encN_bit hid.1]
  by_cases h2 : 128 * k ≤ p
  · have e : 128 * k + (p - 128 * k) = p := by omega
    rw [e]
    by_cases hp : p / 128 < 112
    · have hk : k ≤ p / 128 := by omega
      rw [dRows_row k hp, idRows_row hp, if_neg (by omega)]
      simp [hp, h2]
    · simp [hp, h2]
  · by_cases hp : p / 128 < 112
    · rw [dRows_row k hp, if_pos (by omega)]
      simp [h2]
    · simp [hp, h2]

theorem fixK_sound' (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {G P Pi R : Array Nat}
    (hG : WfN G) (hP : WfN P) (hPi : WfN Pi) (hR : WfN R)
    {k : Nat} (hk : k ≤ 112)
    (h : fixK c rm one (encN G) (encN P) (encN Pi) (encN R) k = true) :
    fixDimOK G P Pi R k = true := by
  have hid := J4B.id_enc hK
  have hrm := (consts_c hK).2
  have hx := J4B.xor_enc hG hid.1
  have hT := J4B.mulRows_enc hK hP hx.1
  unfold fixK at h
  simp only [strictB_eq'] at h
  obtain ⟨h1, h⟩ := andB_true' h
  obtain ⟨h2, h⟩ := andB_true' h
  obtain ⟨h3, h4⟩ := andB_true' h
  have hT' : encN (mulRows 112 P (xorRows112 G (idRows 112))) =
      mulJ c rm (encN P) (Nat.xor (encN G) one) := by
    rw [hT.2, hx.2, hid.2]
  have e1 : mulRows 112 P Pi = idRows 112 := by
    have m := J4B.mulRows_enc hK hP hPi
    exact J4B.enc_inj m.1 hid.1 (by rw [m.2, hid.2]; exact Nat.eq_of_beq_eq_true h1)
  have e2 : mulRows 112 Pi P = idRows 112 := by
    have m := J4B.mulRows_enc hK hPi hP
    exact J4B.enc_inj m.1 hid.1 (by rw [m.2, hid.2]; exact Nat.eq_of_beq_eq_true h2)
  have e4 : mulRows 112 (mulRows 112 P (xorRows112 G (idRows 112))) R = dRows k := by
    have m := J4B.mulRows_enc hK hT.1 hR
    refine J4B.enc_inj m.1 (wf_dRows k) ?_
    rw [m.2, dK_enc hK, hT']
    exact Nat.eq_of_beq_eq_true h4
  have e3 : ∀ i < k, (mulRows 112 P (xorRows112 G (idRows 112)))[i]?.getD 0 = 0 := by
    intro i hi
    have h0 := Nat.eq_of_beq_eq_true (allN_spec h3 i hi)
    rw [← hT', hrm, rowJ_eq hT.1 (by omega)] at h0
    exact h0
  unfold fixDimOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨⟨e1, e2⟩, fun i hi => by rw [e3 i hi]⟩, e4⟩

end CFSG.KS.SporSch.J4E.FixPf

end
