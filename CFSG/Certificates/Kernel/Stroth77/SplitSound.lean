module

public import Certificates.Data.Kernel.Stroth77.SplitK
public import CFSG.CGT.Stroth77.Section1SplitInputs

public section

namespace CFSG.KC.Stroth77SP

open Equiv Equiv.Perm CFSG.CGT.Stroth77

@[expose] def enc (a : Msp) : ℕ :=
  pk (a.vec 0).val (a.vec 1).val (a.vec 2).val (a.vec 3).val (a.vec 4).val
    (a.perm 0).val (a.perm 1).val (a.perm 2).val (a.perm 3).val (a.perm 4).val (a.perm 5).val
    (a.perm⁻¹ 0).val (a.perm⁻¹ 1).val (a.perm⁻¹ 2).val (a.perm⁻¹ 3).val (a.perm⁻¹ 4).val
    (a.perm⁻¹ 5).val

theorem pk_fields {v0 v1 v2 v3 v4 p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5 : ℕ}
    (h0 : v0 < 2) (h1 : v1 < 2) (h2 : v2 < 2) (h3 : v3 < 2) (h4 : v4 < 2)
    (g0 : p0 < 8) (g1 : p1 < 8) (g2 : p2 < 8) (g3 : p3 < 8) (g4 : p4 < 8) (g5 : p5 < 8)
    (f0 : q0 < 8) (f1 : q1 < 8) (f2 : q2 < 8) (f3 : q3 < 8) (f4 : q4 < 8) (f5 : q5 < 8) :
    let c := pk v0 v1 v2 v3 v4 p0 p1 p2 p3 p4 p5 q0 q1 q2 q3 q4 q5
    (vb c 0 = v0 ∧ vb c 1 = v1 ∧ vb c 2 = v2 ∧ vb c 3 = v3 ∧ vb c 4 = v4) ∧
      (im c 0 = p0 ∧ im c 1 = p1 ∧ im c 2 = p2 ∧ im c 3 = p3 ∧ im c 4 = p4 ∧ im c 5 = p5) ∧
      (iv c 0 = q0 ∧ iv c 1 = q1 ∧ iv c 2 = q2 ∧ iv c 3 = q3 ∧ iv c 4 = q4 ∧ iv c 5 = q5) := by
  intro c
  simp only [c, vb, im, iv, pk]
  norm_num
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> omega

theorem zval_lt (x : ZMod 2) : x.val < 2 := ZMod.val_lt x

theorem fin6_lt (x : Fin 6) : x.val < 8 := by omega

theorem enc_fields (a : Msp) :
    (vb (enc a) 0 = (a.vec 0).val ∧ vb (enc a) 1 = (a.vec 1).val ∧ vb (enc a) 2 = (a.vec 2).val ∧
      vb (enc a) 3 = (a.vec 3).val ∧ vb (enc a) 4 = (a.vec 4).val) ∧
    (im (enc a) 0 = (a.perm 0).val ∧ im (enc a) 1 = (a.perm 1).val ∧
      im (enc a) 2 = (a.perm 2).val ∧ im (enc a) 3 = (a.perm 3).val ∧
      im (enc a) 4 = (a.perm 4).val ∧ im (enc a) 5 = (a.perm 5).val) ∧
    (iv (enc a) 0 = (a.perm⁻¹ 0).val ∧ iv (enc a) 1 = (a.perm⁻¹ 1).val ∧
      iv (enc a) 2 = (a.perm⁻¹ 2).val ∧ iv (enc a) 3 = (a.perm⁻¹ 3).val ∧
      iv (enc a) 4 = (a.perm⁻¹ 4).val ∧ iv (enc a) 5 = (a.perm⁻¹ 5).val) :=
  pk_fields (zval_lt _) (zval_lt _) (zval_lt _) (zval_lt _) (zval_lt _)
    (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _)
    (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _)

theorem vb_enc (a : Msp) (i : Fin 6) : vb (enc a) i.val = (a.vec i).val := by
  obtain ⟨⟨h0, h1, h2, h3, h4⟩, -, -⟩ := enc_fields a
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · change vb (enc a) 5 = (a.vec 5).val
    rw [a.vec_five]
    rfl

theorem im_enc (a : Msp) (k : Fin 6) : im (enc a) k.val = (a.perm k).val := by
  obtain ⟨-, ⟨h0, h1, h2, h3, h4, h5⟩, -⟩ := enc_fields a
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem iv_enc (a : Msp) (k : Fin 6) : iv (enc a) k.val = (a.perm⁻¹ k).val := by
  obtain ⟨-, -, ⟨h0, h1, h2, h3, h4, h5⟩⟩ := enc_fields a
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem zval_add (x y : ZMod 2) : (x + y).val = x.val ^^^ y.val := by revert x y; decide

theorem enc_injective {a b : Msp} (h : enc a = enc b) : a = b := by
  refine Msp.ext (funext fun i => ZMod.val_injective 2 ?_) (Equiv.ext fun k => Fin.ext ?_)
  · rw [← vb_enc, ← vb_enc, h]
  · rw [← im_enc, ← im_enc, h]

theorem enc_mul (a b : Msp) : enc (a * b) = mulK (enc a) (enc b) := by
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, ⟨p0, p1, p2, p3, p4, p5⟩, ⟨q0, q1, q2, q3, q4, q5⟩⟩ :=
    enc_fields a
  obtain ⟨-, ⟨r0, r1, r2, r3, r4, r5⟩, -⟩ := enc_fields b
  simp only [mulK, mulR, mulV, a0, a1, a2, a3, a4, p0, p1, p2, p3, p4, p5, q0, q1, q2, q3, q4,
    q5, r0, r1, r2, r3, r4, r5, vb_enc, im_enc, iv_enc]
  simp only [enc, Msp.vec_mul, Msp.perm_mul, mul_inv_rev, Perm.mul_apply, nrm_apply,
    Pi.add_apply, pact_apply, a.vec_five, zero_add, zval_add]

theorem enc_inv (a : Msp) : enc a⁻¹ = invK (enc a) := by
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, ⟨p0, p1, p2, p3, p4, p5⟩, ⟨q0, q1, q2, q3, q4, q5⟩⟩ :=
    enc_fields a
  simp only [invK, invR, a0, a1, a2, a3, a4, p0, p1, p2, p3, p4, p5, q0, q1, q2, q3, q4,
    q5, vb_enc]
  simp only [enc, Msp.vec_inv, Msp.perm_inv, inv_inv, nrm_apply, pact_apply, zval_add]

theorem im_eq_permOf (c : ℕ) (k : Fin 6) : im c k.val = permOf c / 8 ^ k.val % 8 := by
  fin_cases k <;> simp only [im, permOf] <;> norm_num <;> omega

theorem perm_eq_of_permOf {a b : Msp} (h : permOf (enc a) = permOf (enc b)) : a.perm = b.perm :=
  Equiv.ext fun k => Fin.ext (by rw [← im_enc, ← im_enc, im_eq_permOf, im_eq_permOf, h])

theorem permOf_eq_of_perm {a b : Msp} (h : a.perm = b.perm) : permOf (enc a) = permOf (enc b) := by
  have a0 := zval_lt (a.vec 0)
  have a1 := zval_lt (a.vec 1)
  have a2 := zval_lt (a.vec 2)
  have a3 := zval_lt (a.vec 3)
  have a4 := zval_lt (a.vec 4)
  have b0 := zval_lt (b.vec 0)
  have b1 := zval_lt (b.vec 1)
  have b2 := zval_lt (b.vec 2)
  have b3 := zval_lt (b.vec 3)
  have b4 := zval_lt (b.vec 4)
  simp only [permOf, enc, pk, h]
  omega

theorem enc_one : enc 1 = oneK := by decide +kernel
theorem enc_spX1 : enc spX1 = x1K := by decide +kernel
theorem enc_spY1 : enc spY1 = y1K := by decide +kernel
theorem enc_spUV : enc spUV = uvK := by decide +kernel
theorem enc_spT : enc spT = tK0 := by decide +kernel
theorem enc_spX : enc spX = xK := by decide +kernel
theorem enc_spY : enc spY = yK := by decide +kernel
theorem enc_spU : enc spU = uK := by decide +kernel
theorem enc_spW : enc spW = wK := by decide +kernel
theorem enc_spM1 : enc spM1 = m1K := by decide +kernel
theorem enc_spM2 : enc spM2 = m2K := by decide +kernel
theorem enc_spRho : enc spRho = rhoK := by decide +kernel

@[expose] def ePhi (r : ℕ) : Msp :=
  (if r.testBit 0 then spX1 else 1) * (if r.testBit 1 then spY1 else 1) *
    (if r.testBit 2 then spUV else 1) * (if r.testBit 3 then spT else 1)

@[expose] def pPhi (r : ℕ) : Msp :=
  (if r.testBit 0 then spX else 1) * (if r.testBit 1 then spY else 1) *
    (if r.testBit 2 then spU else 1) * (if r.testBit 3 then spW else 1)

theorem enc_ite (p : Prop) [Decidable p] (a : Msp) (c : ℕ) (h : enc a = c) :
    enc (if p then a else 1) = if p then c else oneK := by
  split
  · exact h
  · exact enc_one

theorem enc_ePhi (r : ℕ) : enc (ePhi r) = eK r := by
  simp only [ePhi, eK, selK, enc_mul, enc_ite _ _ _ enc_spX1, enc_ite _ _ _ enc_spY1,
    enc_ite _ _ _ enc_spUV, enc_ite _ _ _ enc_spT]

theorem enc_pPhi (r : ℕ) : enc (pPhi r) = pK r := by
  simp only [pPhi, pK, selK, enc_mul, enc_ite _ _ _ enc_spX, enc_ite _ _ _ enc_spY,
    enc_ite _ _ _ enc_spU, enc_ite _ _ _ enc_spW]

end CFSG.KC.Stroth77SP
