module

public import Certificates.Data.Kernel.Stroth77.MnsK
public import CFSG.Certificates.Kernel.Stroth77.SplitSound
public import CFSG.CGT.Stroth77.NonSplit.StrothTInputs

public section

namespace CFSG.KC.Stroth77MN

open Equiv Equiv.Perm CFSG.CGT.Stroth77
open CFSG.KC.Stroth77SP (vb im iv pk mulK invK permOf conjK selK pk_fields zval_lt fin6_lt
  zval_add im_eq_permOf)

@[expose] def encN (a : Mns) : ℕ :=
  pk (a.vec 0).val (a.vec 1).val (a.vec 2).val (a.vec 3).val (a.vec 4).val
    (a.perm 0).val (a.perm 1).val (a.perm 2).val (a.perm 3).val (a.perm 4).val (a.perm 5).val
    (a.perm⁻¹ 0).val (a.perm⁻¹ 1).val (a.perm⁻¹ 2).val (a.perm⁻¹ 3).val (a.perm⁻¹ 4).val
    (a.perm⁻¹ 5).val

theorem encN_fields (a : Mns) :
    (vb (encN a) 0 = (a.vec 0).val ∧ vb (encN a) 1 = (a.vec 1).val ∧
      vb (encN a) 2 = (a.vec 2).val ∧ vb (encN a) 3 = (a.vec 3).val ∧
      vb (encN a) 4 = (a.vec 4).val) ∧
    (im (encN a) 0 = (a.perm 0).val ∧ im (encN a) 1 = (a.perm 1).val ∧
      im (encN a) 2 = (a.perm 2).val ∧ im (encN a) 3 = (a.perm 3).val ∧
      im (encN a) 4 = (a.perm 4).val ∧ im (encN a) 5 = (a.perm 5).val) ∧
    (iv (encN a) 0 = (a.perm⁻¹ 0).val ∧ iv (encN a) 1 = (a.perm⁻¹ 1).val ∧
      iv (encN a) 2 = (a.perm⁻¹ 2).val ∧ iv (encN a) 3 = (a.perm⁻¹ 3).val ∧
      iv (encN a) 4 = (a.perm⁻¹ 4).val ∧ iv (encN a) 5 = (a.perm⁻¹ 5).val) :=
  pk_fields (zval_lt _) (zval_lt _) (zval_lt _) (zval_lt _) (zval_lt _)
    (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _)
    (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _) (fin6_lt _)

theorem vb_encN (a : Mns) (i : Fin 6) : vb (encN a) i.val = (a.vec i).val := by
  obtain ⟨⟨h0, h1, h2, h3, h4⟩, -, -⟩ := encN_fields a
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · change vb (encN a) 5 = (a.vec 5).val
    rw [a.vec_five]
    rfl

theorem im_encN (a : Mns) (k : Fin 6) : im (encN a) k.val = (a.perm k).val := by
  obtain ⟨-, ⟨h0, h1, h2, h3, h4, h5⟩, -⟩ := encN_fields a
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem iv_encN (a : Mns) (k : Fin 6) : iv (encN a) k.val = (a.perm⁻¹ k).val := by
  obtain ⟨-, -, ⟨h0, h1, h2, h3, h4, h5⟩⟩ := encN_fields a
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem encN_injective {a b : Mns} (h : encN a = encN b) : a = b := by
  refine Mns.ext (funext fun i => ZMod.val_injective 2 ?_) (Equiv.ext fun k => Fin.ext ?_)
  · rw [← vb_encN, ← vb_encN, h]
  · rw [← im_encN, ← im_encN, h]

theorem encN_mul (a b : Mns) : encN (a * b) = mulK (encN a) (encN b) := by
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, ⟨p0, p1, p2, p3, p4, p5⟩, ⟨q0, q1, q2, q3, q4, q5⟩⟩ :=
    encN_fields a
  obtain ⟨-, ⟨r0, r1, r2, r3, r4, r5⟩, -⟩ := encN_fields b
  simp only [mulK, Stroth77SP.mulR, Stroth77SP.mulV, a0, a1, a2, a3, a4, p0, p1, p2, p3, p4, p5,
    q0, q1, q2, q3, q4, q5, r0, r1, r2, r3, r4, r5, vb_encN, im_encN, iv_encN]
  simp only [encN, Mns.vec_mul, Mns.perm_mul, mul_inv_rev, Perm.mul_apply, nrm_apply,
    Pi.add_apply, pact_apply, a.vec_five, zero_add, zval_add]

theorem encN_inv (a : Mns) : encN a⁻¹ = invK (encN a) := by
  obtain ⟨⟨a0, a1, a2, a3, a4⟩, ⟨p0, p1, p2, p3, p4, p5⟩, ⟨q0, q1, q2, q3, q4, q5⟩⟩ :=
    encN_fields a
  simp only [invK, Stroth77SP.invR, a0, a1, a2, a3, a4, p0, p1, p2, p3, p4, p5, q0, q1, q2, q3,
    q4, q5, vb_encN]
  simp only [encN, Mns.vec_inv, Mns.perm_inv, inv_inv, nrm_apply, pact_apply, zval_add]

theorem conjK_encN (a b : Mns) : conjK (encN a) (encN b) = encN (a * b * a⁻¹) := by
  rw [conjK, encN_mul, encN_mul, encN_inv]

theorem perm_eq_of_permOf {a b : Mns} (h : permOf (encN a) = permOf (encN b)) :
    a.perm = b.perm :=
  Equiv.ext fun k => Fin.ext (by rw [← im_encN, ← im_encN, im_eq_permOf, im_eq_permOf, h])

theorem permOf_eq_of_perm {a b : Mns} (h : a.perm = b.perm) :
    permOf (encN a) = permOf (encN b) := by
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
  simp only [permOf, encN, pk, h]
  omega

theorem imCode_encN (a : Mns) :
    imCode (encN a) = tc (a.perm 0).val (a.perm 1).val (a.perm 2).val (a.perm 3).val
      (a.perm 4).val (a.perm 5).val := by
  have a0 := zval_lt (a.vec 0)
  have a1 := zval_lt (a.vec 1)
  have a2 := zval_lt (a.vec 2)
  have a3 := zval_lt (a.vec 3)
  have a4 := zval_lt (a.vec 4)
  have p0 := fin6_lt (a.perm 0)
  have p1 := fin6_lt (a.perm 1)
  have p2 := fin6_lt (a.perm 2)
  have p3 := fin6_lt (a.perm 3)
  have p4 := fin6_lt (a.perm 4)
  have p5 := fin6_lt (a.perm 5)
  simp only [imCode, tc, encN, pk]
  omega

theorem encN_one : encN 1 = oneK := by decide +kernel
theorem encN_mnsX1 : encN mnsX1 = x1K := by decide +kernel
theorem encN_mnsY1 : encN mnsY1 = y1K := by decide +kernel
theorem encN_mnsUV : encN mnsUV = uvK := by decide +kernel
theorem encN_mnsT : encN mnsT = tK0 := by decide +kernel
theorem encN_mnsX : encN mnsX = xK := by decide +kernel
theorem encN_mnsY : encN mnsY = yK := by decide +kernel
theorem encN_mnsU : encN mnsU = uK := by decide +kernel
theorem encN_mnsW : encN mnsW = wK := by decide +kernel
theorem encN_mnsRho : encN mnsRho = rhoK := by decide +kernel

@[expose] def ePhiN (r : ℕ) : Mns :=
  (if r.testBit 0 then mnsX1 else 1) * (if r.testBit 1 then mnsY1 else 1) *
    (if r.testBit 2 then mnsUV else 1) * (if r.testBit 3 then mnsT else 1)

@[expose] def pPhiN (r : ℕ) : Mns :=
  (if r.testBit 0 then mnsX else 1) * (if r.testBit 1 then mnsY else 1) *
    (if r.testBit 2 then mnsU else 1) * (if r.testBit 3 then mnsW else 1)

theorem encN_ite (p : Prop) [Decidable p] (a : Mns) (c : ℕ) (h : encN a = c) :
    encN (if p then a else 1) = if p then c else oneK := by
  split
  · exact h
  · exact encN_one

theorem encN_ePhiN (r : ℕ) : encN (ePhiN r) = eK r := by
  simp only [ePhiN, eK, selK, encN_mul, encN_ite _ _ _ encN_mnsX1, encN_ite _ _ _ encN_mnsY1,
    encN_ite _ _ _ encN_mnsUV, encN_ite _ _ _ encN_mnsT]

theorem encN_pPhiN (r : ℕ) : encN (pPhiN r) = pK r := by
  simp only [pPhiN, pK, selK, encN_mul, encN_ite _ _ _ encN_mnsX, encN_ite _ _ _ encN_mnsY,
    encN_ite _ _ _ encN_mnsU, encN_ite _ _ _ encN_mnsW]

end CFSG.KC.Stroth77MN
