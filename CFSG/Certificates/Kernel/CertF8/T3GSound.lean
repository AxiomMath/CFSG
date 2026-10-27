module

public import Certificates.Data.Kernel.CertF8.T3G
public import CFSG.Certificates.Kernel.G28.T3Sound

public section

namespace CFSG.KC.CertF8.T3G

open CFSG.KC.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

section Monoid

variable {M : Type*} [Monoid M]

structure RelsG (p q r v : ℕ) (U Z O : M) : Prop where
  u9 : U ^ 9 = 1
  z9 : Z ^ 9 = 1
  o3 : O ^ 3 = 1
  uz : U * Z = Z * U
  ou : O * U = U ^ p * Z ^ q * O
  oz : O * Z = U ^ r * Z ^ v * O

variable {p q r v : ℕ} {U Z O : M} (R : RelsG p q r v U Z O)
include R

theorem E_mulG (a b c d : ℕ) : U ^ a * Z ^ b * (U ^ c * Z ^ d) = U ^ (a + c) * Z ^ (b + d) := by
  have h : Z ^ b * U ^ c = U ^ c * Z ^ b := (Commute.pow_pow (R.uz : Commute U Z).symm b c).eq
  calc U ^ a * Z ^ b * (U ^ c * Z ^ d) = U ^ a * (Z ^ b * U ^ c) * Z ^ d := by
        simp only [mul_assoc]
    _ = U ^ a * (U ^ c * Z ^ b) * Z ^ d := by rw [h]
    _ = U ^ (a + c) * Z ^ (b + d) := by
        rw [pow_add, pow_add]
        simp only [mul_assoc]

theorem E_modG (a b : ℕ) : U ^ a * Z ^ b = U ^ (a % 9) * Z ^ (b % 9) := by
  rw [pow_mod_of R.u9 a, pow_mod_of R.z9 b]

theorem O_UG (a : ℕ) : O * U ^ a = U ^ (p * a) * Z ^ (q * a) * O := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc O * U ^ (a + 1) = O * U ^ a * U := by rw [pow_succ, mul_assoc]
      _ = U ^ (p * a) * Z ^ (q * a) * (O * U) := by
          rw [ih]
          simp only [mul_assoc]
      _ = U ^ (p * a) * Z ^ (q * a) * (U ^ p * Z ^ q) * O := by
          rw [R.ou]
          simp only [mul_assoc]
      _ = U ^ (p * (a + 1)) * Z ^ (q * (a + 1)) * O := by
          rw [E_mulG R, mul_add, mul_add, mul_one, mul_one]

theorem O_ZG (b : ℕ) : O * Z ^ b = U ^ (r * b) * Z ^ (v * b) * O := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc O * Z ^ (b + 1) = O * Z ^ b * Z := by rw [pow_succ, mul_assoc]
      _ = U ^ (r * b) * Z ^ (v * b) * (O * Z) := by
          rw [ih]
          simp only [mul_assoc]
      _ = U ^ (r * b) * Z ^ (v * b) * (U ^ r * Z ^ v) * O := by
          rw [R.oz]
          simp only [mul_assoc]
      _ = U ^ (r * (b + 1)) * Z ^ (v * (b + 1)) * O := by
          rw [E_mulG R, mul_add, mul_add, mul_one, mul_one]

theorem O_EG (e : ℕ × ℕ) :
    O * (U ^ e.1 * Z ^ e.2) = U ^ (ph1 p q r v e).1 * Z ^ (ph1 p q r v e).2 * O := by
  calc O * (U ^ e.1 * Z ^ e.2) = O * U ^ e.1 * Z ^ e.2 := by rw [mul_assoc]
    _ = U ^ (p * e.1) * Z ^ (q * e.1) * (O * Z ^ e.2) := by
        rw [O_UG R]
        simp only [mul_assoc]
    _ = U ^ (p * e.1) * Z ^ (q * e.1) * (U ^ (r * e.2) * Z ^ (v * e.2)) * O := by
        rw [O_ZG R]
        simp only [mul_assoc]
    _ = _ := by
        rw [E_mulG R, E_modG R]
        rfl

theorem Opow_EG (c : ℕ) (e : ℕ × ℕ) :
    O ^ c * (U ^ e.1 * Z ^ e.2) =
      U ^ (phG p q r v c e).1 * Z ^ (phG p q r v c e).2 * O ^ c := by
  induction c with
  | zero => simp [phG]
  | succ c ih =>
    calc O ^ (c + 1) * (U ^ e.1 * Z ^ e.2) = O * (O ^ c * (U ^ e.1 * Z ^ e.2)) := by
          rw [pow_succ', mul_assoc]
      _ = O * (U ^ (phG p q r v c e).1 * Z ^ (phG p q r v c e).2) * O ^ c := by
          rw [ih]
          simp only [mul_assoc]
      _ = U ^ (ph1 p q r v (phG p q r v c e)).1 * Z ^ (ph1 p q r v (phG p q r v c e)).2 * O *
            O ^ c := by rw [O_EG R]
      _ = _ := by
          rw [pow_succ' O c, ← mul_assoc]
          rfl

theorem fT_pcIdxG (a b c : ℕ) : fT U Z O (pcIdx a b c) = U ^ a * Z ^ b * O ^ c := by
  have e1 : pcIdx a b c / 27 = a % 9 := by
    unfold pcIdx
    omega
  have e2 : pcIdx a b c / 3 % 9 = b % 9 := by
    unfold pcIdx
    omega
  have e3 : pcIdx a b c % 3 = c % 3 := by
    unfold pcIdx
    omega
  rw [fT, e1, e2, e3, ← E_modG R, ← pow_mod_of R.o3]

theorem fTG_mul (s t : ℕ) : fT U Z O s * fT U Z O t = fT U Z O (pcMulG p q r v s t) := by
  rw [pcMulG, fT_pcIdxG R, fT, fT, pow_add O]
  have h := Opow_EG R (s % 3) (t / 27, t / 3 % 9)
  calc U ^ (s / 27) * Z ^ (s / 3 % 9) * O ^ (s % 3) * (U ^ (t / 27) * Z ^ (t / 3 % 9) * O ^ (t % 3))
        = U ^ (s / 27) * Z ^ (s / 3 % 9) * (O ^ (s % 3) * (U ^ (t / 27) * Z ^ (t / 3 % 9))) *
          O ^ (t % 3) := by simp only [mul_assoc]
    _ = U ^ (s / 27) * Z ^ (s / 3 % 9) *
          (U ^ (phG p q r v (s % 3) (t / 27, t / 3 % 9)).1 *
            Z ^ (phG p q r v (s % 3) (t / 27, t / 3 % 9)).2) *
          (O ^ (s % 3) * O ^ (t % 3)) := by
        rw [h]
        simp only [mul_assoc]
    _ = _ := by rw [E_mulG R]

theorem fTG_pw (a n : ℕ) : fT U Z O (pwG p q r v a n) = fT U Z O a ^ n := by
  induction n with
  | zero =>
    change fT U Z O 0 = _
    rw [pow_zero]
    exact fT_zero
  | succ n ih =>
    change fT U Z O (pcMulG p q r v (pwG p q r v a n) a) = _
    rw [← fTG_mul R, ih, pow_succ]

end Monoid

theorem pcMulG_lt (p q r v s t : ℕ) : pcMulG p q r v s t < 243 := pcIdx_lt _ _ _

theorem pwG_lt (p q r v a n : ℕ) : pwG p q r v a n < 243 := by
  cases n with
  | zero => change 0 < 243; norm_num
  | succ n => exact pcMulG_lt _ _ _ _ _ _

theorem relsG_of {p q r v : ℕ} {Uc Zc Oc : Array ℕ} (hU : Valid Uc) (hZ : Valid Zc)
    (hO : Valid Oc) (h : relG p q r v (codeP Uc) (codeP Zc) (codeP Oc) = true) :
    RelsG p q r v (decode Uc) (decode Zc) (decode Oc) := by
  simp only [relG, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hUp := valid_powCode hU p
  have hUr := valid_powCode hU r
  have hZq := valid_powCode hZ q
  have hZv := valid_powCode hZ v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := congrArg decode (eq_of_beq_codeP (valid_powCode hU 9) valid_idCode
      (codeP_powCode hU 9) codeP_idCode h1)
    rwa [decode_powCode hU, decode_idCode] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_powCode hZ 9) valid_idCode
      (codeP_powCode hZ 9) codeP_idCode h2)
    rwa [decode_powCode hZ, decode_idCode] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_powCode hO 3) valid_idCode
      (codeP_powCode hO 3) codeP_idCode h3)
    rwa [decode_powCode hO, decode_idCode] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_mulCode hU hZ) (valid_mulCode hZ hU)
      (codeP_mulCode hU hZ) (codeP_mulCode hZ hU) h4)
    rwa [decode_mulCode hU hZ, decode_mulCode hZ hU] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_mulCode hO hU)
      (valid_mulCode (valid_mulCode hUp hZq) hO) (codeP_mulCode hO hU)
      (by rw [codeP_mulCode (valid_mulCode hUp hZq) hO, codeP_mulCode hUp hZq, codeP_powCode hU,
        codeP_powCode hZ]) h5)
    rwa [decode_mulCode hO hU, decode_mulCode (valid_mulCode hUp hZq) hO, decode_mulCode hUp hZq,
      decode_powCode hU, decode_powCode hZ] at this
  · have := congrArg decode (eq_of_beq_codeP (valid_mulCode hO hZ)
      (valid_mulCode (valid_mulCode hUr hZv) hO) (codeP_mulCode hO hZ)
      (by rw [codeP_mulCode (valid_mulCode hUr hZv) hO, codeP_mulCode hUr hZv, codeP_powCode hU,
        codeP_powCode hZ]) h6)
    rwa [decode_mulCode hO hZ, decode_mulCode (valid_mulCode hUr hZv) hO, decode_mulCode hUr hZv,
      decode_powCode hU, decode_powCode hZ] at this

end CFSG.KC.CertF8.T3G

end
