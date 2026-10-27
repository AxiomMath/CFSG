module

public import CFSG.ClassicalInvolution.Phan.PhanS19Q7Inputs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Phan.PhanS19Gf
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std

@[expose] def gfDec (n : Nat) : GF49 := ⟨((n % 7 : Nat) : ZMod 7), ((n / 7 : Nat) : ZMod 7)⟩

theorem gfDec_re (n : Nat) : (gfDec n).re = (n : ZMod 7) := by
  simp [gfDec, ZMod.natCast_mod]

theorem gfDec_im (n : Nat) : (gfDec n).im = ((n / 7 : Nat) : ZMod 7) := rfl

theorem gfDec_mk (p q : Nat) : gfDec (p % 7 + 7 * (q % 7)) = ⟨(p : ZMod 7), (q : ZMod 7)⟩ := by
  have h1 : (p % 7 + 7 * (q % 7)) % 7 = p % 7 := by omega
  have h2 : (p % 7 + 7 * (q % 7)) / 7 = q % 7 := by omega
  apply QuadraticAlgebra.ext
  · show ((((p % 7 + 7 * (q % 7)) % 7 : Nat)) : ZMod 7) = (p : ZMod 7)
    rw [h1, ZMod.natCast_mod]
  · rw [gfDec_im, h2, ZMod.natCast_mod]

theorem gfDec_zero : gfDec 0 = 0 := by decide

theorem gfDec_one : gfDec 1 = 1 := by decide

theorem gfDec_kappa : gfDec gfKappa = -2 := by decide

theorem seven_eq_zero : (7 : ZMod 7) = 0 := by decide

theorem six_eq_neg_one : (6 : ZMod 7) = -1 := by decide

theorem natCast_mod_seven (n : Nat) : ((n % 7 : Nat) : ZMod 7) = (n : ZMod 7) :=
  ZMod.natCast_mod n 7

theorem gfDec_add (a b : Nat) : gfDec (gfAdd a b) = gfDec a + gfDec b := by
  unfold gfAdd
  rw [gfDec_mk]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_add, gfDec_re]
    push_cast
    simp only [natCast_mod_seven]
  · simp only [QuadraticAlgebra.im_add, gfDec_im]
    push_cast
    rfl

theorem gfDec_mul (a b : Nat) : gfDec (gfMul a b) = gfDec a * gfDec b := by
  unfold gfMul
  rw [gfDec_mk]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, gfDec_re, gfDec_im]
    push_cast
    rw [six_eq_neg_one]
    simp only [natCast_mod_seven]
    ring
  · simp only [QuadraticAlgebra.im_mul, gfDec_re, gfDec_im]
    push_cast
    simp only [natCast_mod_seven]
    ring

theorem gfDec_neg (a : Nat) : gfDec (gfNeg a) = -gfDec a := by
  unfold gfNeg
  rw [gfDec_mk]
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_neg, gfDec_re]
    rw [Nat.cast_sub (Nat.mod_lt _ (by norm_num)).le]
    simp [seven_eq_zero]
  · simp only [QuadraticAlgebra.im_neg, gfDec_im]
    rw [Nat.cast_sub (Nat.mod_lt _ (by norm_num)).le]
    simp [seven_eq_zero]

theorem gfDec_conj (a : Nat) : gfDec (gfConj a) = star (gfDec a) := by
  unfold gfConj
  rw [gfDec_mk]
  apply QuadraticAlgebra.ext
  · rw [QuadraticAlgebra.re_star, gfDec_re]
    simp
  · rw [QuadraticAlgebra.im_star, gfDec_im]
    rw [Nat.cast_sub (Nat.mod_lt _ (by norm_num)).le]
    simp [seven_eq_zero]

theorem mk_lt (p q : Nat) : p % 7 + 7 * (q % 7) < 49 := by omega

theorem gfAdd_lt (a b : Nat) : gfAdd a b < 49 := mk_lt _ _

theorem gfMul_lt (a b : Nat) : gfMul a b < 49 := mk_lt _ _

theorem gfDec_inj {a b : Nat} (ha : a < 49) (hb : b < 49) (h : gfDec a = gfDec b) : a = b := by
  have h1 : (a : ZMod 7) = (b : ZMod 7) := by
    rw [← gfDec_re a, ← gfDec_re b, h]
  have h2 : ((a / 7 : Nat) : ZMod 7) = ((b / 7 : Nat) : ZMod 7) := by
    rw [← gfDec_im a, ← gfDec_im b, h]
  rw [ZMod.natCast_eq_natCast_iff'] at h1 h2
  omega

theorem gfDec_surj (x : GF49) : ∃ n : Nat, n < 49 ∧ gfDec n = x := by
  refine ⟨x.re.val + 7 * x.im.val, ?_, ?_⟩
  · have h1 := ZMod.val_lt x.re
    have h2 := ZMod.val_lt x.im
    omega
  · have h1 := ZMod.val_lt x.re
    have h2 := ZMod.val_lt x.im
    apply QuadraticAlgebra.ext
    · rw [gfDec_re]
      push_cast
      simp [seven_eq_zero]
    · rw [gfDec_im]
      have : (x.re.val + 7 * x.im.val) / 7 = x.im.val := by omega
      rw [this]
      simp

theorem eq_zero_iff_of_lt {a : Nat} (ha : a < 49) : a = 0 ↔ gfDec a = 0 := by
  constructor
  · rintro rfl
    exact gfDec_zero
  · intro h
    exact gfDec_inj ha (by norm_num) (h.trans gfDec_zero.symm)

theorem ne_iff_of_lt {a b : Nat} (ha : a < 49) (hb : b < 49) : a ≠ b ↔ gfDec a ≠ gfDec b :=
  ⟨fun h h' => h (gfDec_inj ha hb h'), fun h h' => h (by rw [h'])⟩

@[expose] def N7.dec (x : N7) : V7 :=
  ⟨gfDec x.x0, gfDec x.x1, gfDec x.x2, gfDec x.x3, gfDec x.x4, gfDec x.x5, gfDec x.x6⟩

theorem e0N_dec : e0N.dec = e0C := by
  simp only [N7.dec, e0N, e0C, gfDec_zero, gfDec_one]

theorem bfN_lt (x y : N7) : bfN x y < 49 := gfAdd_lt _ _

theorem bfN_dec (x y : N7) : gfDec (bfN x y) = bfC x.dec y.dec := by
  simp only [bfN, bfC, N7.dec, gfDec_add, gfDec_mul, gfDec_kappa]

theorem tauN_dec (x : N7) : (tauN x).dec = tauC x.dec := by
  simp only [tauN, tauC, N7.dec, conj49, gfDec_conj]

theorem herN_lt (x y : N7) : herN x y < 49 := bfN_lt _ _

theorem herN_dec (x y : N7) : gfDec (herN x y) = herC x.dec y.dec := by
  rw [herN, bfN_dec, tauN_dec, herC]

theorem gramNe_iff (x y : N7) : gramNe x y = true ↔ gramC x.dec y.dec ≠ 0 := by
  unfold gramNe
  rw [bne_iff_ne, ne_iff_of_lt (gfMul_lt _ _) (gfMul_lt _ _), gfDec_mul, gfDec_mul, herN_dec,
    herN_dec, herN_dec, herN_dec, gramC, sub_ne_zero]

theorem isFFN_iff (x : N7) : isFFN x = true ↔ isFFC x.dec = true := by
  unfold isFFN isFFC
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  rw [eq_zero_iff_of_lt (bfN_lt _ _), eq_zero_iff_of_lt (herN_lt _ _), bfN_dec, herN_dec]

theorem colN_iff (x y : N7) : colN x y = true ↔ colC x.dec y.dec = true := by
  unfold colN colC
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
  rw [eq_zero_iff_of_lt (bfN_lt _ _), bfN_dec, gramNe_iff]

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
