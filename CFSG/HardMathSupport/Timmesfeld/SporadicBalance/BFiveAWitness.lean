module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveTwoB
public import CFSG.Monster.B.Final.SeedUnit
public import Certificates.Certificate13612
public import Certificates.Certificate13613

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned
  CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

section Elements

@[expose] noncomputable def yAFive : NativeSporadic.B := qFive 1 * qFive 2

@[expose] noncomputable def gOneM : NativeSporadic.B := runG (max15Prog ()) bA₁ bA₂ 1

@[expose] noncomputable def gTwoM : NativeSporadic.B := runG (max15Prog ()) bA₁ bA₂ 2

@[expose] noncomputable def sFiveA : NativeSporadic.B := gTwoM ^ 14

@[expose] noncomputable def yOneFiveA : NativeSporadic.B := gOneM * gTwoM ^ 15 * gOneM ^ 3

@[expose] noncomputable def aFiveA : NativeSporadic.B := (yOneFiveA * gTwoM ^ 15) ^ 5

@[expose] noncomputable def bFiveA : NativeSporadic.B := (gTwoM ^ 15 * yOneFiveA) ^ 5

end Elements

section Parts

theorem bFiveAK_parts : tFive * yAFive = yAFive * tFive ∧
    Matrix.rank (bMat yAFive - 1) = 3480 ∧ Matrix.rank (bMat zFive - 1) = 3500 := by
  obtain ⟨hA, hB, hregs, hcomm, hrA, hrZ⟩ := Certificates.certificate13612
  have hR := bMat_runG_of_regsOK hA hB hregs
  have vx : bMat xFive = CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85 := hR 0 (by norm_num)
  have vh : bMat hFive = CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86 := hR 1 (by norm_num)
  obtain ⟨hx5, -, hh8, -, -, -, -, hq, -⟩ := five_facts
  have e7 : hFive⁻¹ = hFive ^ 7 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hh8
  have e4 : xFive⁻¹ = xFive ^ 4 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hx5
  have hq4 : ∀ i, (qFive i)⁻¹ = qFive i ^ 4 := fun i => by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact (hq i).1
  have v1 : bMat (qFive 0) = CFSG.KC.BM.FiveA.qOneW (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86) := by
    simp only [qFive, qBaseFive, wFive, Matrix.cons_val_zero, map_pow, map_mul, vx, vh,
      CFSG.KC.BM.FiveA.qOneW]
  have v2 : bMat (qFive 1) = CFSG.KC.BM.FiveA.qTwoW (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86) := by
    have e : qFive 1 = hFive ^ 7 * qFive 0 * hFive := by
      simp only [qFive, Matrix.cons_val_one, Matrix.cons_val_zero, e7]
    rw [e, map_mul, map_mul, map_pow, v1, vh, CFSG.KC.BM.FiveA.qTwoW]
  have v3 : bMat (qFive 2) = CFSG.KC.BM.FiveA.qThreeW (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86) := by
    have e : qFive 2 = xFive ^ 4 * qFive 0 * xFive := by
      simp only [qFive, Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.tail_cons,
        Matrix.head_cons, e4]
    rw [e, map_mul, map_mul, map_pow, v1, vx, CFSG.KC.BM.FiveA.qThreeW]
  have hz : zFive = qFive 0 ^ 4 * qFive 1 ^ 4 * qFive 0 * qFive 1 := by
    rw [zFive, bcomm, hq4, hq4]
  have vt : bMat tFive = CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86 ^ 4 := by
    rw [tFive, map_pow, vh]
  have vy : bMat yAFive = CFSG.KC.BM.FiveA.qTwoW (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86) *
      CFSG.KC.BM.FiveA.qThreeW (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f85)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Five.f86) := by
    rw [yAFive, map_mul, v2, v3]
  refine ⟨comm_of_bMat (by rw [vt, vy]; exact hcomm), by rw [vy]; exact hrA, ?_⟩
  rw [hz, map_mul, map_mul, map_mul, map_pow, map_pow, v1, v2]
  exact hrZ

theorem bFiveAM_parts :
    sFiveA ^ 5 = 1 ∧ sFiveA ≠ 1 ∧ Matrix.rank (bMat sFiveA - 1) = 3480 ∧
      aFiveA * aFiveA = 1 ∧ aFiveA ≠ 1 ∧ Matrix.rank (bMat aFiveA - 1) = 2048 ∧
      bFiveA * bFiveA = 1 ∧ bFiveA ≠ 1 ∧ Matrix.rank (bMat bFiveA - 1) = 2048 ∧
      aFiveA * bFiveA = bFiveA * aFiveA ∧ Matrix.rank (bMat (aFiveA * bFiveA) - 1) = 2048 ∧
      aFiveA * sFiveA = sFiveA * aFiveA ∧ bFiveA * sFiveA = sFiveA * bFiveA := by
  obtain ⟨hA, hB, hregs, h⟩ := Certificates.certificate13613
  have hR := bMat_runG_of_regsOK hA hB hregs
  have v1 : bMat gOneM = CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g1 := hR 0 (by norm_num)
  have v2 : bMat gTwoM = CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g2 := hR 1 (by norm_num)
  have es : bMat sFiveA = CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g2 ^ 14 := by
    rw [sFiveA, map_pow, v2]
  have ea : bMat aFiveA = CFSG.KC.BM.FiveM.aW (CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g1)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g2) := by
    rw [aFiveA, yOneFiveA, map_pow, map_mul, map_mul, map_mul, map_pow, map_pow, v1, v2]
    rfl
  have eb : bMat bFiveA = CFSG.KC.BM.FiveM.bW (CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g1)
      (CFSG.KC.BM.stripMat CFSG.KC.BM.Max15.g2) := by
    rw [bFiveA, yOneFiveA, map_pow, map_mul, map_mul, map_mul, map_pow, map_pow, v1, v2]
    rfl
  obtain ⟨hs5, hs1, hsr, haa, ha1, har, hbb, hb1, hbr, hab, habr, has, hbs⟩ := h
  exact ⟨pow_of_bMat (by rw [es]; exact hs5), ne_one_of_bMat (by rw [es]; exact hs1),
    by rw [es]; exact hsr,
    mul_self_of_bMat (by rw [ea]; exact haa), ne_one_of_bMat (by rw [ea]; exact ha1),
    by rw [ea]; exact har,
    mul_self_of_bMat (by rw [eb]; exact hbb), ne_one_of_bMat (by rw [eb]; exact hb1),
    by rw [eb]; exact hbr,
    comm_of_bMat (by rw [ea, eb]; exact hab), by rw [map_mul, ea, eb]; exact habr,
    comm_of_bMat (by rw [ea, es]; exact has), comm_of_bMat (by rw [eb, es]; exact hbs)⟩

end Parts

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
