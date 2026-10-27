module

public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.Mathlib.LinearAlgebra.Matrix.DetSmulEqZero
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e8_a8_rootChar_prime {p : ℕ} (hp : p.Prime) {k : Type} [Field k]
    (a : Fin Tag.E8.rank → kˣ)
    (B : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ)
    (hGram : B.transpose * Tag.E8.cartan * B = CartanMatrix.A 8)
    (hCols : ∀ j, rootChar a (fun i => B i j) = 1)
    (hPow : ∀ i, a i ^ p = 1) (hne : a ≠ 1) : p = 3 := by
  have hdet : B.det * B.det = 9 := by
    have h := congrArg Matrix.det hGram
    have h1 : (B.transpose * Tag.E8.cartan * B).det = B.det * B.det := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_cartan_E8]
      ring
    have h2 : (CartanMatrix.A 8).det = 9 := by
      rw [CartanMatrix.A_det]
      norm_num
    rw [h1] at h
    exact h.trans h2
  have hb : B.det = 3 ∨ B.det = -3 := by
    have hsq : B.det ^ 2 = (3 : ℤ) ^ 2 := by
      rw [pow_two, pow_two, hdet]
      norm_num
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have h3 : ∀ i, a i ^ 3 = 1 := by
    intro i
    have hd := CFSG.MatrixDet.pow_det_eq_one_of_prod_eq_one B.transpose a (fun j => by
      simpa only [rootChar, Matrix.transpose_apply] using hCols j) i
    rw [Matrix.det_transpose] at hd
    rcases hb with hb | hb
    · rw [hb] at hd
      simpa [zpow_ofNat] using hd
    · rw [hb] at hd
      have h2 : (a i ^ (3 : ℤ))⁻¹ = 1 := by simpa [zpow_neg, zpow_ofNat] using hd
      simpa [zpow_ofNat] using inv_eq_one.mp h2
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    apply hne
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have horder_p : orderOf (a i) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hPow i)
  have horder_3 : orderOf (a i) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr (h3 i)
  have hne1 : orderOf (a i) ≠ 1 := by simpa [orderOf_eq_one_iff] using hi
  have hm : orderOf (a i) = p :=
    (hp.eq_one_or_self_of_dvd (orderOf (a i)) horder_p).resolve_left hne1
  rw [hm] at horder_3
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp horder_3

end CFSG.LieType.Chevalley

end
