module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCUnitaryModel
open Matrix

variable {K : Type} [Field K]

theorem gu_multiplier_pow_eq_one {d n p : ℕ} {h : UnitaryFieldData 2 n K} {D : GL (Fin d) K}
    {μ : K} (hd : 1 ≤ d) (hμ0 : μ ≠ 0)
    (hμ : Matrix.transpose ((D : Matrix (Fin d) (Fin d) K).map h.bar) *
      (D : Matrix (Fin d) (Fin d) K) = μ • (1 : Matrix (Fin d) (Fin d) K))
    (hDp : D ^ p = 1) : μ ^ p = 1 := by
  classical
  have hDinv : (D : Matrix (Fin d) (Fin d) K) * ((D⁻¹ : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDT : Matrix.transpose ((D : Matrix (Fin d) (Fin d) K).map h.bar) =
      μ • ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    calc Matrix.transpose ((D : Matrix (Fin d) (Fin d) K).map h.bar)
        = Matrix.transpose ((D : Matrix (Fin d) (Fin d) K).map h.bar) *
            ((D : Matrix (Fin d) (Fin d) K) * ((D⁻¹ : GL (Fin d) K) :
              Matrix (Fin d) (Fin d) K)) := by rw [hDinv, mul_one]
      _ = (Matrix.transpose ((D : Matrix (Fin d) (Fin d) K).map h.bar) *
            (D : Matrix (Fin d) (Fin d) K)) * ((D⁻¹ : GL (Fin d) K) :
              Matrix (Fin d) (Fin d) K) := by rw [mul_assoc]
      _ = (μ • (1 : Matrix (Fin d) (Fin d) K)) * ((D⁻¹ : GL (Fin d) K) :
            Matrix (Fin d) (Fin d) K) := by rw [hμ]
      _ = μ • ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        rw [Matrix.smul_mul, Matrix.one_mul]
  have hmap : Matrix.transpose (((D ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map
      h.bar) =
      μ ^ p • (1 : Matrix (Fin d) (Fin d) K) := by
    have hval : ((D ^ p : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (D : Matrix (Fin d) (Fin d) K) ^ p := Units.val_pow_eq_pow_val D p
    rw [hval, Matrix.map_pow, Matrix.transpose_pow, hDT]
    have hsmul : ∀ k : ℕ, (μ • ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) ^ k =
        (μ ^ k) • (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ, pow_succ]
    have h1 : (D⁻¹ : GL (Fin d) K) ^ p = 1 := by rw [inv_pow, hDp, inv_one]
    have hinvpow : (((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) ^ p) = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    rw [hsmul, hinvpow]
  have hbar1 : ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map h.bar = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]
  have hone : (1 : Matrix (Fin d) (Fin d) K) = μ ^ p • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [← hmap]
    simp [hDp, hbar1]
  have h := congrFun (congrFun hone ⟨0, by omega⟩) ⟨0, by omega⟩
  simpa [Matrix.smul_apply] using h.symm

theorem mem_primeFormUnitary_of_gu_pow_eq_one {d n p : ℕ} {h : UnitaryFieldData 2 n K}
    {D : GL (Fin d) K} (hd : 1 ≤ d)
    (hD : D ∈ LargeEvenGUSet (Fin d) K (2 ^ n)) (hDp : D ^ p = 1)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) :
    D ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h (idGram K d) := by
  classical
  obtain ⟨μ, hμ0, hμq, hμ⟩ := hD
  have hbarEq : (D : Matrix (Fin d) (Fin d) K).map h.bar =
      (D : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n) := by
    ext i j
    simp only [Matrix.map_apply]
    exact (h.bar_apply _).symm
  have hμbar : Matrix.transpose ((D : Matrix (Fin d) (Fin d) K).map h.bar) *
      (D : Matrix (Fin d) (Fin d) K) = μ • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [hbarEq]
    exact hμ
  have hμp : μ ^ p = 1 := gu_multiplier_pow_eq_one hd hμ0 hμbar hDp
  have hqpos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have hμq1 : μ ^ (2 ^ n - 1) = 1 := by
    have h1 : μ ^ (2 ^ n - 1) * μ = μ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hqpos.ne'), hμq]
    exact mul_right_cancel₀ hμ0 (by rw [h1, one_mul])
  have hcop : Nat.Coprime p (2 ^ n - 1) := by
    rw [hp.coprime_iff_not_dvd]
    intro hdvd
    have h2 : p ∣ 2 := by
      have h := (Nat.dvd_sub_iff_left (m := p) (n := 2 ^ n + 1) (k := 2 ^ n - 1)
        (by omega) hdvd).2 hpq
      have hdiff : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
      simpa [hdiff] using h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hp2le : 2 ≤ p := hp.two_le
    omega
  have hμ1 : μ = 1 := by
    have h1 : orderOf μ ∣ p := orderOf_dvd_iff_pow_eq_one.2 hμp
    have h2 : orderOf μ ∣ 2 ^ n - 1 := orderOf_dvd_iff_pow_eq_one.2 hμq1
    have h3 : orderOf μ ∣ Nat.gcd p (2 ^ n - 1) := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  rw [hμ1, one_smul] at hμ
  rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
  rw [hbarEq]
  change ((D : Matrix (Fin d) (Fin d) K).map (· ^ 2 ^ n))ᵀ *
    (1 : Matrix (Fin d) (Fin d) K) * (D : Matrix (Fin d) (Fin d) K) = 1
  simpa only [Matrix.mul_one] using hμ

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
