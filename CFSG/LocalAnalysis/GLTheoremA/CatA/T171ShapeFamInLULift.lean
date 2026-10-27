module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {K : Type} [Field K] [Finite K]

theorem exists_pow_eq_one_of_conjAut_pow_eq_one {n p : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    (hpn : ¬ p ∣ n) {B : Matrix.GeneralLinearGroup (Fin n) K}
    (hB : LinearFlag.conjAut n K B ^ p = 1) :
    ∃ B' : Matrix.GeneralLinearGroup (Fin n) K,
      LinearFlag.conjAut n K B' = LinearFlag.conjAut n K B ∧ B' ^ p = 1 := by
  have hBp : LinearFlag.conjAut n K (B ^ p) = 1 := by rw [map_pow, hB]
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
    hn hBp
  have hdet : c ^ n = (Matrix.GeneralLinearGroup.det B) ^ p := by
    have h := congrArg Matrix.GeneralLinearGroup.det hc
    simp only [map_pow, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at h
    exact h.symm
  have hcop : Nat.Coprime n p := ((hp.coprime_iff_not_dvd).2 hpn).symm
  have hK : (c : K) ^ n = ((Matrix.GeneralLinearGroup.det B : Kˣ) : K) ^ p := by
    exact_mod_cast congrArg (fun u : Kˣ => (u : K)) hdet
  obtain ⟨μ, hμc, -⟩ :=
    (pow_eq_pow_iff_of_coprime (a := (c : K)) (b := ((Matrix.GeneralLinearGroup.det B : Kˣ) : K))
      hcop).1 hK
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hμc
    exact c.ne_zero hμc
  obtain ⟨μ, hμ⟩ : ∃ μ : Kˣ, μ ^ p = c :=
    ⟨Units.mk0 μ hμ0, Units.ext (by simpa using hμc.symm)⟩
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹ * B, ?_, ?_⟩
  · rw [map_mul, LinearFlag.conjAut_scalar, one_mul]
  · have hcB : Commute (Matrix.GeneralLinearGroup.scalar (Fin n) μ⁻¹) B :=
      (commute_iff_eq _ _).mpr (GeneralLinearGroup.scalar_commute μ⁻¹ B)
    rw [hcB.mul_pow, ← map_pow, hc, ← map_mul]
    rw [show (μ⁻¹) ^ p = c⁻¹ by rw [inv_pow, hμ]]
    rw [inv_mul_cancel]
    exact map_one _

theorem commute_of_conjAut_commute {n p : ℕ} (hp : p.Prime) (hn : 2 ≤ n)
    {A B : Matrix.GeneralLinearGroup (Fin n) K} (hA : A ^ p = 1) (hB : B ^ p = 1)
    (hcomm : LinearFlag.conjAut n K A * LinearFlag.conjAut n K B =
      LinearFlag.conjAut n K B * LinearFlag.conjAut n K A) (hpn : ¬ p ∣ n) :
    A * B = B * A := by
  have h1 : LinearFlag.conjAut n K (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨ζ, hζ⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
    hn h1
  have hAB : A * B = Matrix.GeneralLinearGroup.scalar (Fin n) ζ * (B * A) := by
    rw [← hζ]
    group
  have hconjAB : A * B * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin n) ζ * B := by
    rw [hAB]
    group
  have hconj : ∀ k : ℕ, A * B ^ k * A⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ k) * B ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc A * B ^ (k + 1) * A⁻¹ = (A * B ^ k * A⁻¹) * (A * B * A⁻¹) := by group
        _ = (Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ k) * B ^ k) *
              (Matrix.GeneralLinearGroup.scalar (Fin n) ζ * B) := by rw [ih, hconjAB]
        _ = (Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ k) *
              Matrix.GeneralLinearGroup.scalar (Fin n) ζ) * (B ^ k * B) := by
              rw [show (Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ k) * B ^ k) *
                  (Matrix.GeneralLinearGroup.scalar (Fin n) ζ * B) =
                  (Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ k) *
                    (B ^ k * Matrix.GeneralLinearGroup.scalar (Fin n) ζ)) * B by group]
              rw [← GeneralLinearGroup.scalar_commute ζ (B ^ k)]
              group
        _ = Matrix.GeneralLinearGroup.scalar (Fin n) (ζ ^ (k + 1)) * B ^ (k + 1) := by
              rw [← map_mul, ← pow_succ, ← pow_succ]
  have hζp : ζ ^ p = 1 := by
    have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →
        Matrix.GeneralLinearGroup (Fin n) K) := by
      intro a b hab
      have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin n) K =>
        ((g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩)) hab
      exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply] using he)
    have h := hconj p
    rw [hB, mul_one, mul_inv_cancel, mul_one] at h
    exact hinj (by rw [map_one]; exact h.symm)
  have hζn : ζ ^ n = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
      simp [map_mul]
    rw [hζ] at h1
    simpa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using h1
  have hζ1 : ζ = 1 := by
    have hdvd : orderOf ζ ∣ Nat.gcd n p :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.2 hζn) (orderOf_dvd_iff_pow_eq_one.2 hζp)
    rw [Nat.Coprime.gcd_eq_one (((hp.coprime_iff_not_dvd).2 hpn).symm)] at hdvd
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
  rw [hζ1] at hζ
  have h4 : A * B * A⁻¹ * B⁻¹ = 1 := by rw [hζ, map_one]
  calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
    _ = B * A := by rw [h4, one_mul]

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
