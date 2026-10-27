module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLULift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {K : Type} [Field K] [Finite K]

theorem exists_pow_eq_of_not_dvd_card_sub_one {p : ℕ} (hp : p.Prime)
    (hK : ¬ p ∣ Nat.card K - 1) (c : Kˣ) : ∃ c₀ : Kˣ, c₀ ^ p = c := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Nat.card Kˣ = Nat.card K - 1 := by
    simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hcop : (Nat.card Kˣ).Coprime p := by
    rw [hcard]
    exact ((hp.coprime_iff_not_dvd).2 hK).symm
  obtain ⟨c₀, hc₀⟩ := (powCoprime hcop).surjective c
  exact ⟨c₀, by rw [← powCoprime_apply hcop]; exact hc₀⟩

theorem exists_scalar_mul_pow_eq_one_of_conjAut {N p : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (hK : ¬ p ∣ Nat.card K - 1) {B : Matrix.GeneralLinearGroup (Fin N) K}
    (hB : LinearFlag.conjAut N K B ^ p = 1) :
    ∃ (c₀ : Kˣ) (B' : Matrix.GeneralLinearGroup (Fin N) K),
      B' = Matrix.GeneralLinearGroup.scalar (Fin N) c₀ * B ∧ B' ^ p = 1 := by
  have hBp : LinearFlag.conjAut N K (B ^ p) = 1 := by rw [map_pow, hB]
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
    hN hBp
  obtain ⟨c₀, hc₀⟩ := exists_pow_eq_of_not_dvd_card_sub_one hp hK c
  refine ⟨c₀⁻¹, Matrix.GeneralLinearGroup.scalar (Fin N) c₀⁻¹ * B, rfl, ?_⟩
  have hcomm : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) c₀⁻¹) B :=
    (commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute c₀⁻¹ B)
  rw [hcomm.mul_pow, ← map_pow, hc, ← map_mul,
    show c₀⁻¹ ^ p = c⁻¹ by rw [inv_pow, hc₀], inv_mul_cancel, map_one]

theorem commute_of_conjAut_commute_of_not_dvd {N p : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (hnot : ¬ (p ∣ N ∧ p ∣ Nat.card K - 1))
    {A B : Matrix.GeneralLinearGroup (Fin N) K}
    (hAp : LinearFlag.conjAut N K A ^ p = 1)
    (hcomm : LinearFlag.conjAut N K A * LinearFlag.conjAut N K B =
      LinearFlag.conjAut N K B * LinearFlag.conjAut N K A) :
    A * B = B * A := by
  have h1 : LinearFlag.conjAut N K (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨ζ, hζ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one hN h1
  have hAB : A * B = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * (B * A) := by
    rw [← hζ]
    group
  have hconj : A * B * A⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin N) ζ * B := by
    rw [hAB]
    group
  have hApp : LinearFlag.conjAut N K (A ^ p) = 1 := by rw [map_pow, hAp]
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_eq_scalar_of_conjAut_eq_one
    hN hApp
  have hiter : ∀ k : ℕ, A ^ k * B * (A ^ k)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k) * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : A ^ (k + 1) * B * (A ^ (k + 1))⁻¹ =
          A * (A ^ k * B * (A ^ k)⁻¹) * A⁻¹ := by group
      rw [e, ih]
      have hs : A * Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k) =
          Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k) * A :=
        (Matrix.GeneralLinearGroup.scalar_commute (ζ ^ k) A).symm
      calc A * (Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k) * B) * A⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k) * (A * B * A⁻¹) := by
            rw [← mul_assoc A (Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k)) B, hs]
            group
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ k) *
              (Matrix.GeneralLinearGroup.scalar (Fin N) ζ * B) := by rw [hconj]
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ (k + 1)) * B := by
            rw [← mul_assoc, ← map_mul, ← pow_succ]
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin N) : Kˣ →
      Matrix.GeneralLinearGroup (Fin N) K) := by
    intro a b hab
    have he := congrArg (fun g : Matrix.GeneralLinearGroup (Fin N) K =>
      ((g : Matrix (Fin N) (Fin N) K) ⟨0, by omega⟩ ⟨0, by omega⟩)) hab
    exact Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] using he)
  have hζp : ζ ^ p = 1 := by
    have h := hiter p
    rw [hc] at h
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin N) c * B *
        (Matrix.GeneralLinearGroup.scalar (Fin N) c)⁻¹ = B := by
      rw [Matrix.GeneralLinearGroup.scalar_commute c B, mul_assoc, mul_inv_cancel,
        mul_one]
    rw [h2] at h
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin N) (ζ ^ p) = 1 := by
      have h5 := congrArg (fun x : Matrix.GeneralLinearGroup (Fin N) K => x * B⁻¹) h
      simpa using h5.symm
    exact hinj (h3.trans (map_one _).symm)
  have hζN : ζ ^ N = 1 := by
    classical
    have h2 : Matrix.GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by simp [map_mul]
    rw [hζ] at h2
    simpa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using h2
  have hζcard : ζ ^ (Nat.card K - 1) = 1 := by
    classical
    haveI : Fintype K := Fintype.ofFinite K
    have hcard : Nat.card Kˣ = Nat.card K - 1 := by
      simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
    rw [← hcard]
    exact pow_card_eq_one'
  have hζ1 : ζ = 1 := by
    have hdvd : orderOf ζ ∣ Nat.gcd N (Nat.card K - 1) :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.2 hζN) (orderOf_dvd_iff_pow_eq_one.2 hζcard)
    have hcop : (Nat.gcd N (Nat.card K - 1)).Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hpdvd
      exact hnot ⟨hpdvd.trans (Nat.gcd_dvd_left N _), hpdvd.trans (Nat.gcd_dvd_right N _)⟩
    have hpdvd : orderOf ζ ∣ p := orderOf_dvd_iff_pow_eq_one.2 hζp
    have hone : orderOf ζ ∣ 1 := by
      have h := Nat.dvd_gcd hdvd hpdvd
      rwa [Nat.Coprime.gcd_eq_one hcop] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hone)
  rw [hζ1] at hζ
  have h4 : A * B * A⁻¹ * B⁻¹ = 1 := by rw [hζ, map_one]
  calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
    _ = B * A := by rw [h4, one_mul]

theorem exists_commuting_pow_one_lifts {N p : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (hnot : ¬ (p ∣ N ∧ p ∣ Nat.card K - 1))
    {A B : Matrix.GeneralLinearGroup (Fin N) K}
    (hAp : LinearFlag.conjAut N K A ^ p = 1) (hBp : LinearFlag.conjAut N K B ^ p = 1)
    (hcomm : LinearFlag.conjAut N K A * LinearFlag.conjAut N K B =
      LinearFlag.conjAut N K B * LinearFlag.conjAut N K A) :
    ∃ A' B' : Matrix.GeneralLinearGroup (Fin N) K,
      A' ^ p = 1 ∧ B' ^ p = 1 ∧ A' * B' = B' * A' ∧
        LinearFlag.conjAut N K A' = LinearFlag.conjAut N K A ∧
        LinearFlag.conjAut N K B' = LinearFlag.conjAut N K B := by
  by_cases hpN : p ∣ N
  ·
    have hK : ¬ p ∣ Nat.card K - 1 := fun h => hnot ⟨hpN, h⟩
    obtain ⟨c₁, A', hA'e, hA'p⟩ := exists_scalar_mul_pow_eq_one_of_conjAut hp hN hK hAp
    obtain ⟨c₂, B', hB'e, hB'p⟩ := exists_scalar_mul_pow_eq_one_of_conjAut hp hN hK hBp
    have hAB : A * B = B * A :=
      commute_of_conjAut_commute_of_not_dvd hp hN hnot hAp hcomm
    refine ⟨A', B', hA'p, hB'p, ?_, ?_, ?_⟩
    · rw [hA'e, hB'e]
      have hAB' : Commute A B := (commute_iff_eq _ _).mpr hAB
      have hAc : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) c₁ * A)
          (Matrix.GeneralLinearGroup.scalar (Fin N) c₂) :=
        ((commute_iff_eq _ _).mpr (Matrix.GeneralLinearGroup.scalar_commute c₂ _)).symm
      have hAB2 : Commute (Matrix.GeneralLinearGroup.scalar (Fin N) c₁ * A) B :=
        Commute.mul_left ((commute_iff_eq _ _).mpr
          (Matrix.GeneralLinearGroup.scalar_commute c₁ B)) hAB'
      exact (hAc.mul_right hAB2).eq
    · rw [hA'e, map_mul, LinearFlag.conjAut_scalar, one_mul]
    · rw [hB'e, map_mul, LinearFlag.conjAut_scalar, one_mul]
  ·
    obtain ⟨A', hA'c, hA'p⟩ :=
      exists_pow_eq_one_of_conjAut_pow_eq_one hp hN hpN hAp
    obtain ⟨B', hB'c, hB'p⟩ :=
      exists_pow_eq_one_of_conjAut_pow_eq_one hp hN hpN hBp
    refine ⟨A', B', hA'p, hB'p, ?_, hA'c, hB'c⟩
    exact commute_of_conjAut_commute hp hN hA'p hB'p (by rw [hA'c, hB'c]; exact hcomm) hpN

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
