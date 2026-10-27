module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9Spec
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9UHMat
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLRestField
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9UHField
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9UHScalar

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary Matrix
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

section

variable {F : Type} [Field F] [Finite F] {p k : ℕ} [Fact p.Prime] [CharP F p]

theorem unitaryH90_core (hF : Nat.card F = (p ^ (3 * k)) ^ 2) {σ : F ≃+* F}
    (hkc : Nat.card (fixF σ) = (p ^ k) ^ 2)
    (A : GL (Fin 3) F) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hA : conjTr (unitaryInvolution F p (3 * k)) (A : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1)
    (hc : ∃ c : Fˣ, twistedProd σ A 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c) :
    ∃ (M : GL (Fin 3) F) (d : Fˣ),
      conjTr (unitaryInvolution F p (3 * k)) (M : Matrix (Fin 3) (Fin 3) F) *
        (M : Matrix (Fin 3) (Fin 3) F) = 1 ∧
      A * Matrix.GeneralLinearGroup.map (σ : F →+* F) M =
        Matrix.GeneralLinearGroup.scalar (Fin 3) d * M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set bar := unitaryInvolution F p (3 * k) with hbar
  have hinv : ∀ x, bar (bar x) = x := unitaryInvolution_involutive hF
  have hcomm : ∀ x, σ (bar x) = bar (σ x) := sigma_comm_bar σ
  have h3 : ∀ x, σ (σ (σ x)) = x := fun x => by rw [← iter_three, hσ3]; rfl
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨c, hc⟩ := hc
  obtain ⟨H, d, hH⟩ := CFSG.StandardType.OrdPRest.exists_hilbert90 (by norm_num) hσo A hc
  have hHm : (A : Matrix (Fin 3) (Fin 3) F) * (H : Matrix (Fin 3) (Fin 3) F).map σ =
      (d : F) • (H : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg Units.val hH
    simpa [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul] using this
  set H' : Matrix (Fin 3) (Fin 3) F := (H : Matrix (Fin 3) (Fin 3) F) with hH'
  set J : Matrix (Fin 3) (Fin 3) F := conjTr bar H' * H' with hJ
  have hJσ : J.map σ = (bar d * d) • J := map_gram hcomm hA hHm
  have hdetH : H'.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _ |>.1 H.isUnit).ne_zero
  have hdet : J.det ≠ 0 := by
    rw [hJ, det_mul]
    refine mul_ne_zero ?_ hdetH
    have : (conjTr bar H').det = bar H'.det := by
      rw [conjTr, det_transpose]
      exact (RingHom.map_det (bar : F →+* F) H').symm
    rw [this]
    exact fun h => hdetH (bar.injective (by rw [h, map_zero]))
  have hd0 : (d : F) ≠ 0 := d.ne_zero
  have hbd0 : bar d ≠ 0 := fun h => hd0 (bar.injective (by rw [h, map_zero]))
  have hμbar : bar (bar d * d) = bar d * d := by rw [map_mul, hinv, mul_comm]
  have hμ := norm_eq_one_of_map_eq h3 hJσ hdet
  have hl : bar (bar d * d)⁻¹ = (bar d * d)⁻¹ := by rw [map_inv₀, hμbar]
  have hNl : (bar d * d)⁻¹ * σ (bar d * d)⁻¹ * σ (σ (bar d * d)⁻¹) = 1 := by
    simp only [map_inv₀]
    rw [← mul_inv, ← mul_inv, hμ, inv_one]
  obtain ⟨ν, hν0, hνbar, hνσ⟩ := exists_bar_fixed_hilbert90 hF hσ3 hσ1 hl hNl
  have hμ0 : bar d * d ≠ 0 := mul_ne_zero hbd0 hd0
  have hJ'σ : (ν • J).map σ = ν • J := by
    rw [map_smul_σ, hJσ, hνσ, smul_smul]
    congr 1
    field_simp
  have hJh : conjTr bar J = J := by rw [hJ, conjTr_mul, conjTr_conjTr' bar hinv]
  have hJ'h : conjTr bar (ν • J) = ν • J := by rw [conjTr_smul', hνbar, hJh]
  have hdet' : (ν • J).det ≠ 0 := by
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ hν0) hdet
  obtain ⟨N, hNσ, hN1⟩ := exists_fixed_conjTr (J := ν • J) hkc
    (fun i j => congrFun (congrFun hJ'σ i) j) hJ'h hdet'
  obtain ⟨r, hr⟩ := (isUnitaryInvolution_unitaryInvolution hF).exists_norm hνbar
  have hr0 : r ≠ 0 := fun h => hν0 (by rw [← hr, h, mul_zero])
  have hσr0 : σ r ≠ 0 := fun h => hr0 (σ.injective (by rw [h, map_zero]))
  set N' : Matrix (Fin 3) (Fin 3) F := (N : Matrix (Fin 3) (Fin 3) F) with hN'
  have hNm : N'.map σ = N' := Matrix.ext hNσ
  have hM' : ((Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr0) * H * N : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = r • (H' * N') := by
    simp [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, Matrix.mul_assoc]
    rfl
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr0) * H * N,
    d * Units.mk0 (σ r) hσr0 * (Units.mk0 r hr0)⁻¹, ?_, ?_⟩
  · rw [hM', conjTr_smul', conjTr_mul]
    calc (bar r • (conjTr bar N' * conjTr bar H')) * (r • (H' * N'))
        = (bar r * r) • (conjTr bar N' * (conjTr bar H' * H') * N') := by
          rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
          simp only [Matrix.mul_assoc]
      _ = conjTr bar N' * (ν • J) * N' := by
          rw [hr, Matrix.mul_smul, Matrix.smul_mul]
      _ = 1 := hN1
  · apply Units.ext
    have hmapM : (((Matrix.GeneralLinearGroup.map (σ : F →+* F)
        (Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr0) * H * N) : GL (Fin 3) F)) :
        Matrix (Fin 3) (Fin 3) F) = σ r • (H'.map σ * N') := by
      change ((Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 r hr0) * H * N : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).map σ = _
      rw [hM', map_smul_σ, Matrix.map_mul, hNm]
    rw [Units.val_mul, Units.val_mul, hmapM, hM', Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    calc (A : Matrix (Fin 3) (Fin 3) F) * (σ r • (H'.map σ * N'))
        = σ r • (((A : Matrix (Fin 3) (Fin 3) F) * H'.map σ) * N') := by
          rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = (σ r * d) • (H' * N') := by
          rw [hHm, Matrix.smul_mul, smul_smul]
      _ = _ := by
          rw [smul_smul]
          congr 1
          simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0]
          field_simp

end

theorem unitaryH90 (F : Type) [Field F] [Finite F] (q : ℕ) : UnitaryH90 F q := by
  intro hcard σ A hσ3 hσ1 hA hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨p, hpc⟩ := CharP.exists F
  have hp : p.Prime :=
    (CharP.char_is_prime_or_zero F p).resolve_right (CharP.char_ne_zero_of_finite F p)
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F p
  have hq : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← hn, ← Nat.card_eq_fintype_card, hcard, sq]⟩
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hq
  obtain ⟨k, hk3, hkc⟩ := exists_card_fixF hcard (σ := σ) (orderOf_eq_prime hσ3 hσ1)
  subst hk3
  have hmap : ∀ X : Matrix (Fin 3) (Fin 3) F, (X.map (· ^ p ^ (3 * k)))ᵀ =
      conjTr (unitaryInvolution F p (3 * k)) X := by
    intro X
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
    exact (unitaryInvolution_apply (K := F) (p := p) (f := 3 * k) (X j i)).symm
  simp only [hmap] at hA ⊢
  exact unitaryH90_core hcard hkc A hσ3 hσ1 hA hc

end CFSG.HardMathSupport.Solomon.Coordinator
