module

public import CFSG.ClassicalInvolution.AschTight.S1911F0b
public import CFSG.ClassicalInvolution.AschTight.S1911Facts

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem nonempty_mulEquiv_of_iff {K : Type} [Field K] (σ : F ≃+* F) (ι : K →+* F)
    (hι : ∀ x : F, σ x = x ↔ x ∈ ι.range) {P : Matrix (Fin 2) (Fin 2) F} (hP : IsUnit P.det)
    (H : Subgroup SL(2, F))
    (hH : ∀ b : SL(2, F), b ∈ H ↔ (P⁻¹ * (b : Matrix (Fin 2) (Fin 2) F) * P).map σ =
      P⁻¹ * (b : Matrix (Fin 2) (Fin 2) F) * P) :
    Nonempty (↥H ≃* SL(2, K)) := by
  classical
  have hPPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPiP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hdet : ∀ A : SL(2, K), (P * (A : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹).det = 1 := by
    intro A
    have h1 : ((A : Matrix (Fin 2) (Fin 2) K).map ι).det = ι (A : Matrix (Fin 2) (Fin 2) K).det :=
      (RingHom.map_det ι _).symm
    rw [Matrix.det_mul, Matrix.det_mul, h1, A.det_coe, map_one, mul_one, ← Matrix.det_mul, hPPi,
      Matrix.det_one]
  have hconj : ∀ X : Matrix (Fin 2) (Fin 2) F, P⁻¹ * (P * X * P⁻¹) * P = X := by
    intro X
    calc P⁻¹ * (P * X * P⁻¹) * P = (P⁻¹ * P) * X * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]
  let ψ : SL(2, K) → SL(2, F) := fun A =>
    ⟨P * (A : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹, hdet A⟩
  have hmem : ∀ A : SL(2, K), ψ A ∈ H := by
    intro A
    rw [hH]
    change (P⁻¹ * (P * (A : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹) * P).map σ =
      P⁻¹ * (P * (A : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹) * P
    rw [hconj]
    ext i j
    exact (hι _).mpr ⟨_, rfl⟩
  let φ : SL(2, K) →* ↥H :=
    { toFun := fun A => ⟨ψ A, hmem A⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change P * ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹ = 1
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.map_one ι (map_zero ι) (map_one ι),
          Matrix.mul_one, hPPi]
      map_mul' := by
        intro A B
        apply Subtype.ext
        apply Subtype.ext
        change P * ((A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K)).map ι * P⁻¹ =
          P * (A : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹ *
            (P * (B : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹)
        rw [Matrix.map_mul]
        calc P * ((A : Matrix (Fin 2) (Fin 2) K).map ι * (B : Matrix (Fin 2) (Fin 2) K).map ι) *
              P⁻¹ = P * (A : Matrix (Fin 2) (Fin 2) K).map ι * (P⁻¹ * P) *
                (B : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹ := by
              rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc] }
  have hinj : Function.Injective φ := by
    intro A B hAB
    have h1 := congrArg (fun x : ↥H => ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) hAB
    change P * (A : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹ =
      P * (B : Matrix (Fin 2) (Fin 2) K).map ι * P⁻¹ at h1
    have h2 := congrArg (fun X => P⁻¹ * X * P) h1
    simp only [hconj] at h2
    apply Subtype.ext
    ext i j
    exact ι.injective (congrFun (congrFun h2 i) j)
  have hsurj : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    rw [hH] at hb
    set C := P⁻¹ * (b : Matrix (Fin 2) (Fin 2) F) * P with hC
    have hCi : ∀ i j, ∃ y, ι y = C i j := fun i j =>
      (hι (C i j)).mp (congrFun (congrFun hb i) j)
    choose f hf using hCi
    have hfC : (Matrix.of f).map ι = C := by
      ext i j
      exact hf i j
    have hdetf : (Matrix.of f).det = 1 := by
      apply ι.injective
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hfC, map_one, hC, Matrix.det_mul,
        Matrix.det_mul, b.det_coe, mul_one, ← Matrix.det_mul, hPiP, Matrix.det_one]
    refine ⟨⟨Matrix.of f, hdetf⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change P * (Matrix.of f).map ι * P⁻¹ = (b : Matrix (Fin 2) (Fin 2) F)
    rw [hfC, hC]
    calc P * (P⁻¹ * (b : Matrix (Fin 2) (Fin 2) F) * P) * P⁻¹ =
        (P * P⁻¹) * (b : Matrix (Fin 2) (Fin 2) F) * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
      _ = (b : Matrix (Fin 2) (Fin 2) F) := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem factF0 : FactF0 := by
  intro p e _ hp2 he σ hσ1 hσ2 G hinv
  have h2e : 2 * e ≠ 0 := by omega
  obtain ⟨k, hk, hσk⟩ := eq_frobenius_of_sq_eq_one h2e hσ2 hσ1
  have hσ : ∀ x, σ x = x ^ (p ^ e) := by
    intro x
    rw [hσk, show k = e by omega]
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : GaloisField p (2 * e) ≃+* GaloisField p (2 * e) => τ x) hσ2
    simpa using this
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hm3 : 3 ≤ p ^ e := hp3.trans (Nat.le_self_pow he.ne' p)
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p _ h2e, ← pow_mul, mul_comm]
  obtain ⟨l, hl0, hσl, hGl⟩ := exists_mul_map_eq_smul σ hσσ G hinv
  have hlm : l ^ (p ^ e) = l := by rw [← hσ l, hσl]
  obtain ⟨c, hc⟩ := exists_pow_succ_eq hF (by omega) hl0 hlm
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hc
    exact hl0 hc.symm
  have hcs : c * σ c = l := by rw [hσ, ← pow_succ', hc]
  have hA : (c⁻¹ • (G : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * e)))) *
      (c⁻¹ • (G : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * e)))).map σ = 1 := by
    have h1 : (c⁻¹ • (G : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * e)))).map σ =
        σ c⁻¹ • (G : Matrix (Fin 2) (Fin 2) (GaloisField p (2 * e))).map σ := by
      ext i j
      simp
    rw [h1, Matrix.smul_mul, Matrix.mul_smul, hGl, smul_smul, smul_smul, map_inv₀,
      ← mul_inv, hcs, inv_mul_cancel₀ hl0, one_smul]
  obtain ⟨P, hP, hAP⟩ := exists_mul_map_eq_self hF hm3 σ hσ hσσ _ hA
  obtain ⟨ι, hι⟩ := exists_ringHom_range (p := p) he
  have hι' : ∀ x, σ x = x ↔ x ∈ ι.range := fun x => by rw [hσ]; exact hι x
  exact nonempty_mulEquiv_of_iff σ ι hι' hP _ fun b => by
    change semilinHom G σ b = b ↔ _
    exact semilinHom_eq_self_iff σ G hc0 hP hAP b

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
