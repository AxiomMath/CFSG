module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4

public section
namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4
variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem shape_gen (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (α : Su K p f 4 →* Su K p f 4)
    (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A)
    (hfix2 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 2 (by norm_num) A) =
      blockEmb K p f 4 2 2 (by norm_num) A) :
    (φ = RingEquiv.refl K ∧ ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, b, 0; 0, 0, 0, b]) ∨
    (φ = unitaryInvolution K p f ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0]) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  obtain ⟨t, ht, hts⟩ : ∃ t : K, unitaryInvolution K p f t * t = 1 ∧
      unitaryInvolution K p f t ≠ t := by
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
    exact exists_norm_one_ne_aux _ h2 hζ0 hζ
  have ht' := hσσ t
  set G : Matrix (Fin 4) (Fin 4) K := (g : Matrix (Fin 4) (Fin 4) K) with hG
  set Gi : Matrix (Fin 4) (Fin 4) K := ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hGi
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdet : G.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have key : ∀ (r : Su K p f 4) (R R' : Matrix (Fin 4) (Fin 4) K), α r = r → suMat r = R →
      φ.mapMatrix R = R' → G * R' = R * G := by
    intro r R R' hr hR hR'
    have h := hα r
    rw [hr, hR, hR'] at h
    have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc G * R' = G * R' * (Gi * G) := by rw [hGiG, Matrix.mul_one]
      _ = (G * R' * Gi) * G := by simp only [Matrix.mul_assoc]
      _ = R * G := by rw [← h]
  have hd1 : G * !![φ t, 0, 0, 0; 0, φ (unitaryInvolution K p f t), 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![t, 0, 0, 0; 0, unitaryInvolution K p f t, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G := by
    refine key _ _ _ (hfix0 (dSU K p f ht ht')) ?_ ?_
    · rw [suMat_blockEmb_zero, suMat_dSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hd2 : G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, φ t, 0; 0, 0, 0, φ (unitaryInvolution K p f t)] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, t, 0; 0, 0, 0, unitaryInvolution K p f t] * G := by
    refine key _ _ _ (hfix2 (dSU K p f ht ht')) ?_ ?_
    · rw [suMat_blockEmb_two, suMat_dSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hj1 : G * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G := by
    refine key _ _ _ (hfix0 (jSU K p f)) ?_ ?_
    · rw [suMat_blockEmb_zero, suMat_jSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hj2 : G * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] * G := by
    refine key _ _ _ (hfix2 (jSU K p f)) ?_ ?_
    · rw [suMat_blockEmb_two, suMat_jSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hA : ∀ a : K, ∃ b : K,
      G * !![φ a, φ b, 0, 0; -φ (unitaryInvolution K p f b), φ (unitaryInvolution K p f a), 0, 0;
          0, 0, 1, 0; 0, 0, 0, 1] =
        !![a, b, 0, 0; -unitaryInvolution K p f b, unitaryInvolution K p f a, 0, 0;
          0, 0, 1, 0; 0, 0, 0, 1] * G := by
    intro a
    have hfixd : unitaryInvolution K p f (1 - unitaryInvolution K p f a * a) =
        1 - unitaryInvolution K p f a * a := by
      rw [map_sub, map_one, map_mul, hσσ]
      ring
    obtain ⟨b, hb⟩ := hσ.exists_norm hfixd
    have hab : unitaryInvolution K p f a * a + unitaryInvolution K p f b * b = 1 := by
      rw [hb]
      ring
    refine ⟨b, key _ _ _ (hfix0 (aSU K p f hab hσσ)) ?_ ?_⟩
    · rw [suMat_blockEmb_zero, suMat_aSU]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  exact core4 (unitaryInvolution K p f) φ hσσ (u := t) (v := unitaryInvolution K p f t)
    (by rw [mul_comm]; exact ht) hts G hdet hd1 hd2 hj1 hj2 hA

end CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
