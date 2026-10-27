module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainUMat
public import CFSG.ClassicalInvolution.Models.UnitaryFrames.Chart

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Elements

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
@[expose] noncomputable def jSU : Su K p f 2 :=
  mkSU K p f !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
    (by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two])

theorem suMat_jSU : suMat (jSU K p f) = !![0, 1; -1, 0] := rfl

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem diag2_conjTr (σ : K ≃+* K) {t : K} (ht : σ t * t = 1) (ht' : σ (σ t) = t) :
    conjTr σ !![t, 0; 0, σ t] * !![t, 0; 0, σ t] = 1 := by
  have ht2 : t * σ t = 1 := by rw [mul_comm]; exact ht
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two, ht, ht2, ht']

variable (K p f) in
@[expose] noncomputable def dSU {t : K} (ht : unitaryInvolution K p f t * t = 1)
    (ht' : unitaryInvolution K p f (unitaryInvolution K p f t) = t) : Su K p f 2 :=
  mkSU K p f !![t, 0; 0, unitaryInvolution K p f t]
    (by rw [Matrix.det_fin_two_of]; linear_combination ht) (diag2_conjTr _ ht ht')

theorem suMat_dSU {t : K} (ht : unitaryInvolution K p f t * t = 1)
    (ht' : unitaryInvolution K p f (unitaryInvolution K p f t) = t) :
    suMat (dSU K p f ht ht') = !![t, 0; 0, unitaryInvolution K p f t] := rfl

variable (K p f) in
@[expose] noncomputable def xSU : Su K p f 3 :=
  mkSU K p f !![0, 0, 1; 0, -1, 0; 1, 0, 0] (by simp [Matrix.det_fin_three])
    (by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_three])

theorem suMat_xSU : suMat (xSU K p f) = !![0, 0, 1; 0, -1, 0; 1, 0, 0] := rfl

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem blockMat_three (A : Matrix (Fin 2) (Fin 2) K) :
    blockMat 3 0 A = !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := by
  ext a b
  rw [blockMat_apply]
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_rootInvSU_three :
    suMat (rootInvSU K p f (show 2 ≤ 3 by norm_num)) = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  rw [rootInvSU, suMat_blockEmb, suMat_negOneSU, blockMat_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_blockEmb_jSU :
    suMat (blockEmb K p f 3 2 0 (by norm_num) (jSU K p f)) =
      !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  rw [suMat_blockEmb, suMat_jSU, blockMat_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem suMat_blockEmb_dSU {t : K} (ht : unitaryInvolution K p f t * t = 1)
    (ht' : unitaryInvolution K p f (unitaryInvolution K p f t) = t) :
    suMat (blockEmb K p f 3 2 0 (by norm_num) (dSU K p f ht ht')) =
      !![t, 0, 0; 0, unitaryInvolution K p f t, 0; 0, 0, 1] := by
  rw [suMat_blockEmb, suMat_dSU, blockMat_three]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

end Elements

section Main

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem exists_norm_one_ne_aux (σ : K ≃+* K) (h2 : (2 : K) ≠ 0) {ζ : K} (hζ0 : ζ ≠ 0)
    (hζ : σ ζ = -ζ) : ∃ t : K, σ t * t = 1 ∧ σ t ≠ t := by
  have h1m : 1 - ζ ≠ 0 := by
    intro h
    have hζ1 : ζ = 1 := by linear_combination -h
    rw [hζ1, map_one] at hζ
    exact h2 (by linear_combination hζ)
  have h1p : 1 + ζ ≠ 0 := by
    intro h
    have hζ1 : ζ = -1 := by linear_combination h
    rw [hζ1, map_neg, map_one] at hζ
    exact h2 (by linear_combination -hζ)
  have hσt : σ ((1 + ζ) / (1 - ζ)) = (1 - ζ) / (1 + ζ) := by
    rw [map_div₀, map_add, map_sub, map_one, hζ]
    ring
  refine ⟨(1 + ζ) / (1 - ζ), ?_, ?_⟩
  · rw [hσt]
    field_simp
  · rw [hσt]
    intro h
    rw [div_eq_div_iff h1p h1m] at h
    have h4 : (2 * 2 : K) * ζ = 0 := by linear_combination -h
    exact mul_ne_zero (mul_ne_zero h2 h2) hζ0 h4

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mapMatrix_diag3 (σ : K ≃+* K) {t : K} (hσσ : σ (σ t) = t) :
    σ.mapMatrix (!![t, 0, 0; 0, σ t, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
      !![σ t, 0, 0; 0, t, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hσσ]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem mapMatrix_refl (X : Matrix (Fin 3) (Fin 3) K) : (RingEquiv.refl K).mapMatrix X = X := by
  ext i j
  simp

theorem su3_fixing (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (α : Su K p f 3 →* Su K p f 3) (g : GL (Fin 3) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 3, suMat (α x) =
      (g : Matrix (Fin 3) (Fin 3) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    (hu : ((g : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K p f))ᵀ *
        (g : Matrix (Fin 3) (Fin 3) K) = 1)
    (hφ : φ = RingEquiv.refl K ∨ φ = unitaryInvolution K p f)
    (hαα : ∀ x, α (α x) = x)
    (hfix : ∀ r ∈ rootSU2 K p f (show 2 ≤ 3 by norm_num), α r = r) :
    (∀ s, α s = s) ∨ (∀ s, α s = rootInvSU K p f (show 2 ≤ 3 by norm_num) * s *
      (rootInvSU K p f (show 2 ≤ 3 by norm_num))⁻¹) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσσ : ∀ c, unitaryInvolution K p f (unitaryInvolution K p f c) = c :=
    unitaryInvolution_involutive hK
  obtain ⟨t, ht, hts⟩ : ∃ t : K, unitaryInvolution K p f t * t = 1 ∧
      unitaryInvolution K p f t ≠ t := by
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
    exact exists_norm_one_ne_aux _ h2 hζ0 hζ
  set G : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hG
  set Gi : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hGi
  have hGGi : G * Gi = 1 := by rw [hG, hGi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGiG : Gi * G = 1 := by rw [hG, hGi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hφφ : ∀ c, φ (φ c) = c := by
    rcases hφ with rfl | rfl
    · intro c; rfl
    · exact hσσ
  have hmm : ∀ X : Matrix (Fin 3) (Fin 3) K, φ.mapMatrix (φ.mapMatrix X) = X := by
    intro X
    ext i j
    simp [RingEquiv.mapMatrix_apply, hφφ]
  have hcomm : ∀ r : Su K p f 3, α r = r → G * φ.mapMatrix (suMat r) = suMat r * G := by
    intro r hr
    have h := hα r
    rw [hr] at h
    calc G * φ.mapMatrix (suMat r) = G * φ.mapMatrix (suMat r) * (Gi * G) := by
          rw [hGiG, Matrix.mul_one]
      _ = (G * φ.mapMatrix (suMat r) * Gi) * G := by simp only [Matrix.mul_assoc]
      _ = suMat r * G := by rw [← h]
  have hP : ∀ x : Su K p f 3, (G * φ.mapMatrix G) * suMat x = suMat x * (G * φ.mapMatrix G) := by
    intro x
    have h1 := hα (α x)
    rw [hαα x, hα x] at h1
    have hQP : (φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G) = 1 := by
      calc (φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G)
          = φ.mapMatrix Gi * (Gi * G) * φ.mapMatrix G := by simp only [Matrix.mul_assoc]
        _ = φ.mapMatrix Gi * φ.mapMatrix G := by rw [hGiG, Matrix.mul_one]
        _ = φ.mapMatrix (Gi * G) := (map_mul _ _ _).symm
        _ = 1 := by rw [hGiG, map_one]
    have h2' : suMat x = (G * φ.mapMatrix G) * suMat x * (φ.mapMatrix Gi * Gi) := by
      calc suMat x = G * φ.mapMatrix (G * φ.mapMatrix (suMat x) * Gi) * Gi := h1
        _ = (G * φ.mapMatrix G) * suMat x * (φ.mapMatrix Gi * Gi) := by
          rw [map_mul, map_mul, hmm]
          simp only [Matrix.mul_assoc]
    calc (G * φ.mapMatrix G) * suMat x
        = (G * φ.mapMatrix G) * suMat x * ((φ.mapMatrix Gi * Gi) * (G * φ.mapMatrix G)) := by
          rw [hQP, Matrix.mul_one]
      _ = ((G * φ.mapMatrix G) * suMat x * (φ.mapMatrix Gi * Gi)) * (G * φ.mapMatrix G) := by
          simp only [Matrix.mul_assoc]
      _ = suMat x * (G * φ.mapMatrix G) := by rw [← h2']
  have cx := hcomm _ (hfix _ (rootInvSU_mem_rootSU2 (show 2 ≤ 3 by norm_num)))
  rw [suMat_rootInvSU_three] at cx
  have cj := hcomm _ (hfix _ ⟨jSU K p f, rfl⟩)
  rw [suMat_blockEmb_jSU] at cj
  have cd := hcomm _ (hfix _ ⟨dSU K p f ht (hσσ t), rfl⟩)
  rw [suMat_blockEmb_dSU] at cd
  have cP := hP (xSU K p f)
  rw [suMat_xSU] at cP
  have hxx : rootInvSU K p f (show 2 ≤ 3 by norm_num) *
      rootInvSU K p f (show 2 ≤ 3 by norm_num) = 1 := by
    rw [rootInvSU, ← map_mul, negOneSU_mul_self, map_one]
  have hxinv := inv_eq_of_mul_eq_one_right hxx
  have hxM2 : (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  rcases hφ with rfl | rfl
  · simp only [mapMatrix_refl] at cx cj cd cP hα
    obtain ⟨a, w, hGa, haw⟩ := core_id h2 hts G cx cj cd cP
    rcases mul_self_eq_mul_self_iff.mp haw with hw | hw
    · left
      intro s
      apply suMat_injective
      rw [hα s]
      have hGs : G = a • (1 : Matrix (Fin 3) (Fin 3) K) := by
        rw [hGa, ← hw]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hconj : G * suMat s = suMat s * G := by
        rw [hGs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
      rw [hconj, Matrix.mul_assoc, hGGi, Matrix.mul_one]
    · right
      intro s
      apply suMat_injective
      rw [hα s, suMat_mul, suMat_mul, hxinv, suMat_rootInvSU_three]
      have hGs : G = w • (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
        rw [hGa, hw]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hconj : G * suMat s = (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] * suMat s *
          !![-1, 0, 0; 0, -1, 0; 0, 0, 1]) * G := by
        rw [hGs, Matrix.smul_mul, Matrix.mul_smul]
        congr 1
        calc (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) * suMat s
            = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * suMat s *
              (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] * !![-1, 0, 0; 0, -1, 0; 0, 0, 1]) := by
              rw [hxM2, Matrix.mul_one]
          _ = !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * suMat s *
              !![-1, 0, 0; 0, -1, 0; 0, 0, 1] * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
              simp only [Matrix.mul_assoc]
      rw [hconj, Matrix.mul_assoc, hGGi, Matrix.mul_one]
  · exfalso
    have e1 : (unitaryInvolution K p f).mapMatrix
        (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
        !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e2 : (unitaryInvolution K p f).mapMatrix
        (!![0, 1, 0; -1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
        !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have e3 := mapMatrix_diag3 (unitaryInvolution K p f) (hσσ t)
    rw [e1] at cx
    rw [e2] at cj
    rw [e3] at cd
    rw [RingEquiv.mapMatrix_apply] at cP
    exact core_bar h2 hts (unitaryInvolution K p f) G cx cj cd hu cP

end Main

end CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
