module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8W11
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary

section Shape

variable {K : Type} [Field K]

theorem core4one (σ φ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) {u v : K} (huv : u * v = 1)
    (hne : v ≠ u) (G : Matrix (Fin 4) (Fin 4) K) (hdet : G.det ≠ 0)
    (hd1 : G * !![φ u, 0, 0, 0; 0, φ v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![u, 0, 0, 0; 0, v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G)
    (hj1 : G * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G)
    (hA : ∀ a : K, ∃ b : K,
      G * !![φ a, φ b, 0, 0; -φ (σ b), φ (σ a), 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
        !![a, b, 0, 0; -σ b, σ a, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G) :
    (φ = RingEquiv.refl K ∧ ∃ a : K, a ≠ 0 ∧
      G = !![a, 0, 0, 0; 0, a, 0, 0; 0, 0, G 2 2, G 2 3; 0, 0, G 3 2, G 3 3]) ∨
    (φ = σ ∧ ∃ m : K, m ≠ 0 ∧
      G = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, G 2 2, G 2 3; 0, 0, G 3 2, G 3 3]) := by
  have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one huv
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, one_mul] at huv
    exact hne (huv.trans h.symm)
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, mul_one] at huv
    exact hne (h.trans huv.symm)
  have hφu1 : φ u ≠ 1 := fun h => hu1 (φ.injective (by rw [h, map_one]))
  have hφv1 : φ v ≠ 1 := fun h => hv1 (φ.injective (by rw [h, map_one]))
  have hφuv : φ u * φ v = 1 := by rw [← map_mul, huv, map_one]
  obtain ⟨g02, g03, g12, g13, g20, g21, g30, g31⟩ := offBlock_zero φ hu1 hv1 hφu1 hφv1 G hd1
  have b00 := congrFun (congrFun hd1 0) 0
  have b01 := congrFun (congrFun hd1 0) 1
  have b10 := congrFun (congrFun hd1 1) 0
  have b11 := congrFun (congrFun hd1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at b00 b01 b10 b11
  have hG : G = !![G 0 0, G 0 1, 0, 0; G 1 0, G 1 1, 0, 0; 0, 0, G 2 2, G 2 3;
      0, 0, G 3 2, G 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g02, g03, g12, g13, g20, g21, g30, g31]
  have hdet' : (G 0 0 * G 1 1 - G 0 1 * G 1 0) * (G 2 2 * G 3 3 - G 2 3 * G 3 2) ≠ 0 := by
    rw [← det_blockDiag4, ← hG]
    exact hdet
  have hdet1 : G 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := left_ne_zero_of_mul hdet'
  by_cases h00 : G 0 0 = 0
  ·
    have hm : G 0 1 * G 1 0 ≠ 0 := by
      intro h
      apply hdet1
      rw [h00, h]
      ring
    have g01 : G 0 1 ≠ 0 := left_ne_zero_of_mul hm
    have g10 : G 1 0 ≠ 0 := right_ne_zero_of_mul hm
    have hφv : φ v = u := eq_of_rel b01 g01
    have hφu : φ u = v := eq_of_rel b10 g10
    have g11 : G 1 1 = 0 := eq_zero_of_rel b11 (by rw [hφv]; exact hne.symm)
    have w1 : G 1 0 = -G 0 1 := by
      have e := congrFun (congrFun hj1 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, h00, g02, g03] at e
      linear_combination -e
    have hφσ : ∀ a, φ (σ a) = a := by
      intro a
      obtain ⟨b, hb⟩ := hA a
      have e := congrFun (congrFun hb 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, h00, g11, g02, g03] at e
      exact eq_of_rel e g01
    refine Or.inr ⟨RingEquiv.ext fun c => ?_, G 0 1, g01, ?_⟩
    · have := hφσ (σ c)
      rwa [hσσ] at this
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [h00, g11, g02, g03, g12, g13, g20, g21, g30, g31, w1]
  ·
    have hφu : φ u = u := eq_of_rel b00 h00
    have hφv : φ v = v := by
      have h1 : u * φ v = 1 := by rw [← hφu]; exact hφuv
      exact mul_left_cancel₀ hu0 (h1.trans huv.symm)
    have g01 : G 0 1 = 0 := eq_zero_of_rel b01 (by rw [hφv]; exact hne)
    have g10 : G 1 0 = 0 := eq_zero_of_rel b10 (by rw [hφu]; exact hne.symm)
    have w1 : G 1 1 = G 0 0 := by
      have e := congrFun (congrFun hj1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, g01, g02, g03] at e
      linear_combination -e
    have hφ : ∀ a, φ a = a := by
      intro a
      obtain ⟨b, hb⟩ := hA a
      have e := congrFun (congrFun hb 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, g01, g10, g02, g03] at e
      exact eq_of_rel e h00
    refine Or.inl ⟨RingEquiv.ext hφ, G 0 0, h00, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g01, g10, g02, g03, g12, g13, g20, g21, g30, g31, w1]

end Shape

section ShapeSU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_shape_one (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    (α : Su K p f 4 →* Su K p f 4) (g : GL (Fin 4) K) (φ : K ≃+* K)
    (hα : ∀ x : Su K p f 4, suMat (α x) =
      (g : Matrix (Fin 4) (Fin 4) K) * φ.mapMatrix (suMat x) *
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))
    (hfix0 : ∀ A : Su K p f 2, α (blockEmb K p f 4 2 0 (by norm_num) A) =
      blockEmb K p f 4 2 0 (by norm_num) A) :
    (φ = RingEquiv.refl K ∧ ∃ a : K, a ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![a, 0, 0, 0; 0, a, 0, 0;
        0, 0, (g : Matrix (Fin 4) (Fin 4) K) 2 2, (g : Matrix (Fin 4) (Fin 4) K) 2 3;
        0, 0, (g : Matrix (Fin 4) (Fin 4) K) 3 2, (g : Matrix (Fin 4) (Fin 4) K) 3 3]) ∨
    (φ = unitaryInvolution K p f ∧ ∃ m : K, m ≠ 0 ∧
      (g : Matrix (Fin 4) (Fin 4) K) = !![0, m, 0, 0; -m, 0, 0, 0;
        0, 0, (g : Matrix (Fin 4) (Fin 4) K) 2 2, (g : Matrix (Fin 4) (Fin 4) K) 2 3;
        0, 0, (g : Matrix (Fin 4) (Fin 4) K) 3 2, (g : Matrix (Fin 4) (Fin 4) K) 3 3]) := by
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
  have hj1 : G * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G := by
    refine key _ _ _ (hfix0 (jSU K p f)) ?_ ?_
    · rw [suMat_blockEmb_zero, suMat_jSU]
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
  exact core4one (unitaryInvolution K p f) φ hσσ (u := t) (v := unitaryInvolution K p f t)
    (by rw [mul_comm]; exact ht) hts G hdet hd1 hj1 hA

end ShapeSU

section Eigen

variable {K : Type} [Field K]

theorem exists_orthonormal_eigenbasis (σ : K ≃+* K) (hσ : IsUnitaryInvolution σ)
    (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) (haa : σ a * a = 1)
    (H : Matrix (Fin 2) (Fin 2) K) (hH2 : H * H = (a * a) • (1 : Matrix (Fin 2) (Fin 2) K))
    (hns : ¬ ∃ c : K, H = c • (1 : Matrix (Fin 2) (Fin 2) K))
    (hU : (H.map σ)ᵀ * H = 1) :
    ∃ p q r s : K, σ p * p + σ q * q = 1 ∧ σ r * r + σ s * s = 1 ∧ σ p * r + σ q * s = 0 ∧
      H 0 0 * p + H 0 1 * q = a * p ∧ H 1 0 * p + H 1 1 * q = a * q ∧
      H 0 0 * r + H 0 1 * s = -(a * r) ∧ H 1 0 * r + H 1 1 * s = -(a * s) := by
  obtain ⟨p, q, r, s, hdet, e1, e2, e3, e4⟩ := exists_eigenbasis h2 ha H hH2 hns
  have U00 := congrFun (congrFun hU 0) 0
  have U01 := congrFun (congrFun hU 0) 1
  have U10 := congrFun (congrFun hU 1) 0
  have U11 := congrFun (congrFun hU 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at U00 U01 U10 U11
  have E1 : σ (H 0 0) * σ p + σ (H 0 1) * σ q = σ a * σ p := by
    have := congrArg σ e1
    simpa [map_add, map_mul] using this
  have E2 : σ (H 1 0) * σ p + σ (H 1 1) * σ q = σ a * σ q := by
    have := congrArg σ e2
    simpa [map_add, map_mul] using this
  have hX : σ p * r + σ q * s = 0 := by
    have step1 : (σ (H 0 0) * σ p + σ (H 0 1) * σ q) * (H 0 0 * r + H 0 1 * s) +
        (σ (H 1 0) * σ p + σ (H 1 1) * σ q) * (H 1 0 * r + H 1 1 * s) =
        σ p * r + σ q * s := by
      linear_combination (σ p * r) * U00 + (σ p * s) * U01 + (σ q * r) * U10 + (σ q * s) * U11
    have step2 : (σ (H 0 0) * σ p + σ (H 0 1) * σ q) * (H 0 0 * r + H 0 1 * s) +
        (σ (H 1 0) * σ p + σ (H 1 1) * σ q) * (H 1 0 * r + H 1 1 * s) =
        (σ a * σ p) * (-(a * r)) + (σ a * σ q) * (-(a * s)) := by
      rw [E1, E2, e3, e4]
    have step3 : (σ a * σ p) * (-(a * r)) + (σ a * σ q) * (-(a * s)) =
        -(σ p * r + σ q * s) := by
      linear_combination (-(σ p * r + σ q * s)) * haa
    have hXX : σ p * r + σ q * s = -(σ p * r + σ q * s) := step1.symm.trans (step2.trans step3)
    have h : (2 : K) * (σ p * r + σ q * s) = 0 := by linear_combination hXX
    exact (mul_eq_zero.mp h).resolve_left h2
  have hXσ : p * σ r + q * σ s = 0 := by
    have := congrArg σ hX
    simp only [map_add, map_mul, hσ.invol, map_zero] at this
    linear_combination this
  have hN1 : σ p * p + σ q * q ≠ 0 := by
    intro hN
    have hp : σ p * (p * s - q * r) = 0 := by linear_combination s * hN - q * hX
    have hq : σ q * (p * s - q * r) = 0 := by linear_combination p * hX - r * hN
    have hp0 : p = 0 := by
      have := (mul_eq_zero.mp hp).resolve_right hdet
      simpa using this
    have hq0 : q = 0 := by
      have := (mul_eq_zero.mp hq).resolve_right hdet
      simpa using this
    apply hdet
    rw [hp0, hq0]
    ring
  have hN2 : σ r * r + σ s * s ≠ 0 := by
    intro hN
    have hr : σ r * (r * q - s * p) = 0 := by linear_combination q * hN - s * hXσ
    have hs : σ s * (r * q - s * p) = 0 := by linear_combination r * hXσ - p * hN
    have hdet' : r * q - s * p ≠ 0 := by
      intro h
      apply hdet
      linear_combination -h
    have hr0 : r = 0 := by
      have := (mul_eq_zero.mp hr).resolve_right hdet'
      simpa using this
    have hs0 : s = 0 := by
      have := (mul_eq_zero.mp hs).resolve_right hdet'
      simpa using this
    apply hdet
    rw [hr0, hs0]
    ring
  have hfix1 : σ (σ p * p + σ q * q)⁻¹ = (σ p * p + σ q * q)⁻¹ := by
    rw [map_inv₀]
    congr 1
    simp only [map_add, map_mul, hσ.invol]
    ring
  have hfix2 : σ (σ r * r + σ s * s)⁻¹ = (σ r * r + σ s * s)⁻¹ := by
    rw [map_inv₀]
    congr 1
    simp only [map_add, map_mul, hσ.invol]
    ring
  obtain ⟨b₁, hb₁⟩ := hσ.exists_norm hfix1
  obtain ⟨b₂, hb₂⟩ := hσ.exists_norm hfix2
  refine ⟨b₁ * p, b₁ * q, b₂ * r, b₂ * s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [map_mul]
    have : σ b₁ * b₁ * (σ p * p + σ q * q) = 1 := by rw [hb₁]; exact inv_mul_cancel₀ hN1
    linear_combination this
  · simp only [map_mul]
    have : σ b₂ * b₂ * (σ r * r + σ s * s) = 1 := by rw [hb₂]; exact inv_mul_cancel₀ hN2
    linear_combination this
  · simp only [map_mul]
    linear_combination (σ b₁ * b₂) * hX
  · linear_combination b₁ * e1
  · linear_combination b₁ * e2
  · linear_combination b₂ * e3
  · linear_combination b₂ * e4

theorem conjTr_adapted_mul_self (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) {p q r s : K}
    (h1 : σ p * p + σ q * q = 1) (h2 : σ r * r + σ s * s = 1) (h3 : σ p * r + σ q * s = 0) :
    conjTr σ (!![0, 1, 0, 0; 0, 0, 1, 0; p, 0, 0, r; q, 0, 0, s] : Matrix (Fin 4) (Fin 4) K) *
      !![0, 1, 0, 0; 0, 0, 1, 0; p, 0, 0, r; q, 0, 0, s] = 1 := by
  have h3' : p * σ r + q * σ s = 0 := by
    have := congrArg σ h3
    simp only [map_add, map_mul, hσσ, map_zero] at this
    linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_four]
  · exact h1
  · exact h3
  · linear_combination h3'
  · exact h2

end Eigen

section Scalar

variable {K : Type} [Field K]

theorem scalar_of_commute_mix {l L00 L01 L10 L11 : K}
    (hmix : (!![l, 0, 0, 0; 0, l, 0, 0; 0, 0, L00, L01; 0, 0, L10, L11] :
        Matrix (Fin 4) (Fin 4) K) * !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] =
      !![0, 0, 1, 0; 0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1] *
        !![l, 0, 0, 0; 0, l, 0, 0; 0, 0, L00, L01; 0, 0, L10, L11])
    (hJ : (!![l, 0, 0, 0; 0, l, 0, 0; 0, 0, L00, L01; 0, 0, L10, L11] :
        Matrix (Fin 4) (Fin 4) K) * !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] =
      !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] *
        !![l, 0, 0, 0; 0, l, 0, 0; 0, 0, L00, L01; 0, 0, L10, L11]) :
    L00 = l ∧ L01 = 0 ∧ L10 = 0 ∧ L11 = l := by
  have e20 := congrFun (congrFun hmix 2) 0
  have e30 := congrFun (congrFun hmix 3) 0
  have e23 := congrFun (congrFun hmix 2) 3
  have f22 := congrFun (congrFun hJ 2) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e20 e30 e23 f22
  exact ⟨e20, e23, e30, f22.symm.trans e20⟩

end Scalar

end CFSG.ClassicalInvolution.Asc77.T8W
