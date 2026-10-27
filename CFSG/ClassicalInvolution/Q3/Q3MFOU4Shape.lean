module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Mat

public section

namespace CFSG.ClassicalInvolution.Q3.Q3MFOU4

open Matrix CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

variable {K : Type} [Field K]

theorem core4_one (σ φ : K ≃+* K) {u v : K} (huv : u * v = 1) (hne : v ≠ u) (hσu : σ u = v)
    (hσv : σ v = u) (hφ : φ = RingEquiv.refl K ∨ φ = σ) (G : Matrix (Fin 4) (Fin 4) K)
    (hdet : G.det ≠ 0)
    (hd1 : G * !![φ u, 0, 0, 0; 0, φ v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![u, 0, 0, 0; 0, v, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G)
    (hj1 : G * !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] =
      !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] * G) :
    (G 0 2 = 0 ∧ G 0 3 = 0 ∧ G 1 2 = 0 ∧ G 1 3 = 0 ∧ G 2 0 = 0 ∧ G 2 1 = 0 ∧ G 3 0 = 0 ∧
      G 3 1 = 0) ∧
    ((φ = RingEquiv.refl K ∧ G 0 1 = 0 ∧ G 1 0 = 0 ∧ G 1 1 = G 0 0 ∧ G 0 0 ≠ 0) ∨
      (φ = σ ∧ G 0 0 = 0 ∧ G 1 1 = 0 ∧ G 1 0 = -G 0 1 ∧ G 0 1 ≠ 0)) := by
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
  obtain ⟨g02, g03, g12, g13, g20, g21, g30, g31⟩ := offBlock_zero φ hu1 hv1 hφu1 hφv1 G hd1
  have b00 := congrFun (congrFun hd1 0) 0
  have b01 := congrFun (congrFun hd1 0) 1
  have b10 := congrFun (congrFun hd1 1) 0
  have b11 := congrFun (congrFun hd1 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at b00 b01 b10 b11
  refine ⟨⟨g02, g03, g12, g13, g20, g21, g30, g31⟩, ?_⟩
  have hG : G = !![G 0 0, G 0 1, 0, 0; G 1 0, G 1 1, 0, 0; 0, 0, G 2 2, G 2 3;
      0, 0, G 3 2, G 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g02, g03, g12, g13, g20, g21, g30, g31]
  have hdet' : (G 0 0 * G 1 1 - G 0 1 * G 1 0) * (G 2 2 * G 3 3 - G 2 3 * G 3 2) ≠ 0 := by
    rw [← det_blockDiag4, ← hG]
    exact hdet
  have hdet1 : G 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := left_ne_zero_of_mul hdet'
  rcases hφ with hφ | hφ
  ·
    have b01' : G 0 1 * v = u * G 0 1 := by simpa [hφ] using b01
    have b10' : G 1 0 * u = v * G 1 0 := by simpa [hφ] using b10
    have g01 : G 0 1 = 0 := eq_zero_of_rel b01' hne
    have g10 : G 1 0 = 0 := eq_zero_of_rel b10' hne.symm
    have h00 : G 0 0 ≠ 0 := by
      intro h
      apply hdet1
      rw [h, g01]
      ring
    have w1 : G 1 1 = G 0 0 := by
      have e := congrFun (congrFun hj1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_four, g01, g02, g03] at e
      linear_combination -e
    exact Or.inl ⟨hφ, g01, g10, w1, h00⟩
  ·
    have b00' : G 0 0 * v = u * G 0 0 := by simpa [hφ, hσu] using b00
    have b11' : G 1 1 * u = v * G 1 1 := by simpa [hφ, hσv] using b11
    have g00 : G 0 0 = 0 := eq_zero_of_rel b00' hne
    have g11 : G 1 1 = 0 := eq_zero_of_rel b11' hne.symm
    have hm : G 0 1 * G 1 0 ≠ 0 := by
      intro h
      apply hdet1
      rw [g00, h]
      ring
    have g01 : G 0 1 ≠ 0 := left_ne_zero_of_mul hm
    have w1 : G 1 0 = -G 0 1 := by
      have e := congrFun (congrFun hj1 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_four, g00, g02, g03] at e
      linear_combination -e
    exact Or.inr ⟨hφ, g00, g11, w1, g01⟩

end CFSG.ClassicalInvolution.Q3.Q3MFOU4
