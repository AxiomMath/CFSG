module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.UnitaryThreeRecognition.Model CFSG.BenderSuzuki.MatrixGroups
  CFSG.BenderSuzuki.External CFSG.ClassicalGroups.Unitary

section Coordinates

variable {K : Type} [Field K] (J : HermitianForm 3 K)

theorem exists_inverting_coord_of_fst_ne (hσ : IsUnitaryInvolution J.conj) (z : Coord J)
    (hz : (z : K × K).1 ≠ 0) :
    ∃ w : Coord J, w * hermitianTorusAction J (-1) z * w⁻¹ = z⁻¹ := by
  obtain ⟨⟨a, b⟩, hzab⟩ := z
  have hz' : b + J.conj b + a * J.conj a = 0 := hzab
  have hσa : J.conj a ≠ 0 := by simpa using hz
  have hinv : ∀ c, J.conj (J.conj c) = c := hσ.invol
  set w₁ : K := J.conj b / J.conj a with hw₁
  have hw1 : w₁ * J.conj a = J.conj b := div_mul_cancel₀ _ hσa
  have hw2 : a * J.conj w₁ = b := by
    rw [hw₁, map_div₀, hinv, hinv]
    field_simp
  obtain ⟨c, hc⟩ := hσ.trace_surj (-(w₁ * J.conj w₁)) (by rw [map_neg, map_mul, hinv, mul_comm])
  refine ⟨⟨(w₁, c), by show c + J.conj c + w₁ * J.conj w₁ = 0; rw [hc]; ring⟩, ?_⟩
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val, coord_inv_val, coord_inv_val, torusAction_val]
  simp
  linear_combination hc + hw1 - hw2

theorem exists_inverting_coord_of_fst_eq (hσ : IsUnitaryInvolution J.conj) (z : Coord J)
    (hz : (z : K × K).1 = 0) :
    ∃ k : Kˣ, hermitianTorusAction J k z = z⁻¹ := by
  obtain ⟨⟨a, b⟩, hzab⟩ := z
  have hz' : b + J.conj b + a * J.conj a = 0 := hzab
  have ha : a = 0 := hz
  subst ha
  have hbσ : J.conj b = -b := by
    have : b + J.conj b = 0 := by simpa using hz'
    linear_combination this
  obtain ⟨c, hc⟩ := hσ.exists_norm (d := -1) (by rw [map_neg, map_one])
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Subtype.ext
  rw [torusAction_val, coord_inv_val]
  simp only [Units.val_mk0, zero_mul, hbσ]
  refine Prod.ext (by simp) ?_
  show b * (J.conj c)⁻¹ * c⁻¹ = -b
  have : J.conj c * c = -1 := hc
  rw [mul_assoc, ← mul_inv, this]
  simp

end Coordinates

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem exists_inverting_rootGroup {t : ProjectiveSpecialUnitaryMatrixGroup J}
    (ht : t ∈ rootGroup J hJ) :
    ∃ n ∈ Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      n * t * n⁻¹ = t⁻¹ := by
  have hσ := isUnitaryInvolution_conj J hK hfix
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 ht
  by_cases hz : (z : K × K).1 = 0
  · obtain ⟨k, hk⟩ := exists_inverting_coord_of_fst_eq J hσ z hz
    refine ⟨torus J hJ k, torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ k),
      ?_⟩
    rw [torus_mul_root_mul_inv, hk, map_inv]
  · obtain ⟨w, hw⟩ := exists_inverting_coord_of_fst_ne J hσ z hz
    refine ⟨root J hJ w * torus J hJ (-1),
      mul_mem (Subgroup.le_normalizer (root_mem_rootGroup J hJ w))
        (torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ (-1))), ?_⟩
    calc root J hJ w * torus J hJ (-1) * root J hJ z * (root J hJ w * torus J hJ (-1))⁻¹
        = root J hJ w * (torus J hJ (-1) * root J hJ z * (torus J hJ (-1))⁻¹) *
            (root J hJ w)⁻¹ := by group
      _ = root J hJ (w * hermitianTorusAction J (-1) z * w⁻¹) := by
          rw [torus_mul_root_mul_inv, map_mul, map_mul, map_inv]
      _ = (root J hJ z)⁻¹ := by rw [hw, map_inv]

end Model

end CFSG.AGLEmbedding.UnitaryModel
