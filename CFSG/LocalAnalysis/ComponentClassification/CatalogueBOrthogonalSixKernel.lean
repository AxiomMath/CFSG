module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixKernelMatrix
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixKernelSpan

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

@[expose] def sixSpecialNegIdentity (delta : K) : sixSpecialUnitary delta :=
  ⟨⟨-1, -1, by simp, by simp⟩, by
    constructor
    · change (sixBar delta (-1)).transpose * sixGram (extension delta) * (-1) = _
      have hb : sixBar delta (1 : Matrix (Fin 4) (Fin 4) (extension delta)) = 1 := by
        apply Matrix.ext
        intro i j
        simp [sixBar, Matrix.one_apply]
      rw [sixBar_neg, hb]
      simp
    · change (- (1 : Matrix (Fin 4) (Fin 4) (extension delta))).det = 1
      simp [Matrix.det_neg]
      ring⟩

theorem sixSpecialNegIdentity_val (delta : K) :
    (sixSpecialNegIdentity delta).val.val =
      -(1 : Matrix (Fin 4) (Fin 4) (extension delta)) := rfl

theorem sixSpecialNegIdentity_square (delta : K) :
    sixSpecialNegIdentity delta * sixSpecialNegIdentity delta = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (- (1 : Matrix (Fin 4) (Fin 4) (extension delta))) * (-1) = 1
  simp

theorem sixSpecialNegIdentity_central (delta : K) :
    sixSpecialNegIdentity delta ∈ Subgroup.center (sixSpecialUnitary delta) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  apply Units.ext
  change g.val.val * (-1) = (-1) * g.val.val
  simp

theorem sixSpecialNegIdentity_action (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) : sixSpecialKappa delta h2 (sixSpecialNegIdentity delta) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  rw [sixSpecialKappa_val, sixSpecialNegIdentity_val]
  change (- (1 : Matrix (Fin 4) (Fin 4) (extension delta))) * X.val *
    (- (1 : Matrix (Fin 4) (Fin 4) (extension delta))).transpose = X.val
  simp

theorem sixSpecialKappa_kernel_matrix_iff (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : sixSpecialUnitary delta) :
    sixSpecialKappa delta h2 g = 1 ↔
      g.val.val = 1 ∨ g.val.val = -(1 : Matrix (Fin 4) (Fin 4) (extension delta)) := by
  constructor
  · intro hg
    exact fixed_skew_matrix_sign g.val (sixSpecial_fixed_skew delta h2 g hg)
  · rintro (hg | hg)
    · have he : g = 1 := Subtype.ext (Units.ext hg)
      rw [he, map_one]
    · have he : g = sixSpecialNegIdentity delta := Subtype.ext (Units.ext hg)
      rw [he, sixSpecialNegIdentity_action delta h2]

theorem sixSpecialKappa_kernel_iff (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) (g : sixSpecialUnitary delta) :
    g ∈ (sixSpecialKappa delta h2).ker ↔ g = 1 ∨ g = sixSpecialNegIdentity delta := by
  rw [MonoidHom.mem_ker, sixSpecialKappa_kernel_matrix_iff delta h2]
  constructor
  · rintro (hg | hg)
    · exact Or.inl (Subtype.ext (Units.ext hg))
    · exact Or.inr (Subtype.ext (Units.ext hg))
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem sixSpecialKappa_kernel_central (delta : K) [Fact (¬ IsSquare delta)]
    (h2 : (2 : K) ≠ 0) :
    (sixSpecialKappa delta h2).ker ≤ Subgroup.center (sixSpecialUnitary delta) := by
  intro g hg
  obtain rfl | rfl := (sixSpecialKappa_kernel_iff delta h2 g).mp hg
  · exact (Subgroup.center _).one_mem
  · exact sixSpecialNegIdentity_central delta

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
