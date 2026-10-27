module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix QuadraticMap CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K]

theorem sixBar_mem (delta : K) (X : sixSubmodule delta) :
    sixBar delta X.val ∈ sixSubmodule delta := by
  constructor
  · rw [← sixBar_transpose, X.property.1, sixBar_neg]
  · have h := congrArg (sixBar delta) X.property.2
    rw [sixBar_sharp, sixBar_mul, sixBar_mul, sixBar_gram] at h
    exact h

@[expose] def sixGammaLinear (delta : K) : sixSubmodule delta ≃ₗ[K] sixSubmodule delta where
  toFun X := ⟨sixBar delta X.val, sixBar_mem delta X⟩
  invFun X := ⟨sixBar delta X.val, sixBar_mem delta X⟩
  left_inv X := Subtype.ext (sixBar_square delta X.val)
  right_inv X := Subtype.ext (sixBar_square delta X.val)
  map_add' X Y := Subtype.ext (sixBar_add delta X.val Y.val)
  map_smul' a X := Subtype.ext (sixBar_smul delta a X.val)

theorem sixGammaLinear_val (delta : K) (X : sixSubmodule delta) :
    (sixGammaLinear delta X).val = sixBar delta X.val := rfl

theorem sixGammaLinear_form (delta : K) (X : sixSubmodule delta) :
    sixForm delta (sixGammaLinear delta X) = sixForm delta X := by
  rw [sixForm_apply, sixForm_apply]
  simp [sixGammaLinear, sixBar, conjugation]

@[expose] def sixGamma (delta : K) : SixIsometries delta :=
  ⟨sixGammaLinear delta,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (sixGammaLinear_form delta)⟩

theorem sixGamma_val (delta : K) (X : sixSubmodule delta) :
    ((sixGamma delta).val X).val = sixBar delta X.val := rfl

theorem sixGamma_square (delta : K) : sixGamma delta * sixGamma delta = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact Subtype.ext (sixBar_square delta X.val)

theorem sixBar_det (delta : K) (X : Matrix (Fin 4) (Fin 4) (extension delta)) :
    (sixBar delta X).det = conjugation delta X.det :=
  ((conjugation delta).map_det X).symm

@[expose] def sixConjugateD (delta : K) : sixSimilitudes delta →* sixSimilitudes delta where
  toFun g := ⟨GeneralLinearGroup.map (conjugation delta).toRingHom g.val, by
    refine ⟨sixMultiplier delta g, ?_, ?_⟩
    · have h := congrArg (sixBar delta) (sixMultiplier_spec delta g)
      rw [sixBar_mul, sixBar_mul, sixBar_transpose, sixBar_square,
        sixBar_gram, sixBar_smul, sixBar_gram] at h
      change (sixBar delta (sixBar delta g.val.val)).transpose * sixGram (extension delta) *
        sixBar delta g.val.val = _
      rw [sixBar_square]
      exact h
    · change (sixBar delta g.val.val).det = _
      rw [sixBar_det, sixMultiplier_det]
      exact (conjugation delta).commutes _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ g.val h.val)

theorem sixConjugateD_val (delta : K) (g : sixSimilitudes delta) :
    (sixConjugateD delta g).val.val = sixBar delta g.val.val := rfl

theorem sixMultiplier_conjugate (delta : K) (g : sixSimilitudes delta) :
    sixMultiplier delta (sixConjugateD delta g) = sixMultiplier delta g := by
  apply sixMultiplier_eq_of_equation
  change (sixBar delta (sixBar delta g.val.val)).transpose * sixGram (extension delta) *
    sixBar delta g.val.val = _
  have h := congrArg (sixBar delta) (sixMultiplier_spec delta g)
  rw [sixBar_mul, sixBar_mul, sixBar_transpose, sixBar_gram,
    sixBar_smul, sixBar_gram] at h
  exact h

theorem sixConjugateD_square (delta : K) (g : sixSimilitudes delta) :
    sixConjugateD delta (sixConjugateD delta g) = g := by
  apply Subtype.ext
  apply Units.ext
  exact sixBar_square delta g.val.val

theorem sixGamma_kappa_gamma (delta : K) [Fact (¬ IsSquare delta)] (h2 : (2 : K) ≠ 0)
    (g : sixSimilitudes delta) :
    sixGamma delta * kappa delta h2 g * sixGamma delta =
      kappa delta h2 (sixConjugateD delta g) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  apply Subtype.ext
  change sixBar delta (sixCongruenceMatrix delta g (sixBar delta X.val)) = _
  rw [sixCongruenceMatrix, sixBar_smul, sixBar_mul, sixBar_mul,
    sixBar_square, sixBar_transpose]
  rw [kappa_val, sixMultiplier_conjugate, sixConjugateD_val]

end CFSG.ComponentClassification.CatalogueBOrthogonalSix
