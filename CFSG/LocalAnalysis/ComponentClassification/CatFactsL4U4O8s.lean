module

public import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
public import TauCeti.Algebra.Group.Units.Basic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4O8a
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIO

open CFSG Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal TauCeti
open CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {K : Type} [Field K] {b c : K}

theorem polar_isometryEquiv {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
    [Module K V₂] {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂)
    (x y : V₁) : polar Q₂ (e x) (e y) = polar Q₁ x y := by
  simp only [polar, ← map_add, e.map_app]

@[expose] def hypQ8 (i : Fin 3) : HypPair (Q8 K b c) where
  e := coordinateMinusIsometry 4 K (by norm_num) b c
    (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).e
  f := coordinateMinusIsometry 4 K (by norm_num) b c
    (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).f
  Q_e := by
    rw [QuadraticMap.IsometryEquiv.map_app]
    exact (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).Q_e
  Q_f := by
    rw [QuadraticMap.IsometryEquiv.map_app]
    exact (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).Q_f
  polar_ef := by
    rw [polar_isometryEquiv]
    exact (ClassicalGroups.Orthogonal.minusPair (n := 4) K b c i).polar_ef

theorem hypQ8_orth {i j : Fin 3} (hij : i ≠ j) : (hypQ8 (K := K) (b := b) (c := c) i).Orth
    (hypQ8 j) := by
  have h := ClassicalGroups.Orthogonal.minusPair_orth (K := K) (b := b) (c := c) (n := 4) hij
  exact ⟨(polar_isometryEquiv _ _ _).trans h.ee, (polar_isometryEquiv _ _ _).trans h.ef,
    (polar_isometryEquiv _ _ _).trans h.fe, (polar_isometryEquiv _ _ _).trans h.ff⟩

theorem reflect_four_mem [Finite K] (h2K : (2 : K) ≠ 0) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (a₁ a₂ a₃ a₄ : Fin (2 * 4) → K) (h₁ : Q8 K b c a₁ ≠ 0) (h₂ : Q8 K b c a₂ ≠ 0)
    (h₃ : Q8 K b c a₃ ≠ 0) (h₄ : Q8 K b c a₄ ≠ 0)
    (hsq : IsSquare (Q8 K b c a₁ * Q8 K b c a₂ * Q8 K b c a₃ * Q8 K b c a₄)) :
    ∃ hmem : reflect (Q8 K b c) a₁ * reflect (Q8 K b c) a₂ * reflect (Q8 K b c) a₃ *
        reflect (Q8 K b c) a₄ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q8 K b c),
      (⟨_, hmem⟩ : TauCeti.QuadraticMap.orthogonalGroup (Q8 K b c)) ∈
        orthogonalDerived (Q8 K b c) := by
  let : Invertible (2 : K) := invertibleOfNonzero h2K
  let : Invertible (Q8 K b c a₁) := invertibleOfNonzero h₁
  let : Invertible (Q8 K b c a₂) := invertibleOfNonzero h₂
  let : Invertible (Q8 K b c a₃) := invertibleOfNonzero h₃
  let : Invertible (Q8 K b c a₄) := invertibleOfNonzero h₄
  set g := TauCeti.QuadraticMap.reflectionOrthogonal (Q8 K b c) a₁ *
    TauCeti.QuadraticMap.reflectionOrthogonal (Q8 K b c) a₂ *
    TauCeti.QuadraticMap.reflectionOrthogonal (Q8 K b c) a₃ *
    TauCeti.QuadraticMap.reflectionOrthogonal (Q8 K b c) a₄ with hg
  have hgv : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) = reflect (Q8 K b c) a₁ *
      reflect (Q8 K b c) a₂ * reflect (Q8 K b c) a₃ * reflect (Q8 K b c) a₄ := by
    rw [hg, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect,
      ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect,
      ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect,
      ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect]
  have hmem : reflect (Q8 K b c) a₁ * reflect (Q8 K b c) a₂ * reflect (Q8 K b c) a₃ *
      reflect (Q8 K b c) a₄ ∈ TauCeti.QuadraticMap.orthogonalGroup (Q8 K b c) := by
    rw [← hgv]
    exact g.property
  have hgg : (⟨_, hmem⟩ : TauCeti.QuadraticMap.orthogonalGroup (Q8 K b c)) = g :=
    Subtype.ext hgv.symm
  refine ⟨hmem, ?_⟩
  rw [hgg]
  have hnd := (regular_coordinateQuadMinus 4 K b c (by norm_num) hirr).1
  have hidx := ClassicalInvolution.orthogonalGroup_index_four hnd
    (hypQ8_orth (K := K) (b := b) (c := c) (i := 0) (j := 1) (by decide))
    (hypQ8_orth (K := K) (b := b) (c := c) (i := 0) (j := 2) (by decide))
    (hypQ8_orth (K := K) (b := b) (c := c) (i := 1) (j := 2) (by decide))
  have hdet : ClassicalInvolution.detSpinorNorm
      (QuadraticMap.nondegenerate_polar_iff.mp hnd) g = 1 := by
    rw [hg, map_mul, map_mul, map_mul, ClassicalInvolution.detSpinorNorm_reflectionOrthogonal,
      ClassicalInvolution.detSpinorNorm_reflectionOrthogonal,
      ClassicalInvolution.detSpinorNorm_reflectionOrthogonal,
      ClassicalInvolution.detSpinorNorm_reflectionOrthogonal]
    simp only [Prod.mk_mul_mk, ← map_mul]
    refine Prod.ext (by norm_num) ?_
    change squareClassHom _ = 1
    rw [← MonoidHom.mem_ker, ker_squareClassHom, Subgroup.mem_square,
      ← isSquare_units_val_iff]
    simpa [Units.val_mul] using hsq
  have hE := (hidx.2 g).mpr hdet
  rw [← commutator_coordinateQuadMinus 4 K b c (by norm_num) hirr,
    ← Subgroup.map_subtype_commutator] at hE
  obtain ⟨g', hg', hgg'⟩ := hE
  have : g' = g := Subtype.ext hgg'
  rw [this] at hg'
  exact hg'

end OIO

end CFSG.ComponentClassification.CatFactsL4U4
