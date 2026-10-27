module

public import CFSG.GH74.Generic.BProg.B2.GenLocL4QBasis
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction

public section

namespace CFSG.GH74.Generic.BProg.B2

open Matrix CFSG CFSG.ComponentClassification

namespace GenLocL4Q

variable {F : Type} [Field F]

theorem slConj_commute {R : GL (Fin 4) F} {x X : Matrix (Fin 4) (Fin 4) F}
    (h : x * (R : Matrix (Fin 4) (Fin 4) F) = (R : Matrix (Fin 4) (Fin 4) F) * X)
    (g : Matrix.SpecialLinearGroup (Fin 4) F)
    (hg : (g : Matrix (Fin 4) (Fin 4) F) * X = X * (g : Matrix (Fin 4) (Fin 4) F)) :
    ((CatalogueBHigherLinearAction.slConjugation 4 F R g : Matrix.SpecialLinearGroup (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F) * x =
      x * (CatalogueBHigherLinearAction.slConjugation 4 F R g : Matrix.SpecialLinearGroup (Fin 4) F) := by
  rw [CatalogueBHigherLinearAction.slConjugation_matrix]
  have h1 : ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x =
      X * ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    calc ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x
        = ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x *
            ((R : Matrix (Fin 4) (Fin 4) F) * ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (x * (R : Matrix (Fin 4) (Fin 4) F)) *
            ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
      _ = X * ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          rw [h, ← Matrix.mul_assoc, Units.inv_mul, one_mul]
  calc (R : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
        ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x
      = (R : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) *
          (((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * x)) := by simp only [Matrix.mul_assoc]
    _ = (R : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) * X) *
          ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [h1]; simp only [Matrix.mul_assoc]
    _ = (R : Matrix (Fin 4) (Fin 4) F) * (X * (g : Matrix (Fin 4) (Fin 4) F)) *
          ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [hg]
    _ = (R : Matrix (Fin 4) (Fin 4) F) * X * ((g : Matrix (Fin 4) (Fin 4) F) *
          ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by simp only [Matrix.mul_assoc]
    _ = x * (R : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) *
          ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by rw [h]
    _ = x * ((R : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) *
          ((R⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by simp only [Matrix.mul_assoc]

theorem eq_top_of_commuting_centralizers [Finite F] (hF : ringChar F ≠ 2) {c m : F} (hc : c ≠ 0)
    (hm : m ≠ 0) {x y : Matrix (Fin 4) (Fin 4) F} (hx : x * x = c • 1) (hy : y * y = m • 1)
    (hxy : x * y = -(y * x)) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F))
    (hX : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * x = x * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (hY : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * y = y * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ)
    (hXY : ∀ g : Matrix.SpecialLinearGroup (Fin 4) F,
      (g : Matrix (Fin 4) (Fin 4) F) * (x * y) = (x * y) * (g : Matrix (Fin 4) (Fin 4) F) → g ∈ Γ) :
    Γ = ⊤ := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨R, hRu, hxR, hyR⟩ := exists_regular_basis hF hc hm hx hy hxy
  let Rg : GL (Fin 4) F := hRu.unit
  have hRg : (Rg : Matrix (Fin 4) (Fin 4) F) = R := hRu.unit_spec
  have hxR' : x * (Rg : Matrix (Fin 4) (Fin 4) F) = (Rg : Matrix (Fin 4) (Fin 4) F) * Xr c := by
    rw [hRg]; exact hxR
  have hyR' : y * (Rg : Matrix (Fin 4) (Fin 4) F) = (Rg : Matrix (Fin 4) (Fin 4) F) * Yr m := by
    rw [hRg]; exact hyR
  have hxyR' : (x * y) * (Rg : Matrix (Fin 4) (Fin 4) F) =
      (Rg : Matrix (Fin 4) (Fin 4) F) * (Xr c * Yr m) := by
    rw [hRg, Matrix.mul_assoc, hyR, ← Matrix.mul_assoc, hxR, Matrix.mul_assoc]
  let φ : MulAut (Matrix.SpecialLinearGroup (Fin 4) F) := CatalogueBHigherLinearAction.slConjugation 4 F Rg
  let ΓR : Subgroup (Matrix.SpecialLinearGroup (Fin 4) F) := Γ.comap φ.toMonoidHom
  have hΓR : ΓR = ⊤ := by
    refine eq_top_of_centralizers (m := m) h2 hc ΓR ?_ ?_ ?_
    · intro g hg
      exact hX _ (slConj_commute hxR' g hg)
    · intro g hg
      exact hY _ (slConj_commute hyR' g hg)
    · intro g hg
      exact hXY _ (slConj_commute hxyR' g hg)
  rw [eq_top_iff]
  intro h _
  have hmem : φ.symm h ∈ ΓR := hΓR ▸ Subgroup.mem_top _
  have : φ (φ.symm h) ∈ Γ := hmem
  rwa [MulEquiv.apply_symm_apply] at this

end GenLocL4Q

end CFSG.GH74.Generic.BProg.B2
