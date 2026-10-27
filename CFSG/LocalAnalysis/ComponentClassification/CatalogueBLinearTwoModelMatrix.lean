module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjective

public section

namespace CFSG.ComponentClassification.CatalogueBLinearTwoModel

noncomputable section

open CFSG.GorensteinWalter CatalogueSchreierLinearTwo

theorem pslModel_two_eq_native_range (p f : ℕ) [Fact p.Prime] :
    Assembly.ComponentType.pslModel 2 p f =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := GaloisField p f)).range := by
  let K := GaloisField p f
  change (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) K →* Kˣ).ker.map
    Matrix.ProjGenLinGroup.mk =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    have hmem : A ∈ (Matrix.SpecialLinearGroup.toGL
        (n := Fin 2) (R := K)).range := by
      rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
      exact hA
    obtain ⟨B, hB⟩ := hmem
    refine ⟨psl2QuotientMap K B, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL B) =
      Matrix.ProjGenLinGroup.mk A
    exact congrArg Matrix.ProjGenLinGroup.mk hB
  · rintro ⟨g, rfl⟩
    obtain ⟨B, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) g
    refine ⟨Matrix.SpecialLinearGroup.toGL B, ?_, rfl⟩
    exact Matrix.SpecialLinearGroup.coeToGL_det B

@[expose] def nativePSLEquivPslModel (p f : ℕ) [Fact p.Prime] :
    PSL2 (GaloisField p f) ≃* Assembly.ComponentType.pslModel 2 p f :=
  (MonoidHom.ofInjective (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    (n := Fin 2) (R := GaloisField p f))).trans
      (MulEquiv.subgroupCongr (pslModel_two_eq_native_range p f).symm)

@[expose] def pslModelEquivCoordinateG (p f : ℕ) [Fact p.Prime] :
    Assembly.ComponentType.pslModel 2 p f ≃* coordinateG (GaloisField p f) :=
  (nativePSLEquivPslModel p f).symm.trans (pslEquivCoordinateG (GaloisField p f))

end

end CFSG.ComponentClassification.CatalogueBLinearTwoModel
