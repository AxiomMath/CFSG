module
public import CFSG.LieType.AlgebraicGroups.FixedComponentCentralIsogeny
public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL
public import CFSG.LieType.AlgebraicGroups.G2ExceptionalComorphism
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import TauCeti.Algebra.AlgebraicGroup.ConstantGroup.Points
public import TauCeti.Algebra.AlgebraicGroup.Torus.SmoothConnected

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open WithConv
open scoped CFSG.ConvolutionPoints

variable {k : Type} [Field k] [IsAlgClosed k]
variable {A : Type} [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem innerCoordinate_points (M : Subgroup (WithConv (A →ₐ[k] k)))
    (a : WithConv (A →ₐ[k] k)) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    ∀ y ∈ subgroupPoints M, y.comp (innerCo a) ∈ subgroupPoints M := by
  intro y hy
  change toConv (y.comp (innerCo a)) ∈ M
  rw [point_comp_innerCo]
  exact ha (toConv y) hy

def innerCoordinate (M : Subgroup (WithConv (A →ₐ[k] k)))
    (a : WithConv (A →ₐ[k] k))
    (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    (A ⧸ subgroupIdeal M) →ₐc[k] (A ⧸ subgroupIdeal M) := by
  let : IsReduced (A ⧸ subgroupIdeal M) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (isRadical_pointsIdeal _)
  have hpts := innerCoordinate_points M a ha
  exact bialgHomOfPointMul (quotientCo M (innerCo a) hpts)
    (quotientCo_pointMul M _ hpts (by
      intro y z
      rw [point_comp_innerCo, point_comp_innerCo, point_comp_innerCo]
      group))

theorem innerCoordinate_toAlgHom (M : Subgroup (WithConv (A →ₐ[k] k)))
    (a : WithConv (A →ₐ[k] k)) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    (innerCoordinate M a ha).toAlgHom.comp (Ideal.Quotient.mkₐ k (subgroupIdeal M)) =
      (Ideal.Quotient.mkₐ k (subgroupIdeal M)).comp (innerCo a) := by
  let : IsReduced (A ⧸ subgroupIdeal M) :=
    (Ideal.isRadical_iff_quotient_reduced _).1 (isRadical_pointsIdeal _)
  rw [innerCoordinate, coe_bialgHomOfPointMul]
  exact quotientCo_comp_mkₐ M (innerCo a) (innerCoordinate_points M a ha)

theorem innerCoordinate_cube (M : Subgroup (WithConv (A →ₐ[k] k)))
    (a : WithConv (A →ₐ[k] k)) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    (ha3 : a ^ 3 = 1) :
    ((innerCoordinate M a ha).comp (innerCoordinate M a ha)).comp (innerCoordinate M a ha) =
      BialgHom.id k (A ⧸ subgroupIdeal M) := by
  suffices h : (((innerCoordinate M a ha).comp (innerCoordinate M a ha)).comp
      (innerCoordinate M a ha)).toAlgHom = (BialgHom.id k (A ⧸ subgroupIdeal M)).toAlgHom by
    exact BialgHom.ext fun x => AlgHom.congr_fun h x
  apply Ideal.Quotient.algHom_ext k
  rw [BialgHom.comp_toAlgHom, BialgHom.comp_toAlgHom]
  let σ := (innerCoordinate M a ha).toAlgHom
  let π := Ideal.Quotient.mkₐ k (subgroupIdeal M)
  let γ := innerCo a
  have hπ : σ.comp π = π.comp γ := innerCoordinate_toAlgHom M a ha
  have ha3' : a * a * a = 1 := by simpa [pow_succ] using ha3
  have hγ : (γ.comp γ).comp γ = AlgHom.id k A := by
    dsimp only [γ]
    rw [innerCo_comp_innerCo, innerCo_comp_innerCo, ← mul_assoc, ha3', innerCo_one]
  change ((σ.comp σ).comp σ).comp π = (AlgHom.id k _).comp π
  calc
    ((σ.comp σ).comp σ).comp π = σ.comp (σ.comp (σ.comp π)) := by
      simp only [AlgHom.comp_assoc]
    _ = σ.comp (σ.comp (π.comp γ)) := by rw [hπ]
    _ = σ.comp ((π.comp γ).comp γ) := by
      have h := congrArg (fun t => t.comp γ) hπ
      have h' : σ.comp (π.comp γ) = (π.comp γ).comp γ := by
        simpa only [AlgHom.comp_assoc] using h
      exact congrArg (fun t => σ.comp t) h'
    _ = (π.comp γ).comp (γ.comp γ) := by
      have h := congrArg (fun t => t.comp (γ.comp γ)) hπ
      simpa only [AlgHom.comp_assoc] using h
    _ = π.comp ((γ.comp γ).comp γ) := by simp only [AlgHom.comp_assoc]
    _ = π := by rw [hγ, AlgHom.comp_id]
    _ = (AlgHom.id k _).comp π := (AlgHom.id_comp _).symm

theorem innerCoordinate_on_points (M : Subgroup (WithConv (A →ₐ[k] k)))
    (a : WithConv (A →ₐ[k] k)) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    (x : WithConv ((A ⧸ subgroupIdeal M) →ₐ[k] k)) :
    (TauCeti.AlgHom.mapDomain (innerCoordinate M a ha) x).ofConv.comp
      (Ideal.Quotient.mkₐ k (subgroupIdeal M)) =
    (a * toConv (x.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal M))) * a⁻¹).ofConv := by
  rw [TauCeti.AlgHom.mapDomain_apply]
  change (x.ofConv.comp (innerCoordinate M a ha).toAlgHom).comp _ = _
  rw [AlgHom.comp_assoc, innerCoordinate_toAlgHom, ← AlgHom.comp_assoc]
  exact congrArg ofConv (point_comp_innerCo
    (toConv (x.ofConv.comp (Ideal.Quotient.mkₐ k (subgroupIdeal M)))) a)

end CFSG.LieType.AlgebraicGroups
