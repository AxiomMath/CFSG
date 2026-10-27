module

public import CFSG.LieType.AlgebraicGroups.FixedComponentNorm
public import CFSG.GroupTheory.FixedCentralDefect
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Equalizer

public noncomputable section

open CategoryTheory WithConv
namespace CFSG.LieType.AlgebraicGroups

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem fixedCoordinate_points_range
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : M →ₐc[k] M) :
    (TauCeti.AlgHom.mapDomain (A := k)
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σ)).hom.hom).range =
      TauCeti.fixedSubgroup (TauCeti.AlgHom.mapDomain (A := k) σ) := by
  ext x
  change x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup M.obj (fixedHopfIdeal M σ)
    (CommAlgCat.of k k) ↔ TauCeti.AlgHom.mapDomain σ x = x
  have hI : TauCeti.CommHopfAlgCat.equalizerHopfIdeal
      (_root_.CommHopfAlgCat.ofHom σ) (𝟙 M.obj) = fixedHopfIdeal M σ := by
    rw [TauCeti.CommHopfAlgCat.equalizerHopfIdeal_def]
    rfl
  rw [← hI, TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_equalizerHopfIdeal_iff]
  change TauCeti.AlgHom.mapDomain σ x =
      TauCeti.AlgHom.mapDomain (BialgHom.id k M) x ↔ _
  rw [TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]

def fixedCoordinateMap
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X) (f : M.obj ⟶ X.obj)
    (hf : f.hom.comp σM = σX.comp f.hom) :
    fixedCoordinate M σM ⟶ fixedCoordinate X σX := by
  let qX := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom
  let g := qX.comp f.hom
  have hg : g.comp σM = g := by
    dsimp only [g]
    rw [BialgHom.comp_assoc, hf, ← BialgHom.comp_assoc]
    rw [fixedCoordinateHom_comp]
  exact TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient (fixedHopfIdeal M σM)
    (TauCeti.FiniteTypeCommHopfAlgCat.ofHom g)
    (by
      change (TauCeti.HopfIdeal.equalizer σM (BialgHom.id k M)).toIdeal ≤
        RingHom.ker g.toAlgHom.toRingHom
      exact (TauCeti.HopfIdeal.equalizer_le_ker_iff g.toAlgHom.toRingHom).2 fun x =>
        congrArg (fun h : M →ₐc[k] fixedCoordinate X σX => h x) hg)

omit [IsAlgClosed k] in
theorem fixedCoordinateMap_comp
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X) (f : M.obj ⟶ X.obj)
    (hf : f.hom.comp σM = σX.comp f.hom) :
    (fixedCoordinateMap M X σM σX f hf).hom.hom.comp
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σM)).hom.hom =
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom.comp
        f.hom := by
  have h := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient
    (fixedHopfIdeal M σM)
    (TauCeti.FiniteTypeCommHopfAlgCat.ofHom
      ((TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom.comp f.hom))
    (by
      let qX := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom
      let g := qX.comp f.hom
      have hg : g.comp σM = g := by
        dsimp only [g]
        rw [BialgHom.comp_assoc, hf, ← BialgHom.comp_assoc, fixedCoordinateHom_comp]
      change (TauCeti.HopfIdeal.equalizer σM (BialgHom.id k M)).toIdeal ≤
        RingHom.ker g.toAlgHom.toRingHom
      exact (TauCeti.HopfIdeal.equalizer_le_ker_iff g.toAlgHom.toRingHom).2 fun x =>
        congrArg (fun h : M →ₐc[k] fixedCoordinate X σX => h x) hg)
  exact congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom h

theorem componentPointsHom_map_eq_one_of_source_component_eq_one
    (M N : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (f : M.obj ⟶ N.obj)
    (x : TauCeti.HopfAlgebra.points (R := k) (H := N) (CommAlgCat.of k k))
    (hx : TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap N x = 1) :
    TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom M (CommAlgCat.of k k)
      (TauCeti.AlgHom.mapDomain f.hom x) = 1 := by
  have hx0 := (TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff N x).1 hx
  let q := TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient N
    (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := N))
  change x ∈ (TauCeti.AlgHom.mapDomain (A := k) q.hom.hom).range at hx0
  obtain ⟨y, rfl⟩ := hx0
  change TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom M (CommAlgCat.of k k)
    (TauCeti.AlgHom.mapDomain f.hom (TauCeti.AlgHom.mapDomain q.hom.hom y)) = 1
  rw [← MonoidHom.comp_apply (TauCeti.AlgHom.mapDomain f.hom)
    (TauCeti.AlgHom.mapDomain q.hom.hom), ← TauCeti.AlgHom.mapDomain_comp]
  exact componentPointsHom_map_eq_one M (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent N)
    (f ≫ q.hom) (TauCeti.FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent N) y

def pointAutOfCube
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : M →ₐc[k] M)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k M) :
    MulAut (TauCeti.HopfAlgebra.points (R := k) (H := M) (CommAlgCat.of k k)) where
  toFun := TauCeti.AlgHom.mapDomain σ
  invFun := TauCeti.AlgHom.mapDomain (σ.comp σ)
  map_mul' := map_mul _
  left_inv x := by
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← BialgHom.comp_assoc, hσ,
      TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]
  right_inv x := by
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hσ,
      TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]

omit [IsAlgClosed k] in
theorem pointAutOfCube_pow_three
    (M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) (σ : M →ₐc[k] M)
    (hσ : (σ.comp σ).comp σ = BialgHom.id k M) : pointAutOfCube M σ hσ ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  change TauCeti.AlgHom.mapDomain σ (TauCeti.AlgHom.mapDomain σ
    (TauCeti.AlgHom.mapDomain σ x)) = x
  rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
    ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← BialgHom.comp_assoc, hσ,
    TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]

theorem isPGroup_fixed_components_of_central_surjection
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X)
    (hM : (σM.comp σM).comp σM = BialgHom.id k M)
    (hX : (σX.comp σX).comp σX = BialgHom.id k X)
    (f : M.obj ⟶ X.obj) (hf : f.hom.comp σM = σX.comp f.hom)
    (hfs : Function.Surjective (TauCeti.AlgHom.mapDomain (A := k) f.hom))
    (hfc : (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker ≤
      Subgroup.center (TauCeti.HopfAlgebra.points (R := k) (H := X) (CommAlgCat.of k k)))
    (hcompX : ∀ x : TauCeti.HopfAlgebra.points (R := k) (H := fixedCoordinate X σX)
        (CommAlgCat.of k k),
      letI : Group (_root_.ConnectedComponents (PrimeSpectrum (fixedCoordinate X σX))) :=
        TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents (fixedCoordinate X σX)
      TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap (fixedCoordinate X σX) (x ^ 3) = 1) :
    letI := (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints (fixedCoordinate M σM)).str
    IsPGroup 3 (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints (fixedCoordinate M σM)) := by
  let F := fixedCoordinate M σM
  let F' := fixedCoordinate X σX
  let _ := (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints F).str
  let : Finite (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints F) :=
    TauCeti.FiniteTypeCommHopfAlgCat.instFiniteComponentGroupPoints F
  let : Group (_root_.ConnectedComponents (PrimeSpectrum F)) :=
    TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents F
  let e := TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMulEquivConnectedComponents F
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σM)).hom.hom
  let q' := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom
  let α := pointAutOfCube X σX hX
  let β := pointAutOfCube M σM hM
  let φ := TauCeti.AlgHom.mapDomain (A := k) f.hom
  have hφ : φ.comp α.toMonoidHom = β.toMonoidHom.comp φ := by
    change (TauCeti.AlgHom.mapDomain f.hom).comp (TauCeti.AlgHom.mapDomain σX) =
      (TauCeti.AlgHom.mapDomain σM).comp (TauCeti.AlgHom.mapDomain f.hom)
    rw [← TauCeti.AlgHom.mapDomain_comp, ← TauCeti.AlgHom.mapDomain_comp, hf]
  apply (isPGroup_iff_exists_pow_pow_eq_one).2
  refine ⟨2, fun c => ?_⟩
  obtain ⟨x, rfl⟩ := TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMk_surjective F c
  let y := TauCeti.AlgHom.mapDomain q x
  have hy : β y = y := fixedCoordinate_point_fixed M σM x
  obtain ⟨z, hz, hzy⟩ := CFSG.FixedCentralDefect.exists_fixed_lift_cube φ α β hfs
    (pointAutOfCube_pow_three X σX hX) hfc hφ hy
  have hzrange : z ∈ (TauCeti.AlgHom.mapDomain q').range := by
    rw [fixedCoordinate_points_range]
    exact hz
  obtain ⟨z', hz'⟩ := hzrange
  have hfixed : TauCeti.AlgHom.mapDomain (fixedCoordinateMap M X σM σX f hf).hom.hom z' =
      x ^ 3 := by
    apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective M.obj (fixedHopfIdeal M σM)
      (CommAlgCat.of k k)
    change TauCeti.AlgHom.mapDomain q
        (TauCeti.AlgHom.mapDomain (fixedCoordinateMap M X σM σX f hf).hom.hom z') =
      TauCeti.AlgHom.mapDomain q (x ^ 3)
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
      fixedCoordinateMap_comp, TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply,
      hz', hzy, map_pow]
  have hkill : TauCeti.FiniteTypeCommHopfAlgCat.componentPointsHom F (CommAlgCat.of k k)
      (x ^ (3 ^ 2)) = 1 := by
    rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, ← hfixed, ← map_pow]
    exact componentPointsHom_map_eq_one_of_source_component_eq_one F F'
      (fixedCoordinateMap M X σM σX f hf).hom (z' ^ 3) (hcompX z')
  apply e.injective
  rw [map_pow, map_one]
  change TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMulEquivConnectedComponents F
    (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMk F x) ^ (3 ^ 2) = 1
  rw [TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsMulEquivConnectedComponents_apply,
    TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPointsToConnectedComponents_mk,
    ← TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap_apply, ← map_pow]
  exact (componentPointsHom_eq_one_iff F _).1 hkill

theorem isPGroup_fixed_components_of_central_isogeny
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X)
    (hM : (σM.comp σM).comp σM = BialgHom.id k M)
    (hX : (σX.comp σX).comp σX = BialgHom.id k X)
    (f : M.obj ⟶ X.obj) (hf : f.hom.comp σM = σX.comp f.hom)
    (hisog : TauCeti.CommHopfAlgCat.IsCentralIsogeny f)
    (hcompX : ∀ x : TauCeti.HopfAlgebra.points (R := k) (H := fixedCoordinate X σX)
        (CommAlgCat.of k k),
      letI : Group (_root_.ConnectedComponents (PrimeSpectrum (fixedCoordinate X σX))) :=
        TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents (fixedCoordinate X σX)
      TauCeti.FiniteTypeCommHopfAlgCat.rationalComponentMap (fixedCoordinate X σX) (x ^ 3) = 1) :
    letI := (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints (fixedCoordinate M σM)).str
    IsPGroup 3 (TauCeti.FiniteTypeCommHopfAlgCat.componentGroupPoints (fixedCoordinate M σM)) := by
  apply isPGroup_fixed_components_of_central_surjection M X σM σX hM hX f hf
  · exact hisog.isIsogeny.mapPointsFunctor_app_surjective k
  · have hker := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      f (CommAlgCat.of k k)
    change TauCeti.CommHopfAlgCat.quotientPointsSubgroup X.obj
        (TauCeti.CommHopfAlgCat.kernelHopfIdeal f) (CommAlgCat.of k k) =
      (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker at hker
    rw [← hker]
    exact (TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_center X.obj
      (TauCeti.CommHopfAlgCat.kernelHopfIdeal f) hisog.isCentral_kernelHopfIdeal
      (CommAlgCat.of k k)).trans TauCeti.HopfAlgebra.center_le_center
  · exact hcompX

end CFSG.LieType.AlgebraicGroups
