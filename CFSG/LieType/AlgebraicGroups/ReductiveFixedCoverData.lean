module

public import CFSG.LieType.AlgebraicGroups.ReductiveFixedComponentsThree

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

theorem exists_identityComponent_mkQuotient_lift (F P : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (φ : F ⟶ P) (hP : ConnectedSpace (PrimeSpectrum P)) :
    ∃ ψ : TauCeti.FiniteTypeCommHopfAlgCat.identityComponent F ⟶ P,
      TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient F
          (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := F)) ≫ ψ = φ := by
  let := hP
  refine ⟨TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient _ φ
      (TauCeti.CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected φ.hom), ?_⟩
  exact TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

omit [IsAlgClosed k] in
theorem surjective_toBialgHom_mkQuotient (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (I : TauCeti.HopfIdeal k H) :
    Function.Surjective (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient H I)) := by
  have h := TauCeti.CommHopfAlgCat.mkQuotient_surjective H.obj I
  simpa [TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom,
    TauCeti.FiniteTypeCommHopfAlgCat.forget₂_commHopfAlgCat_map_mkQuotient] using h

omit [IsAlgClosed k] in
theorem injective_mapDomain_of_surjective {H K : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (f : H →ₐc[k] K) (hf : Function.Surjective f) :
    Function.Injective (TauCeti.AlgHom.mapDomain (A := k) f) :=
  TauCeti.CommHopfAlgCat.mapPointsFunctor_app_injective_of_surjective
    (_root_.CommHopfAlgCat.ofHom f) hf (CommAlgCat.of k k)

omit [IsAlgClosed k] in
theorem finite_ker_mapDomain_of_isCentralIsogeny {M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    (f : M.obj ⟶ X.obj) (hf : TauCeti.CommHopfAlgCat.IsCentralIsogeny f) :
    ((TauCeti.AlgHom.mapDomain (A := k) f.hom).ker : Set (WithConv (X →ₐ[k] k))).Finite := by
  let I := TauCeti.CommHopfAlgCat.kernelHopfIdeal f
  have hker := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
    f (CommAlgCat.of k k)
  change TauCeti.CommHopfAlgCat.quotientPointsSubgroup X.obj I (CommAlgCat.of k k) =
    (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker at hker
  rw [← hker]
  have : Module.Finite k (X.obj ⧸ I.toIdeal) :=
    TauCeti.CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hf.isIsogeny.finite
  have hofinj : Function.Injective
      (WithConv.ofConv : WithConv ((X.obj ⧸ I.toIdeal) →ₐ[k] k) → _) := by
    intro a b h
    exact WithConv.ext h
  have : Finite (WithConv ((X.obj ⧸ I.toIdeal) →ₐ[k] k)) :=
    Finite.of_injective WithConv.ofConv hofinj
  let toKer : WithConv ((X.obj ⧸ I.toIdeal) →ₐ[k] k) →
      TauCeti.CommHopfAlgCat.quotientPointsSubgroup X.obj I (CommAlgCat.of k k) :=
    fun q => ⟨TauCeti.CommHopfAlgCat.quotientPointsHom X.obj I (CommAlgCat.of k k) q,
      Set.mem_range_self q⟩
  change (Set.range (TauCeti.CommHopfAlgCat.quotientPointsHom X.obj I
    (CommAlgCat.of k k))).Finite
  exact Set.finite_range _

theorem exists_mapDomain_fixedCoordinateMap_eq_pow_three
    (M X : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k)
    (σM : M →ₐc[k] M) (σX : X →ₐc[k] X)
    (hM : (σM.comp σM).comp σM = BialgHom.id k M)
    (hX : (σX.comp σX).comp σX = BialgHom.id k X)
    (f : M.obj ⟶ X.obj) (hf : f.hom.comp σM = σX.comp f.hom)
    (hisog : TauCeti.CommHopfAlgCat.IsCentralIsogeny f)
    (y : WithConv (fixedCoordinate M σM →ₐ[k] k)) :
    ∃ z : WithConv (fixedCoordinate X σX →ₐ[k] k),
      TauCeti.AlgHom.mapDomain (fixedCoordinateMap M X σM σX f hf).hom.hom z = y ^ 3 := by
  let A := CommAlgCat.of k k
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σM)).hom.hom
  let q' := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX)).hom.hom
  let α : MulAut (TauCeti.HopfAlgebra.points (R := k) (H := X) A) :=
    { toFun := TauCeti.AlgHom.mapDomain σX
      invFun := TauCeti.AlgHom.mapDomain (σX.comp σX)
      map_mul' := map_mul _
      left_inv := fun x => by
        rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← BialgHom.comp_assoc,
          hX, TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]
      right_inv := fun x => by
        rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hX,
          TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply] }
  let β : MulAut (TauCeti.HopfAlgebra.points (R := k) (H := M) A) :=
    { toFun := TauCeti.AlgHom.mapDomain σM
      invFun := TauCeti.AlgHom.mapDomain (σM.comp σM)
      map_mul' := map_mul _
      left_inv := fun x => by
        rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← BialgHom.comp_assoc,
          hM, TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]
      right_inv := fun x => by
        rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, hM,
          TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply] }
  have hα : α ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    change TauCeti.AlgHom.mapDomain σX (TauCeti.AlgHom.mapDomain σX
      (TauCeti.AlgHom.mapDomain σX x)) = x
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← BialgHom.comp_assoc, hX,
      TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]
  have hβ : β ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    change TauCeti.AlgHom.mapDomain σM (TauCeti.AlgHom.mapDomain σM
      (TauCeti.AlgHom.mapDomain σM x)) = x
    rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
      ← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp, ← BialgHom.comp_assoc, hM,
      TauCeti.AlgHom.mapDomain_id, MonoidHom.id_apply]
  let φ := TauCeti.AlgHom.mapDomain (A := k) f.hom
  have hφ : φ.comp α.toMonoidHom = β.toMonoidHom.comp φ := by
    change (TauCeti.AlgHom.mapDomain f.hom).comp (TauCeti.AlgHom.mapDomain σX) =
      (TauCeti.AlgHom.mapDomain σM).comp (TauCeti.AlgHom.mapDomain f.hom)
    rw [← TauCeti.AlgHom.mapDomain_comp, ← TauCeti.AlgHom.mapDomain_comp, hf]
  have hcentral : φ.ker ≤
      Subgroup.center (TauCeti.HopfAlgebra.points (R := k) (H := X) A) := by
    have hk := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      f A
    change TauCeti.CommHopfAlgCat.quotientPointsSubgroup X.obj
        (TauCeti.CommHopfAlgCat.kernelHopfIdeal f) A =
      (TauCeti.AlgHom.mapDomain (A := k) f.hom).ker at hk
    rw [← hk]
    exact (TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_center X.obj
      (TauCeti.CommHopfAlgCat.kernelHopfIdeal f) hisog.isCentral_kernelHopfIdeal
      A).trans TauCeti.HopfAlgebra.center_le_center
  have hsurj : Function.Surjective φ := hisog.isIsogeny.mapPointsFunctor_app_surjective k
  have hy : β (TauCeti.AlgHom.mapDomain q y) = TauCeti.AlgHom.mapDomain q y :=
    fixedCoordinate_point_fixed M σM y
  obtain ⟨z', hz'fix, hz'⟩ := CFSG.FixedCentralDefect.exists_fixed_lift_cube φ α β hsurj
    hα hcentral hφ hy
  have hzrange : z' ∈ (TauCeti.AlgHom.mapDomain q').range := by
    rw [fixedCoordinate_points_range]
    exact hz'fix
  obtain ⟨z, hz⟩ := hzrange
  refine ⟨z, ?_⟩
  apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective M.obj (fixedHopfIdeal M σM) A
  change TauCeti.AlgHom.mapDomain q
      (TauCeti.AlgHom.mapDomain (fixedCoordinateMap M X σM σX f hf).hom.hom z) =
    TauCeti.AlgHom.mapDomain q (y ^ 3)
  rw [← MonoidHom.comp_apply, ← TauCeti.AlgHom.mapDomain_comp,
    fixedCoordinateMap_comp, TauCeti.AlgHom.mapDomain_comp, MonoidHom.comp_apply,
    hz, hz', map_pow]

namespace EquivariantReductiveCoverThree

abbrev fixedSource {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σM : M →ₐc[k] M}
    (D : EquivariantReductiveCoverThree M σM) : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k :=
  TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct
    (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate D.torus D.torusAut))
    (fixedCoordinate D.semisimple.obj D.semisimpleAut)

abbrev torusToFixedIdentity {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σM : M →ₐc[k] M}
    (D : EquivariantReductiveCoverThree M σM) :
    D.torus →ₐc[k] TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
      (fixedCoordinate D.torus D.torusAut) :=
  (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (fixedCoordinate D.torus D.torusAut)
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k)
          (H := fixedCoordinate D.torus D.torusAut)))).comp
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient D.torus (fixedHopfIdeal D.torus D.torusAut)))

abbrev fixedSourceMap {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σM : M →ₐc[k] M}
    (D : EquivariantReductiveCoverThree M σM) :
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus D.semisimple.obj →ₐc[k]
      D.fixedSource :=
  Bialgebra.TensorProduct.map D.torusToFixedIdentity
    (FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut)

theorem torusToFixedIdentity_comp_torusAut {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    {σM : M →ₐc[k] M} (D : EquivariantReductiveCoverThree M σM) :
    D.torusToFixedIdentity.comp D.torusAut = D.torusToFixedIdentity := by
  rw [BialgHom.comp_assoc]
  exact congrArg _ (fixedCoordinateHom_comp D.torus D.torusAut)

theorem fixedSourceMap_comp_productAut {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    {σM : M →ₐc[k] M} (D : EquivariantReductiveCoverThree M σM) :
    D.fixedSourceMap.comp (Bialgebra.TensorProduct.map D.torusAut D.semisimpleAut) =
      D.fixedSourceMap := by
  apply BialgHom.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
      have ht : D.torusToFixedIdentity (D.torusAut a) = D.torusToFixedIdentity a :=
        congrArg (fun f => f a) D.torusToFixedIdentity_comp_torusAut
      have hs : FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut
          (D.semisimpleAut b) =
          FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut b :=
        congrArg (fun f : D.semisimple.obj →ₐc[k]
          fixedCoordinate D.semisimple.obj D.semisimpleAut => f b)
          (fixedCoordinateHom_comp D.semisimple.obj D.semisimpleAut)
      simp only [BialgHom.comp_apply, Bialgebra.TensorProduct.map_tmul, ht, hs]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def fixedSourceFixedMap {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    {σM : M →ₐc[k] M} (D : EquivariantReductiveCoverThree M σM) :
    fixedCoordinate (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus D.semisimple.obj)
        (Bialgebra.TensorProduct.map D.torusAut D.semisimpleAut) ⟶ D.fixedSource := by
  let : Algebra.FiniteType k (D.torus ⊗[k] D.semisimple.obj) :=
    FixedProduct.tensorProductFiniteType D.torus D.semisimple.obj
  let : Algebra.FiniteType k (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
      (fixedCoordinate D.torus D.torusAut) ⊗[k] fixedCoordinate D.semisimple.obj D.semisimpleAut) :=
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) _ _
  exact TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient
    (fixedHopfIdeal (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus D.semisimple.obj)
      (Bialgebra.TensorProduct.map D.torusAut D.semisimpleAut))
    (TauCeti.FiniteTypeCommHopfAlgCat.ofHom D.fixedSourceMap)
    (by
      change (TauCeti.HopfIdeal.equalizer (Bialgebra.TensorProduct.map D.torusAut D.semisimpleAut)
          (BialgHom.id k _)).toIdeal ≤ RingHom.ker D.fixedSourceMap.toAlgHom.toRingHom
      exact (TauCeti.HopfIdeal.equalizer_le_ker_iff D.fixedSourceMap.toAlgHom.toRingHom).2
        fun x => congrArg (fun f => f x) D.fixedSourceMap_comp_productAut)

theorem fixedSourceFixedMap_comp_mkQuotient {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k}
    {σM : M →ₐc[k] M} (D : EquivariantReductiveCoverThree M σM) :
    (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap).comp
        (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient
            (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus D.semisimple.obj)
            (fixedHopfIdeal (TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus
              D.semisimple.obj) (Bialgebra.TensorProduct.map D.torusAut D.semisimpleAut)))) =
      D.fixedSourceMap := by
  let : Algebra.FiniteType k (D.torus ⊗[k] D.semisimple.obj) :=
    FixedProduct.tensorProductFiniteType D.torus D.semisimple.obj
  let : Algebra.FiniteType k (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
      (fixedCoordinate D.torus D.torusAut) ⊗[k] fixedCoordinate D.semisimple.obj D.semisimpleAut) :=
    TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) _ _
  exact congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _)

theorem exists_normFactor {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σM : M →ₐc[k] M}
    (D : EquivariantReductiveCoverThree M σM) [Coalgebra.IsCocomm k D.torus.obj] :
    ∃ ν : TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
        (fixedCoordinate D.torus D.torusAut) →ₐc[k] D.torus,
      ν.comp D.torusToFixedIdentity = normThreeBialgHom D.torus D.torusAut := by
  let ν₀ : fixedCoordinate D.torus D.torusAut ⟶ D.torus :=
    TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient (fixedHopfIdeal D.torus D.torusAut)
      (TauCeti.FiniteTypeCommHopfAlgCat.ofHom (normThreeBialgHom D.torus D.torusAut))
      (by
        change (TauCeti.HopfIdeal.equalizer D.torusAut (BialgHom.id k D.torus)).toIdeal ≤
          RingHom.ker (normThreeBialgHom D.torus D.torusAut).toAlgHom.toRingHom
        exact (TauCeti.HopfIdeal.equalizer_le_ker_iff
          (normThreeBialgHom D.torus D.torusAut).toAlgHom.toRingHom).2
          fun x => congrArg (fun f => f x)
            (normThreeBialgHom_comp D.torus D.torusAut D.torusAut_cube))
  have hν₀ : (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ν₀).comp
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient D.torus (fixedHopfIdeal D.torus D.torusAut))) =
      normThreeBialgHom D.torus D.torusAut :=
    congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _)
  have hT : ConnectedSpace (PrimeSpectrum D.torus) :=
    (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).1
      (TauCeti.torusCommHopfAlgProperty.geometricallyConnected k D.torus D.isTorus)
  obtain ⟨ν, hν⟩ := exists_identityComponent_mkQuotient_lift
    (fixedCoordinate D.torus D.torusAut) D.torus ν₀ hT
  refine ⟨TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ν, ?_⟩
  rw [← hν₀, ← hν]
  rfl

theorem exists_identityComponent_coordinate
    {M : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σM : M →ₐc[k] M}
    (D : EquivariantReductiveCoverThree M σM)
    (hM : (σM.comp σM).comp σM = BialgHom.id k M)
    (hS : ConnectedSpace (PrimeSpectrum (fixedCoordinate D.semisimple.obj D.semisimpleAut))) :
    ∃ ψ : TauCeti.FiniteTypeCommHopfAlgCat.identityComponent (fixedCoordinate M σM) ⟶
        D.fixedSource,
      ((TauCeti.AlgHom.mapDomain (A := k) (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ)).ker :
          Set (WithConv (D.fixedSource →ₐ[k] k))).Finite ∧
      (∀ z : WithConv (D.fixedSource →ₐ[k] k),
        TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ) z = 1 →
        ∀ y : WithConv (D.fixedSource →ₐ[k] k), z * y = y * z) ∧
      (∀ n : WithConv (TauCeti.FiniteTypeCommHopfAlgCat.identityComponent
          (fixedCoordinate M σM) →ₐ[k] k), ∃ x : WithConv (D.fixedSource →ₐ[k] k),
        TauCeti.AlgHom.mapDomain (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ) x = n ^ 9) := by
  classical
  let X := TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus D.semisimple.obj
  let σX := Bialgebra.TensorProduct.map D.torusAut D.semisimpleAut
  let FM := fixedCoordinate M σM
  let qM : M →ₐc[k] FM := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σM))
  let qX : X →ₐc[k] fixedCoordinate X σX := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
    (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient X (fixedHopfIdeal X σX))
  let rM : FM →ₐc[k] TauCeti.FiniteTypeCommHopfAlgCat.identityComponent FM :=
    TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
      (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient FM
        (TauCeti.HopfAlgebra.identityComponentHopfIdeal (k := k) (H := FM)))
  let φ1 := fixedCoordinateMap M X σM σX D.cover D.equivariant
  let φ := φ1 ≫ D.fixedSourceFixedMap
  have hSrc : ConnectedSpace (PrimeSpectrum D.fixedSource) := by
    apply (TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k
      D.fixedSource.obj).1
    exact TauCeti.geometricallyConnectedCommHopfAlgProperty.tensorProduct _ _
      ((TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2
        (TauCeti.FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent _))
      ((TauCeti.geometricallyConnectedCommHopfAlgProperty_iff_connectedSpace k _).2 hS)
  obtain ⟨ψ, hψ⟩ := exists_identityComponent_mkQuotient_lift FM D.fixedSource φ hSrc
  let ψ' := TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom ψ
  have hψ' : ψ'.comp rM =
      (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap).comp φ1.hom.hom :=
    congrArg TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom hψ
  have hkey : (ψ'.comp rM).comp qM = D.fixedSourceMap.comp D.cover.hom := by
    rw [hψ', BialgHom.comp_assoc]
    change (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap).comp
        ((fixedCoordinateMap M X σM σX D.cover D.equivariant).hom.hom.comp
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient M (fixedHopfIdeal M σM)).hom.hom) = _
    rw [fixedCoordinateMap_comp, ← BialgHom.comp_assoc]
    exact congrArg (fun f => f.comp D.cover.hom) D.fixedSourceFixedMap_comp_mkQuotient
  have hpts : ∀ x : WithConv (D.fixedSource →ₐ[k] k),
      TauCeti.AlgHom.mapDomain qM (TauCeti.AlgHom.mapDomain rM (TauCeti.AlgHom.mapDomain ψ' x)) =
        TauCeti.AlgHom.mapDomain D.cover.hom (TauCeti.AlgHom.mapDomain D.fixedSourceMap x) := by
    intro x
    change TauCeti.AlgHom.mapDomain ((ψ'.comp rM).comp qM) x =
      TauCeti.AlgHom.mapDomain (D.fixedSourceMap.comp D.cover.hom) x
    rw [hkey]
  have hrM : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) rM) :=
    injective_mapDomain_of_surjective rM (surjective_toBialgHom_mkQuotient _ _)
  have hqM : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) qM) :=
    injective_mapDomain_of_surjective qM (surjective_toBialgHom_mkQuotient _ _)
  have hsurjSrc : Function.Surjective D.fixedSourceMap := by
    have ht : Function.Surjective D.torusToFixedIdentity :=
      (surjective_toBialgHom_mkQuotient _ _).comp (surjective_toBialgHom_mkQuotient _ _)
    have hs : Function.Surjective
        (FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut) :=
      surjective_toBialgHom_mkQuotient _ _
    exact TensorProduct.map_surjective
      (show Function.Surjective D.torusToFixedIdentity.toLinearMap from ht)
      (show Function.Surjective
        (FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut).toLinearMap from hs)
  have hSrcInj : Function.Injective (TauCeti.AlgHom.mapDomain (A := k) D.fixedSourceMap) :=
    injective_mapDomain_of_surjective D.fixedSourceMap hsurjSrc
  have hKfin := finite_ker_mapDomain_of_isCentralIsogeny D.cover D.isCentralIsogeny
  have hKcen : (TauCeti.AlgHom.mapDomain (A := k) D.cover.hom).ker ≤
      Subgroup.center (TauCeti.HopfAlgebra.points (R := k) (H := X.obj) (CommAlgCat.of k k)) := by
    have hker := TauCeti.CommHopfAlgCat.quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor
      D.cover (CommAlgCat.of k k)
    change TauCeti.CommHopfAlgCat.quotientPointsSubgroup X.obj
        (TauCeti.CommHopfAlgCat.kernelHopfIdeal D.cover) (CommAlgCat.of k k) =
      (TauCeti.AlgHom.mapDomain (A := k) D.cover.hom).ker at hker
    rw [← hker]
    exact (TauCeti.CommHopfAlgCat.quotientPointsSubgroup_le_center X.obj
      (TauCeti.CommHopfAlgCat.kernelHopfIdeal D.cover) D.isCentralIsogeny.isCentral_kernelHopfIdeal
      (CommAlgCat.of k k)).trans TauCeti.HopfAlgebra.center_le_center
  have hkerC : ∀ x : WithConv (D.fixedSource →ₐ[k] k), TauCeti.AlgHom.mapDomain ψ' x = 1 →
      TauCeti.AlgHom.mapDomain D.cover.hom (TauCeti.AlgHom.mapDomain D.fixedSourceMap x) = 1 := by
    intro x hx
    rw [← hpts, hx, map_one, map_one]
  refine ⟨ψ, ?_, ?_, ?_⟩
  · refine (hKfin.preimage hSrcInj.injOn).subset ?_
    intro x hx
    exact hkerC x hx
  · intro z hz y
    apply hSrcInj
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hKcen (hkerC z hz)) _ |>.symm
  · intro n
    let _ : Coalgebra.IsCocomm k D.torus.obj :=
      TauCeti.torusCommHopfAlgProperty.isCocomm k D.torus D.isTorus
    let y := TauCeti.AlgHom.mapDomain rM n
    obtain ⟨z, hz⟩ := exists_mapDomain_fixedCoordinateMap_eq_pow_three M X σM σX hM
      D.productAut_cube D.cover D.equivariant D.isCentralIsogeny y
    obtain ⟨w, hw⟩ := FixedProduct.exists_mapDomain_productFixedCoordinateMap_eq_pow_three
      D.torus D.semisimple.obj D.torusAut D.semisimpleAut D.torusAut_cube D.semisimpleAut_cube z
    obtain ⟨ν, hν⟩ := D.exists_normFactor
    let N2 : D.fixedSource →ₐc[k] TauCeti.FiniteTypeCommHopfAlgCat.tensorProduct D.torus
        (fixedCoordinate D.semisimple.obj D.semisimpleAut) :=
      Bialgebra.TensorProduct.map ν (BialgHom.id k _)
    have hN2src : N2.comp D.fixedSourceMap =
        FixedProduct.productTensorMap D.torus D.semisimple.obj D.torusAut D.semisimpleAut := by
      apply BialgHom.ext
      intro a
      induction a using TensorProduct.inductionOn with
      | tmul a b =>
          have ha : ν (D.torusToFixedIdentity a) = normThreeBialgHom D.torus D.torusAut a :=
            congrArg (fun f => f a) hν
          change ν (D.torusToFixedIdentity a) ⊗ₜ[k]
              BialgHom.id k _ (FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut b) =
            normThreeBialgHom D.torus D.torusAut a ⊗ₜ[k]
              FixedProduct.fixedQuotientMapS D.semisimple.obj D.semisimpleAut b
          rw [ha, BialgHom.id_apply]
      | add a b ha hb => simp only [map_add, ha, hb]
    have hN2 : N2.comp (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap) =
        TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (FixedProduct.productFixedCoordinateMap D.torus D.semisimple.obj D.torusAut
            D.semisimpleAut D.torusAut_cube D.semisimpleAut_cube) := by
      apply BialgHom.ext
      intro b
      obtain ⟨a, rfl⟩ := surjective_toBialgHom_mkQuotient X (fixedHopfIdeal X σX) b
      have h1 := congrArg (fun f => f a) (congrArg N2.comp D.fixedSourceFixedMap_comp_mkQuotient)
      have h2 := congrArg (fun f => TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom f a)
        (FixedProduct.productFixedCoordinateMap_comp_mkQuotient D.torus D.semisimple.obj
          D.torusAut D.semisimpleAut D.torusAut_cube D.semisimpleAut_cube)
      simp only [BialgHom.comp_apply] at h1
      change N2 (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap (qX a)) =
        TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom
          (FixedProduct.productFixedCoordinateMap D.torus D.semisimple.obj D.torusAut
            D.semisimpleAut D.torusAut_cube D.semisimpleAut_cube) (qX a)
      rw [show N2 (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap (qX a)) =
          N2 (D.fixedSourceMap a) from h1]
      rw [show N2 (D.fixedSourceMap a) =
          FixedProduct.productTensorMap D.torus D.semisimple.obj D.torusAut D.semisimpleAut a from
        congrArg (fun f => f a) hN2src]
      exact h2.symm
    refine ⟨TauCeti.AlgHom.mapDomain N2 w, hrM ?_⟩
    change TauCeti.AlgHom.mapDomain (ψ'.comp rM) (TauCeti.AlgHom.mapDomain N2 w) =
      TauCeti.AlgHom.mapDomain rM (n ^ 9)
    rw [hψ', map_pow]
    change TauCeti.AlgHom.mapDomain φ1.hom.hom
        (TauCeti.AlgHom.mapDomain
          (N2.comp (TauCeti.FiniteTypeCommHopfAlgCat.toBialgHom D.fixedSourceFixedMap)) w) = y ^ 9
    rw [hN2, hw, map_pow, hz, ← pow_mul]

end EquivariantReductiveCoverThree

end CFSG.LieType.AlgebraicGroups
