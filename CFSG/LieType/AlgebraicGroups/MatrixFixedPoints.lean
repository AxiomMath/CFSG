module
public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupInnerCoordinate
public import CFSG.LieType.AlgebraicGroups.ReductiveFixedComponentsThree
public import CFSG.LieType.AlgebraicGroups.MatrixComponentQuotient
public import CFSG.LieType.AlgebraicGroups.CentralizerComponentInduction
public import TauCeti.RingTheory.Flat.TensorProduct

public noncomputable section
open WithConv
open scoped CFSG.ConvolutionPoints
namespace CFSG.LieType.AlgebraicGroups
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
variable {τ : Tag} {k : Type} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
theorem matrixInnerCoordinate_mem (M : Subgroup (ModGL τ k)) (a : ModGL τ k)
    (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    ∀ y ∈ M.map (modGLPoint τ k).toMonoidHom,
      modGLPoint τ k a * y * (modGLPoint τ k a)⁻¹ ∈ M.map (modGLPoint τ k).toMonoidHom := by
  rintro _ ⟨y, hy, rfl⟩
  change (modGLPoint τ k) a * (modGLPoint τ k) y * ((modGLPoint τ k) a)⁻¹ ∈ _
  rw [← map_inv, ← map_mul, ← map_mul]
  exact Subgroup.mem_map_of_mem _ (ha y hy)

@[expose] def matrixInnerCoordinate (M : Subgroup (ModGL τ k)) (a : ModGL τ k)
    (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    MatrixComponents.coordinateHopf M →ₐc[k] MatrixComponents.coordinateHopf M :=
  innerCoordinate (M.map (modGLPoint τ k).toMonoidHom) (modGLPoint τ k a)
    (matrixInnerCoordinate_mem M a ha)

theorem matrixInnerCoordinate_cube (M : Subgroup (ModGL τ k)) (a : ModGL τ k)
    (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) (ha3 : a ^ 3 = 1) :
    ((matrixInnerCoordinate M a ha).comp (matrixInnerCoordinate M a ha)).comp
      (matrixInnerCoordinate M a ha) = BialgHom.id k (MatrixComponents.coordinateHopf M) := by
  apply innerCoordinate_cube
  rw [← map_pow, ha3, map_one]

@[expose] def matrixFixedPointsHom (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))
      (CommAlgCat.of k k) →* ↥(M ⊓ Subgroup.centralizer {a}) := by
  let σ := matrixInnerCoordinate M a ha
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (MatrixComponents.coordinateHopf M)
    (fixedHopfIdeal (MatrixComponents.coordinateHopf M) σ)).hom.hom
  let e := MatrixComponents.coordinatePointsMulEquiv M hM
  refine ((M.subtype.comp e.toMonoidHom).comp
    (TauCeti.AlgHom.mapDomain (A := k) q)).codRestrict
      (M ⊓ Subgroup.centralizer {a}) ?_
  intro x
  have hx := fixedCoordinate_point_fixed (MatrixComponents.coordinateHopf M) σ x
  have heval := innerCoordinate_on_points (M.map (modGLPoint τ k).toMonoidHom)
    (modGLPoint τ k a) (matrixInnerCoordinate_mem M a ha) (TauCeti.AlgHom.mapDomain q x)
  have hpoint : modGLPoint τ k (e (TauCeti.AlgHom.mapDomain q x) : ModGL τ k) =
      toConv ((TauCeti.AlgHom.mapDomain q x).ofConv.comp
        (Ideal.Quotient.mkₐ k (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))) := by
    have he := coe_mapQuotientPointsEquiv (modGLPoint τ k) M
      (MatrixComponents.pointsZero_subgroupIdeal_map_modGLPoint M hM)
      (TauCeti.AlgHom.mapDomain q x)
    have he' : (e (TauCeti.AlgHom.mapDomain q x) : ModGL τ k) =
        (modGLPoint τ k).symm (toConv ((TauCeti.AlgHom.mapDomain q x).ofConv.comp
          (Ideal.Quotient.mkₐ k (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom))))) := by
      dsimp [e, MatrixComponents.coordinatePointsMulEquiv]
      exact he
    rw [he', MulEquiv.apply_symm_apply]
  refine ⟨(e (TauCeti.AlgHom.mapDomain q x)).property, ?_⟩
  change (e (TauCeti.AlgHom.mapDomain q x) : ModGL τ k) ∈ Subgroup.centralizer {a}
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply (modGLPoint τ k).injective
  rw [map_mul, map_mul, hpoint]
  have h := congrArg (fun p => toConv (p.comp
      (Ideal.Quotient.mkₐ k (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))))
    (congrArg ofConv hx)
  change toConv ((TauCeti.AlgHom.mapDomain
      (innerCoordinate (M.map (modGLPoint τ k).toMonoidHom) (modGLPoint τ k a)
        (matrixInnerCoordinate_mem M a ha)) (TauCeti.AlgHom.mapDomain q x)).ofConv.comp
      (Ideal.Quotient.mkₐ k (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))) = _ at h
  rw [heval, toConv_ofConv] at h
  have h' := congrArg (fun g => g * modGLPoint τ k a) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h'.symm

theorem matrixFixedPointsHom_apply (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M)
    (x : TauCeti.HopfAlgebra.points (R := k)
      (H := fixedCoordinate (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))
      (CommAlgCat.of k k)) :
    (matrixFixedPointsHom M hM a ha x : ModGL τ k) =
      MatrixComponents.coordinatePointsMulEquiv M hM
        (TauCeti.AlgHom.mapDomain
          (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (MatrixComponents.coordinateHopf M)
            (fixedHopfIdeal (MatrixComponents.coordinateHopf M) (matrixInnerCoordinate M a ha))).hom.hom x) := rfl

theorem matrixFixedPointsHom_bijective (M : Subgroup (ModGL τ k))
    (hM : IsPointClosed k (transportPoints (modGLPoint τ k) (M : Set (ModGL τ k))))
    (a : ModGL τ k) (ha : ∀ y ∈ M, a * y * a⁻¹ ∈ M) :
    Function.Bijective (matrixFixedPointsHom M hM a ha) := by
  let σ := matrixInnerCoordinate M a ha
  let q := (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (MatrixComponents.coordinateHopf M)
    (fixedHopfIdeal (MatrixComponents.coordinateHopf M) σ)).hom.hom
  let e := MatrixComponents.coordinatePointsMulEquiv M hM
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply TauCeti.CommHopfAlgCat.quotientPointsHom_injective
      (MatrixComponents.coordinateHopf M).obj (fixedHopfIdeal (MatrixComponents.coordinateHopf M) σ)
      (CommAlgCat.of k k)
    change TauCeti.AlgHom.mapDomain q x = TauCeti.AlgHom.mapDomain q y
    apply e.injective
    apply Subtype.ext
    have h := congrArg Subtype.val hxy
    rw [matrixFixedPointsHom_apply M hM a ha x,
      matrixFixedPointsHom_apply M hM a ha y] at h
    exact h
  · intro g
    let gM : M := ⟨g, g.property.1⟩
    let x := e.symm gM
    have hxrange : x ∈ (TauCeti.AlgHom.mapDomain q).range := by
      change x ∈ (TauCeti.AlgHom.mapDomain
        (TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient (MatrixComponents.coordinateHopf M)
          (fixedHopfIdeal (MatrixComponents.coordinateHopf M) σ)).hom.hom).range
      change x ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup
        (MatrixComponents.coordinateHopf M).obj
        (fixedHopfIdeal (MatrixComponents.coordinateHopf M) σ) (CommAlgCat.of k k)
      apply (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ x).2
      intro h hh
      have hfix : TauCeti.AlgHom.mapDomain σ x = x := by
        have hxe : e x = gM := e.apply_symm_apply gM
        apply e.injective
        apply Subtype.ext
        have heval := innerCoordinate_on_points (M.map (modGLPoint τ k).toMonoidHom)
          (modGLPoint τ k a) (matrixInnerCoordinate_mem M a ha) x
        have hxpoint : modGLPoint τ k (e x : ModGL τ k) =
            toConv (x.ofConv.comp (Ideal.Quotient.mkₐ k
              (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))) := by
          rw [MatrixComponents.coordinatePointsMulEquiv_coe,
            MulEquiv.apply_symm_apply]
        have hyPoint : modGLPoint τ k (e (TauCeti.AlgHom.mapDomain σ x) : ModGL τ k) =
            toConv ((TauCeti.AlgHom.mapDomain σ x).ofConv.comp
              (Ideal.Quotient.mkₐ k (subgroupIdeal (M.map (modGLPoint τ k).toMonoidHom)))) := by
          rw [MatrixComponents.coordinatePointsMulEquiv_coe,
            MulEquiv.apply_symm_apply]
        apply (modGLPoint τ k).injective
        rw [hyPoint]
        change toConv ((TauCeti.AlgHom.mapDomain (innerCoordinate
          (M.map (modGLPoint τ k).toMonoidHom) (modGLPoint τ k a)
          (matrixInnerCoordinate_mem M a ha)) x).ofConv.comp _) = _
        rw [heval, toConv_ofConv, ← hxpoint, hxe]
        have hag : a * (g : ModGL τ k) * a⁻¹ = g := by
          have hc := Subgroup.mem_centralizer_singleton_iff.mp g.property.2
          rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
        rw [← map_inv, ← map_mul, ← map_mul, hag]
      have hkill : (fixedHopfIdeal (MatrixComponents.coordinateHopf M) σ).toIdeal ≤
          RingHom.ker x.ofConv.toRingHom := by
        change (TauCeti.HopfIdeal.equalizer σ (BialgHom.id k _)).toIdeal ≤ _
        apply (TauCeti.HopfIdeal.equalizer_le_ker_iff _).2
        intro a
        exact congrArg (fun f => f.ofConv a) hfix
      exact hkill (TauCeti.HopfIdeal.mem_toIdeal.mpr hh)
    obtain ⟨y, hy⟩ := hxrange
    refine ⟨y, ?_⟩
    apply Subtype.ext
    rw [matrixFixedPointsHom_apply]
    change (e (TauCeti.AlgHom.mapDomain q y) : ModGL τ k) = g
    rw [hy]
    exact congrArg Subtype.val (e.apply_symm_apply gM)

end CFSG.LieType.AlgebraicGroups
