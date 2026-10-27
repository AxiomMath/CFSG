module

public import CFSG.LieType.AlgebraicGroups.EquivariantAffineEmbedding
public import CFSG.LieType.AlgebraicGroups.ChevalleyLine
public import CFSG.LieType.AlgebraicGroups.ConnectedCenterAutomorphism

public noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups

universe u v

section PointConjugation

variable {R : Type u} [CommSemiring R]
variable {H : Type v} [CommSemiring H] [HopfAlgebra R H]

theorem scalar_left_convolution_mem_subcoalgebra (D : TauCeti.Subcoalgebra R H)
    (p : WithConv (H →ₐ[R] R)) (f : WithConv (H →ₐ[R] H))
    (hf : Set.MapsTo f.ofConv D D) {x : H} (hx : x ∈ D) :
    (TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId R H) p * f).ofConv x ∈ D := by
  obtain ⟨z, hz⟩ := D.comul_mem hx
  rw [AlgHom.convMul_apply, ← hz]
  clear hz
  change _ ∈ D.carrier
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using D.carrier.add_mem hz hw
  | tmul a b =>
    simpa only [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Algebra.ofId_apply, Submodule.subtype_apply, ← Algebra.smul_def] using
      D.carrier.smul_mem (p.ofConv (a : H)) (hf b.property)

theorem scalar_right_convolution_mem_subcoalgebra (D : TauCeti.Subcoalgebra R H)
    (p : WithConv (H →ₐ[R] R)) (f : WithConv (H →ₐ[R] H))
    (hf : Set.MapsTo f.ofConv D D) {x : H} (hx : x ∈ D) :
    (f * TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId R H) p).ofConv x ∈ D := by
  obtain ⟨z, hz⟩ := D.comul_mem hx
  rw [AlgHom.convMul_apply, ← hz]
  clear hz
  change _ ∈ D.carrier
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simpa only [map_add] using D.carrier.add_mem hz hw
  | tmul a b =>
    simp only [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      TauCeti.AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      Algebra.ofId_apply, Submodule.subtype_apply]
    rw [mul_comm, ← Algebra.smul_def]
    exact D.carrier.smul_mem (p.ofConv (b : H)) (hf a.property)

theorem pointConjugation_mem_subcoalgebra (D : TauCeti.Subcoalgebra R H)
    (g : WithConv (H →ₐ[R] R)) {x : H} (hx : x ∈ D) :
    TauCeti.HopfAlgebra.pointConjugationAlgHom g x ∈ D := by
  have h := TauCeti.HopfAlgebra.toConv_pointConjugationAlgHom g
  have hx' := scalar_right_convolution_mem_subcoalgebra D g⁻¹
    (TauCeti.AlgHom.mapValue (H := H) (Algebra.ofId R H) g * toConv (AlgHom.id R H))
    (fun z hz => scalar_left_convolution_mem_subcoalgebra D g (toConv (AlgHom.id R H))
      (fun z hz => hz) hz) hx
  rw [map_inv, ← h] at hx'
  exact hx'

theorem map_pointConjugation_subcoalgebra (D : TauCeti.Subcoalgebra R H)
    (g : WithConv (H →ₐ[R] R)) :
    D.map (TauCeti.HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom.toCoalgHom = D := by
  have heq (h : WithConv (H →ₐ[R] R)) (x : H) :
      (TauCeti.HopfAlgebra.pointConjugationBialgEquiv h).toBialgHom x =
        TauCeti.HopfAlgebra.pointConjugationAlgHom h x := by
    have hh := AlgHom.congr_fun (TauCeti.HopfAlgebra.pointConjugationBialgEquiv_toAlgHom h) x
    simpa only [← BialgEquiv.toBialgHom_eq_coe, BialgHom.coe_toAlgHom] using hh
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := TauCeti.Subcoalgebra.mem_map.mp hx
    simpa only [BialgHom.toCoalgHom_apply, heq] using
      pointConjugation_mem_subcoalgebra D g hy
  · intro x hx
    refine TauCeti.Subcoalgebra.mem_map.mpr
      ⟨TauCeti.HopfAlgebra.pointConjugationAlgHom g⁻¹ x,
        pointConjugation_mem_subcoalgebra D g⁻¹ hx, ?_⟩
    have h := AlgHom.congr_fun
      (TauCeti.HopfAlgebra.pointConjugationAlgHom_mul g⁻¹ g) x
    simpa only [BialgHom.toCoalgHom_apply, heq, inv_mul_cancel,
      TauCeti.HopfAlgebra.pointConjugationAlgHom_one,
      AlgHom.id_apply, AlgHom.comp_apply] using h.symm

theorem map_innerTwist_subcoalgebra (σ : H →ₐc[R] H)
    (D : TauCeti.Subcoalgebra R H) (hD : D.map σ.toCoalgHom = D)
    (y : WithConv (H →ₐ[R] R)) :
    D.map (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom).toCoalgHom =
      D := by
  have heq : (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom).toCoalgHom =
      σ.toCoalgHom.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom.toCoalgHom := rfl
  rw [heq, ← TauCeti.Subcoalgebra.map_map, map_pointConjugation_subcoalgebra, hD]

end PointConjugation

section FiniteCoordinates

variable {k : Type u} [Field k]
variable {H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k} {σ : H →ₐc[k] H}

theorem innerTwist_bijective (σ : H →ₐc[k] H) (hσ : Function.Bijective σ)
    (y : WithConv (H →ₐ[k] k)) :
    Function.Bijective (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom) := by
  let τ := σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom
  constructor
  · intro a b hab
    apply (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toAlgEquiv.injective
    apply hσ.1
    simpa only [τ, BialgHom.comp_apply, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, BialgEquiv.coe_toAlgEquiv] using hab
  · intro a
    obtain ⟨b, hb⟩ := hσ.2 a
    obtain ⟨c, hc⟩ := (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toAlgEquiv.surjective b
    have hc' : (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y) c = b := by
      simpa only [BialgEquiv.coe_toAlgEquiv] using hc
    refine ⟨c, ?_⟩
    simpa only [τ, BialgHom.comp_apply, BialgEquiv.toBialgHom_eq_coe,
      BialgEquiv.coe_toBialgHom, hc'] using hb

namespace SemisimpleAffineCoordinatesThree

theorem exists_finite_innerTwist_defining_coordinates [IsAlgClosed k] [IsReduced H]
    (E : SemisimpleAffineCoordinatesThree H σ) (I : TauCeti.HopfIdeal k H)
    (y : WithConv (H →ₐ[k] k)) :
    ∃ D : TauCeti.Subcoalgebra k H,
      Module.Finite k D.toSubmodule ∧ D.map σ.toCoalgHom = D ∧
      D.map (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom).toCoalgHom = D ∧
      E.coalgebra ≤ D ∧ Algebra.adjoin k (D : Set H) = ⊤ ∧
      I.toIdeal ≤ Ideal.span ((D : Set H) ∩ (I : Set H)) := by
  have hI : I.toIdeal.FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hI
  obtain ⟨D, hD, hsD⟩ := TauCeti.Subcoalgebra.exists_finiteDimensional_subcoalgebra_of_setFinite
    (k := k) (C := H) s hs
  let : Module.Finite k D.toSubmodule := hD
  let : Module.Finite k E.coalgebra.toSubmodule := E.finite
  let : Module.Finite k (E.coalgebra ⊔ D).toSubmodule :=
    TauCeti.Subcoalgebra.sup_finite _ _
  let W := cyclicClosureThree σ.toCoalgHom (E.coalgebra ⊔ D)
  have hσ : (σ.toCoalgHom.comp σ.toCoalgHom).comp σ.toCoalgHom = CoalgHom.id k H :=
    congrArg BialgHom.toCoalgHom E.coordinateEnd_cube
  have hW : E.coalgebra ⊔ D ≤ W := le_cyclicClosureThree _ _
  have hEW : E.coalgebra ≤ W := le_sup_left.trans hW
  have hWσ := map_cyclicClosureThree σ.toCoalgHom hσ (E.coalgebra ⊔ D)
  refine ⟨W, finite_cyclicClosureThree _ _, hWσ,
    map_innerTwist_subcoalgebra σ W hWσ y, hEW, ?_, ?_⟩
  · apply top_unique
    rw [← E.generates]
    exact Algebra.adjoin_mono (TauCeti.Subcoalgebra.le_def.mp hEW)
  · rw [← hspan]
    apply Ideal.span_mono
    intro x hx
    have hDW : D ≤ W := le_sup_right.trans hW
    have hxW : x ∈ W := (TauCeti.Subcoalgebra.le_def.mp hDW) (hsD hx)
    have hxI : x ∈ I.toIdeal := hspan ▸ Submodule.subset_span hx
    exact ⟨hxW, hxI⟩

end SemisimpleAffineCoordinatesThree

local instance (D : TauCeti.Subcoalgebra k H) : AddCommGroup D.toRegularSubcomodule :=
  Module.addCommMonoidToAddCommGroup k

theorem coordinateActor_map_definingSubspace (τ : H →ₐc[k] H)
    (hτ : Function.Bijective τ) (I : TauCeti.HopfIdeal k H)
    (hI : I.comapOfSurjective τ hτ.2 = I)
    (D : TauCeti.Subcoalgebra k H) (hD : D.map τ.toCoalgHom = D) :
    (I.definingSubspace D.toRegularSubcomodule).map (coordinateActor τ D hD) =
      I.definingSubspace D.toRegularSubcomodule := by
  have hmem (x : D.toRegularSubcomodule) :
      coordinateActor τ D hD x ∈ I.definingSubspace D.toRegularSubcomodule ↔
        x ∈ I.definingSubspace D.toRegularSubcomodule := by
    simp only [TauCeti.HopfIdeal.mem_definingSubspace, coordinateActor_apply]
    have hp : (x : H) ∈ I.comapOfSurjective τ hτ.2 ↔ (x : H) ∈ I := by rw [hI]
    exact TauCeti.HopfIdeal.mem_comapOfSurjective.symm.trans hp
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact (hmem x).mpr hx
  · intro x hx
    obtain ⟨y, rfl⟩ := (coordinateActor_bijective τ D hD hτ).2 x
    exact Submodule.mem_map.mpr ⟨y, (hmem y).mp hx, rfl⟩

theorem coordinateActorEquivOfBijective_symm_intertwines (τ : H →ₐc[k] H)
    (hτ : Function.Bijective τ)
    (D : TauCeti.Subcoalgebra k H) (hD : D.map τ.toCoalgHom = D)
    (g : WithConv (H →ₐ[k] k)) :
    (coordinateActorEquivOfBijective τ D hD hτ).symm.toLinearMap ∘ₗ
        TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule g =
      TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
          (TauCeti.AlgHom.mapDomain τ g) ∘ₗ
        (coordinateActorEquivOfBijective τ D hD hτ).symm.toLinearMap := by
  let e := coordinateActorEquivOfBijective τ D hD hτ
  apply LinearMap.ext
  intro x
  apply e.injective
  have h := LinearMap.congr_fun (coordinateActor_intertwines τ D hD g) (e.symm x)
  rw [← coordinateActorEquivOfBijective_toLinearMap τ D hD hτ] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
  change e (TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
    (TauCeti.AlgHom.mapDomain τ g) (e.symm x)) =
      TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule g (e (e.symm x)) at h
  rw [e.apply_symm_apply] at h
  change e (e.symm (TauCeti.Comodule.basePointsRepresentation (H := H)
      D.toRegularSubcomodule g x)) =
    e (TauCeti.Comodule.basePointsRepresentation (H := H) D.toRegularSubcomodule
      (TauCeti.AlgHom.mapDomain τ g) (e.symm x))
  exact (e.apply_symm_apply _).trans h.symm

theorem exists_line_coordinates_of_invariant_defining_subcoalgebra
    (τ : H →ₐc[k] H) (hτ : Function.Bijective τ)
    (I : TauCeti.HopfIdeal k H) (hI' : I.comapOfSurjective τ hτ.2 = I)
    (D : TauCeti.Subcoalgebra k H) [Module.Finite k D.toSubmodule]
    (hD : D.map τ.toCoalgHom = D)
    (hgenI : I.toIdeal ≤ Ideal.span ((D : Set H) ∩ (I : Set H))) :
    letI : TauCeti.Comodule k H (ExteriorAlgebra k D.toRegularSubcomodule) :=
      TauCeti.Comodule.exteriorAlgebra k H D.toRegularSubcomodule
    ∃ (v : ExteriorAlgebra k D.toRegularSubcomodule)
      (F : Module.End k (ExteriorAlgebra k D.toRegularSubcomodule)),
      v ≠ 0 ∧ F v ≠ 0 ∧ F v ∈ k ∙ v ∧
      (∀ (g : WithConv (H →ₐ[k] k)) (w : ExteriorAlgebra k D.toRegularSubcomodule),
        F (TauCeti.Comodule.basePointsRepresentation (H := H)
            (ExteriorAlgebra k D.toRegularSubcomodule) g w) =
          TauCeti.Comodule.basePointsRepresentation (H := H)
            (ExteriorAlgebra k D.toRegularSubcomodule) (TauCeti.AlgHom.mapDomain τ g) (F w)) ∧
      (∀ g : WithConv (H →ₐ[k] k),
        g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ↔
          TauCeti.Comodule.basePointsRepresentation (H := H)
            (ExteriorAlgebra k D.toRegularSubcomodule) g v ∈ k ∙ v) := by
  let : Module.Finite k D.toRegularSubcomodule := D.toRegularSubcomodule_finite
  let : TauCeti.Comodule k H (ExteriorAlgebra k D.toRegularSubcomodule) :=
    TauCeti.Comodule.exteriorAlgebra k H D.toRegularSubcomodule
  let e := coordinateActorEquivOfBijective τ D hD hτ
  let R := I.definingSubspace D.toRegularSubcomodule
  have hR : R.map e.toLinearMap = R := by
    rw [coordinateActorEquivOfBijective_toLinearMap]
    exact coordinateActor_map_definingSubspace τ hτ I hI' D hD
  have he : e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have hRF : R.map e.symm.toLinearMap = R := by
    have h := congrArg (Submodule.map e.symm.toLinearMap) hR
    rw [← Submodule.map_comp, he, Submodule.map_id] at h
    exact h.symm
  obtain ⟨v, hv, hline, hpreserve, -⟩ := ClosedCone.exists_exteriorLine_quotientPointsSubgroup
    I D.toRegularSubcomodule hgenI
  let F := (ExteriorAlgebra.map e.symm.toLinearMap).toLinearMap
  refine ⟨v, F, hv, ClosedCone.exteriorAlgebraMap_ne_zero e.symm hv,
    hpreserve e.symm.toLinearMap (fun u hu => ?_), ?_, hline⟩
  · change e.symm u ∈ R
    rw [← hRF]
    exact Submodule.mem_map_of_mem hu
  · intro g w
    exact ClosedCone.exteriorAlgebraMap_basePointsRepresentation_of_lift
      (fun g w => LinearMap.congr_fun
        (coordinateActorEquivOfBijective_symm_intertwines τ hτ D hD g) w) g w

theorem SemisimpleAffineCoordinatesThree.exists_innerTwist_line_coordinates
    [IsAlgClosed k] [IsReduced H] (E : SemisimpleAffineCoordinatesThree H σ)
    (I : TauCeti.HopfIdeal k H) (y : WithConv (H →ₐ[k] k))
    (hI : ∀ a : H,
      (σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom) a ∈ I ↔ a ∈ I) :
    let τ := σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom
    ∃ (D : TauCeti.Subcoalgebra k H) (_hD : D.map τ.toCoalgHom = D),
      Module.Finite k D.toSubmodule ∧ E.coalgebra ≤ D ∧
      Algebra.adjoin k (D : Set H) = ⊤ ∧
      I.toIdeal ≤ Ideal.span ((D : Set H) ∩ (I : Set H)) ∧
      letI : TauCeti.Comodule k H (ExteriorAlgebra k D.toRegularSubcomodule) :=
        TauCeti.Comodule.exteriorAlgebra k H D.toRegularSubcomodule
      ∃ (v : ExteriorAlgebra k D.toRegularSubcomodule)
        (F : Module.End k (ExteriorAlgebra k D.toRegularSubcomodule)),
        v ≠ 0 ∧ F v ≠ 0 ∧ F v ∈ k ∙ v ∧
        (∀ (g : WithConv (H →ₐ[k] k)) (w : ExteriorAlgebra k D.toRegularSubcomodule),
          F (TauCeti.Comodule.basePointsRepresentation (H := H)
              (ExteriorAlgebra k D.toRegularSubcomodule) g w) =
            TauCeti.Comodule.basePointsRepresentation (H := H)
              (ExteriorAlgebra k D.toRegularSubcomodule) (TauCeti.AlgHom.mapDomain τ g) (F w)) ∧
        (∀ g : WithConv (H →ₐ[k] k),
          g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ↔
            TauCeti.Comodule.basePointsRepresentation (H := H)
              (ExteriorAlgebra k D.toRegularSubcomodule) g v ∈ k ∙ v) := by
  classical
  let τ := σ.comp (TauCeti.HopfAlgebra.pointConjugationBialgEquiv y).toBialgHom
  have hσ := CanonicalReductive.aut_bijective H σ E.coordinateEnd_cube
  have hτ : Function.Bijective τ := innerTwist_bijective σ hσ y
  have hI' : I.comapOfSurjective τ hτ.2 = I := by
    apply SetLike.ext
    intro a
    rw [TauCeti.HopfIdeal.mem_comapOfSurjective]
    exact hI a
  obtain ⟨D, hfin, hDσ, hD, hED, hgen, hgenI⟩ :=
    E.exists_finite_innerTwist_defining_coordinates I y
  let : Module.Finite k D.toSubmodule := hfin
  refine ⟨D, hD, hfin, hED, hgen, hgenI, ?_⟩
  exact exists_line_coordinates_of_invariant_defining_subcoalgebra τ hτ I hI' D hD hgenI

end FiniteCoordinates

end CFSG.LieType.AlgebraicGroups
