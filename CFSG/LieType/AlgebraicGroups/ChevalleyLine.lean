module

public import CFSG.LieType.AlgebraicGroups.ComoduleLift
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Subspace
public import CFSG.Mathlib.LinearAlgebra.ExteriorLieStabilizer
public import CFSG.LieType.AlgebraicGroups.ChevalleyTangent
public import CFSG.ThirdParty.TauCeti.ExteriorDifferential

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {M : Type u} [AddCommGroup M] [Module k M]

section Linear

theorem exists_basis_span_image_eq [FiniteDimensional k M] (U : Submodule k M) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k M) (s : Finset (Fin n)),
      Submodule.span k (b '' (s : Set (Fin n))) = U := by
  classical
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  let bU := Module.finBasis k U
  let b₀ := (bU.prod (Module.finBasis k U')).map (Submodule.prodEquivOfIsCompl U U' hU')
  refine ⟨_, b₀.reindex finSumFinEquiv, Finset.univ.image (Fin.castAdd _), ?_⟩
  have h1 := congrArg (Submodule.map U.subtype) bU.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h1
  convert h1 using 2
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, ← Set.range_comp,
    Function.comp_def, Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_fst,
    Module.Basis.prod_apply_inl_snd, ZeroMemClass.coe_zero, add_zero, Submodule.coe_subtype, b₀]

theorem exteriorAlgebraMap_ne_zero (f : M ≃ₗ[k] M) {x : ExteriorAlgebra k M} (hx : x ≠ 0) :
    ExteriorAlgebra.map f.toLinearMap x ≠ 0 := by
  have h : (ExteriorAlgebra.map f.symm.toLinearMap).comp
      (ExteriorAlgebra.map f.toLinearMap) = AlgHom.id k (ExteriorAlgebra k M) := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp
  intro h0
  apply hx
  rw [← AlgHom.id_apply (R := k) x, ← h, AlgHom.comp_apply, h0, map_zero]

theorem exists_exteriorLine [FiniteDimensional k M] (U : Submodule k M) :
    ∃ ω : ExteriorAlgebra k M, ω ≠ 0 ∧
      (∀ f : M ≃ₗ[k] M, ExteriorAlgebra.map f.toLinearMap ω ∈ k ∙ ω →
        U.map f.toLinearMap = U) ∧
      (∀ f : M →ₗ[k] M, (∀ u ∈ U, f u ∈ U) → ExteriorAlgebra.map f ω ∈ k ∙ ω) ∧
      (∃ (d : ℕ) (w : ⋀[k]^d M), (w : ExteriorAlgebra k M) = ω ∧
        ∀ f : Module.End k M, exteriorPower.lieMap d f w ∈ k ∙ w ↔ U.map f ≤ U) ∧
      ∀ (f : M →ₗ[k] M) (D : ExteriorAlgebra k M →ₗ[k] ExteriorAlgebra k M),
        (∀ m, D (ExteriorAlgebra.ι k m) = ExteriorAlgebra.ι k (f m)) →
        (∀ x y, D (x * y) = D x * y + x * D y) → (D ω ∈ k ∙ ω ↔ U.map f ≤ U) := by
  obtain ⟨n, b, s, hs⟩ := exists_basis_span_image_eq U
  obtain ⟨w, hw, -, hlie⟩ := CFSG.LinearAlgebra.exists_coe_eq_basis_exteriorAlgebra b s
  refine ⟨b.ExteriorAlgebra s, b.ExteriorAlgebra.ne_zero s, fun f hf => ?_, fun f hf => ?_,
    ⟨s.card, w, hw, fun f => by rw [← hs]; exact hlie f⟩, fun f D hι hmul => by
      rw [← hs]
      exact CFSG.LinearAlgebra.leibniz_basis_exteriorAlgebra_mem_span_singleton_iff b s f D hι hmul⟩
  · have hne := exteriorAlgebraMap_ne_zero f (b.ExteriorAlgebra.ne_zero s)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hne (by rw [← hc, zero_smul])
    rw [← hs]
    refine (b.map_span_exteriorAlgebra_eq_iff s f).mp ?_
    rw [Submodule.map_span, Set.image_singleton, AlgHom.toLinearMap_apply, ← hc,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0)]
  · have h := b.map_span_exteriorAlgebra_le s f (by
      rw [hs, Submodule.map_le_iff_le_comap]
      exact fun u hu => hf u hu)
    exact h (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _))

end Linear

section Points

attribute [local instance] TauCeti.Comodule.exteriorAlgebra

variable {H : Type u} [CommRing H] [HopfAlgebra k H] [TauCeti.Comodule k H M]

theorem basePointsRepresentation_exteriorAlgebra_eq_map (x : WithConv (H →ₐ[k] k))
    (w : ExteriorAlgebra k M) :
    basePointsRepresentation (H := H) (ExteriorAlgebra k M) x w =
      ExteriorAlgebra.map (basePointsRepresentation (H := H) M x) w := by
  have h : basePointsExteriorAlgHom (H := H) x =
      ExteriorAlgebra.map (basePointsRepresentation (H := H) M x) := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      basePointsExteriorAlgHom_apply, basePointsRepresentation_exteriorAlgebra_ι,
      ExteriorAlgebra.map_apply_ι]
  rw [← basePointsExteriorAlgHom_apply, h]

theorem exists_exteriorLine_basePointsRepresentation [FiniteDimensional k M]
    (U : Submodule k M) :
    ∃ ω : ExteriorAlgebra k M, ω ≠ 0 ∧
      (∀ g : WithConv (H →ₐ[k] k),
        basePointsRepresentation (H := H) (ExteriorAlgebra k M) g ω ∈ k ∙ ω ↔
          ∀ u ∈ U, basePointsRepresentation (H := H) M g u ∈ U) ∧
      (∀ f : M →ₗ[k] M, (∀ u ∈ U, f u ∈ U) → ExteriorAlgebra.map f ω ∈ k ∙ ω) ∧
      ∀ d : Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k),
        differential (R := k) (H := H) (M := ExteriorAlgebra k M) d ω ∈ k ∙ ω ↔
          ∀ u ∈ U, differential (R := k) (H := H) (M := M) d u ∈ U := by
  obtain ⟨ω, hω, hequiv, hmap, -, hdiff⟩ := exists_exteriorLine U
  refine ⟨ω, hω, ?_, hmap, ?_⟩
  · intro g
    let e : M ≃ₗ[k] M := LinearEquiv.ofLinear (basePointsRepresentation (H := H) M g)
      (basePointsRepresentation (H := H) M g⁻¹)
      (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
      (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])
    rw [basePointsRepresentation_exteriorAlgebra_eq_map]
    refine ⟨fun h u hu => ?_, hmap _⟩
    have hU : U.map e.toLinearMap = U := hequiv e h
    rw [← hU]
    exact Submodule.mem_map_of_mem hu
  · intro d
    rw [hdiff _ _
      (CFSG.ThirdParty.TauCeti.Comodule.differential_exteriorAlgebra_ι d)
      (CFSG.ThirdParty.TauCeti.Comodule.differential_exteriorAlgebra_mul d),
      Submodule.map_le_iff_le_comap]
    rfl

theorem mapsTo_endOfPoint_baseChange_iff (U : Submodule k M) (g : WithConv (H →ₐ[k] k)) :
    Set.MapsTo (endOfPoint M g.ofConv) (U.baseChange k) (U.baseChange k) ↔
      ∀ u ∈ U, basePointsRepresentation (H := H) M g u ∈ U := by
  have hmem : ∀ x : k ⊗[k] M, x ∈ U.baseChange k ↔ TensorProduct.lid k M x ∈ U := by
    intro x
    constructor
    · intro hx
      rw [Submodule.baseChange_eq_span] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨u, hu, rfl⟩ := hy
        simpa using hu
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact U.add_mem hx hy
      | smul a x _ hx => rw [map_smul]; exact U.smul_mem a hx
    · intro hx
      have hx' : x = 1 ⊗ₜ[k] TensorProduct.lid k M x := by
        rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
      rw [hx']
      exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  constructor
  · intro h u hu
    have h1 := h (show 1 ⊗ₜ[k] u ∈ (U.baseChange k : Set (k ⊗[k] M)) from
      Submodule.tmul_mem_baseChange_of_mem 1 hu)
    rw [SetLike.mem_coe, hmem, ← basePointsRepresentation_apply] at h1
    exact h1
  · intro h x hx
    rw [SetLike.mem_coe, hmem] at hx ⊢
    have hx' : x = 1 ⊗ₜ[k] TensorProduct.lid k M x := by
      rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
    rw [hx', ← basePointsRepresentation_apply]
    exact h _ hx

theorem exists_exteriorLine_of_mapsTo [FiniteDimensional k M] (U : Submodule k M)
    (P : Set (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ Set.MapsTo (endOfPoint M g.ofConv) (U.baseChange k) (U.baseChange k)) :
    ∃ ω : ExteriorAlgebra k M, ω ≠ 0 ∧
      (∀ g, g ∈ P ↔ basePointsRepresentation (H := H) (ExteriorAlgebra k M) g ω ∈ k ∙ ω) ∧
      (∀ f : M →ₗ[k] M, (∀ u ∈ U, f u ∈ U) → ExteriorAlgebra.map f ω ∈ k ∙ ω) ∧
      ∀ d : Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k),
        differential (R := k) (H := H) (M := ExteriorAlgebra k M) d ω ∈ k ∙ ω ↔
          ∀ u ∈ U, differential (R := k) (H := H) (M := M) d u ∈ U := by
  obtain ⟨ω, hω, hline, hmap, hdiff⟩ := exists_exteriorLine_basePointsRepresentation (H := H) U
  exact ⟨ω, hω, fun g => by rw [hP, mapsTo_endOfPoint_baseChange_iff, hline], hmap, hdiff⟩

end Points

section Hopf

attribute [local instance] TauCeti.Comodule.exteriorAlgebra

theorem exists_exteriorLine_quotientPointsSubgroup {H : _root_.CommHopfAlgCat.{u} k}
    (I : TauCeti.HopfIdeal k H) (V : TauCeti.Subcomodule k H H) [Module.Finite k V]
    (hgen : I.toIdeal ≤ Ideal.span ((V : Set H) ∩ (I : Set H))) :
    letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
    ∃ ω : ExteriorAlgebra k V, ω ≠ 0 ∧
      (∀ g : WithConv (H →ₐ[k] k),
        g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k) ↔
          basePointsRepresentation (H := H) (ExteriorAlgebra k V) g ω ∈ k ∙ ω) ∧
      (∀ f : V →ₗ[k] V, (∀ u ∈ I.definingSubspace V, f u ∈ I.definingSubspace V) →
        ExteriorAlgebra.map f ω ∈ k ∙ ω) ∧
      ∀ d : Derivation k H (TauCeti.Bialgebra.CounitAlgebra k H k),
        d ∈ I.lieSubalgebra (B := k) ↔
          differential (R := k) (H := H) (M := ExteriorAlgebra k V) d ω ∈ k ∙ ω := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup k
  obtain ⟨ω, hω, hpoint, hmap, hdiff⟩ := exists_exteriorLine_of_mapsTo (H := H) (I.definingSubspace V)
    (TauCeti.CommHopfAlgCat.quotientPointsSubgroup H I (CommAlgCat.of k k))
    fun g => I.mem_quotientPointsSubgroup_iff_mapsTo_definingSubspace V hgen (CommAlgCat.of k k) g
  refine ⟨ω, hω, hpoint, hmap, ?_⟩
  intro d
  rw [TauCeti.HopfIdeal.mem_lieSubalgebra_iff_preserves_definingSubspace I V hgen d, hdiff]

end Hopf

end CFSG.LieType.AlgebraicGroups.ClosedCone
