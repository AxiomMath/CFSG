module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitFixed

public noncomputable section

open WithConv TauCeti.Comodule MvPolynomial
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

attribute [local instance] TauCeti.Comodule.tensor

variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]

theorem orbitCone_eq_setOf_tmul_mem {w₀ : W} (hw₀ : w₀ ≠ 0) (f : F) :
    orbitCone k H f = {v | ∃ u : W, u ≠ 0 ∧ u ⊗ₜ[k] v ∈ orbitCone k H (w₀ ⊗ₜ[k] f)} := by
  have hgw : ∀ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) W g w₀ ≠ 0 := by
    intro g h0
    apply hw₀
    have := congrArg (basePointsRepresentation (H := H) W g⁻¹) h0
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  ext v
  constructor
  · rintro ⟨g, c, rfl⟩
    refine ⟨basePointsRepresentation (H := H) W g w₀, hgw g, g, c, ?_⟩
    rw [basePointsRepresentation_tmul, TensorProduct.tmul_smul]
  · rintro ⟨u, hu, g, c, hgc⟩
    obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual k W, θ u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hu ((Module.forall_dual_apply_eq_zero_iff k u).mp hcon)
    have h1 := congrArg ((TensorProduct.lid k F).toLinearMap ∘ₗ LinearMap.rTensor F θ) hgc
    rw [basePointsRepresentation_tmul, map_smul] at h1
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul] at h1
    refine ⟨g, (θ u)⁻¹ * (c * θ (basePointsRepresentation (H := H) W g w₀)), ?_⟩
    calc v = (θ u)⁻¹ • θ u • v := by rw [smul_smul, inv_mul_cancel₀ hθ, one_smul]
      _ = _ := by rw [h1, smul_smul, smul_smul, mul_assoc]

theorem isZariskiClosed_orbitCone_of_tmul [IsAlgClosed k] [FiniteDimensional k W]
    [FiniteDimensional k F] {w₀ : W} (hw₀ : w₀ ≠ 0) {f : F}
    (hY : IsZariskiClosed k (orbitCone k H (w₀ ⊗ₜ[k] f))) :
    IsZariskiClosed k (orbitCone k H f) := by
  classical
  let bW := Module.finBasis k W
  let bF := Module.finBasis k F
  let bT := bW.tensorProduct bF
  have hYc : IsCone k (orbitCone k H (w₀ ⊗ₜ[k] f)) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  obtain ⟨S₀, hS₀, hY'⟩ := hY.exists_isHomogeneous hYc bT
  let e : Fin (Module.finrank k W) × Fin (Module.finrank k F) →
      MvPolynomial (Fin (Module.finrank k W)) (MvPolynomial (Fin (Module.finrank k F)) k) :=
    fun ij => C (X ij.2) * X ij.1
  let S : Set (MvPolynomial (Fin (Module.finrank k W))
      (MvPolynomial (Fin (Module.finrank k F)) k)) := aeval e '' S₀
  have hS : ∀ q ∈ S, ∃ d, q.IsHomogeneous d := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨d, hd⟩ := hS₀ p hp
    refine ⟨1 * d, ?_⟩
    rw [aeval_def]
    exact hd.eval₂ _ _ (fun r => by rw [MvPolynomial.algebraMap_apply]; exact isHomogeneous_C _ _)
      fun ij => isHomogeneous_C_mul_X _ _
  have hev : ∀ (v : F) (u : W)
      (p : MvPolynomial (Fin (Module.finrank k W) × Fin (Module.finrank k F)) k),
      eval (bW.equivFun u) (map ((aeval (bF.equivFun v) :
        MvPolynomial (Fin (Module.finrank k F)) k →ₐ[k] k) :
          MvPolynomial (Fin (Module.finrank k F)) k →+* k) (aeval e p)) =
        eval (bT.equivFun (u ⊗ₜ[k] v)) p := by
    intro v u p
    have h1 : ((aeval (bW.equivFun u)).comp (mapAlgHom (aeval (bF.equivFun v)))).comp
        (aeval e) = aeval (bT.equivFun (u ⊗ₜ[k] v)) := by
      refine MvPolynomial.algHom_ext fun ⟨i, j⟩ => ?_
      simp [e, bT, Module.Basis.equivFun_apply, Module.Basis.tensorProduct_repr_tmul_apply]
    have h2 := congrArg (fun ψ => ψ p) h1
    simp only [AlgHom.comp_apply, mapAlgHom_apply] at h2
    exact h2
  have hset : {v | ∃ u : W, u ≠ 0 ∧ u ⊗ₜ[k] v ∈ orbitCone k H (w₀ ⊗ₜ[k] f)} =
      bF.equivFun ⁻¹' MvPolynomial.zeroLocus k (CFSG.eliminationIdeal S) := by
    ext v
    have key := CFSG.forall_mem_eliminationIdeal_iff hS (aeval (bF.equivFun v))
    rw [Set.mem_preimage, MvPolynomial.mem_zeroLocus_iff]
    refine Iff.trans ?_ key.symm
    constructor
    · rintro ⟨u, hu, hmem⟩
      refine ⟨bW.equivFun u, fun h => hu (bW.equivFun.injective (by rw [h, map_zero])), ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      rw [hev]
      exact (hY' _).mp hmem p hp
    · rintro ⟨u', hu', hall⟩
      refine ⟨bW.equivFun.symm u', fun h => hu' (by
        rw [← bW.equivFun.apply_symm_apply u', h, map_zero]), (hY' _).mpr fun p hp => ?_⟩
      have h := hall _ ⟨p, hp, rfl⟩
      rwa [← bW.equivFun.apply_symm_apply u', hev] at h
  rw [orbitCone_eq_setOf_tmul_mem hw₀ f, hset]
  exact isZariskiClosed_preimage_zeroLocus bF _

theorem finite_lines_of_relIndex_ne_zero {w₀ : W} {f : F} (B P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀)
    (hBf : ∀ b ∈ B, basePointsRepresentation (H := H) F b f ∈ k ∙ f) (hidx : B.relIndex P ≠ 0) :
    {ℓ : Submodule k F | ∃ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
        ℓ = k ∙ basePointsRepresentation (H := H) F g f}.Finite := by
  have : (B.subgroupOf P).FiniteIndex := Subgroup.finiteIndex_iff.mpr hidx
  have hline : ∀ p q : WithConv (H →ₐ[k] k), p⁻¹ * q ∈ B →
      k ∙ basePointsRepresentation (H := H) F p f = k ∙ basePointsRepresentation (H := H) F q f := by
    intro p q hpq
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hBf _ hpq)
    have hq : basePointsRepresentation (H := H) F q f =
        c • basePointsRepresentation (H := H) F p f := by
      rw [← map_smul, hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    by_cases hc0 : c = 0
    · have hf : f = 0 := by
        have h1 := congrArg (basePointsRepresentation (H := H) F q⁻¹) hq
        rw [hc0, zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply] at h1
        exact h1
      simp [hf]
    · rw [hq, Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0)]
  let φ : P ⧸ B.subgroupOf P → Submodule k F := Quotient.lift
    (fun p : P => k ∙ basePointsRepresentation (H := H) F (p : WithConv (H →ₐ[k] k)) f)
    fun p q hpq => by
      refine hline p q ?_
      have h := QuotientGroup.leftRel_apply.mp hpq
      rwa [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
  refine (Set.finite_range φ).subset ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨Quotient.mk _ ⟨g, (hP g).mpr hg⟩, rfl⟩

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]

theorem isZariskiClosed_orbitCone_of_finite_lines [FiniteDimensional k W] [FiniteDimensional k F]
    {w₀ : W} (hw₀ : w₀ ≠ 0) (hX : IsZariskiClosed k (orbitCone k H w₀)) {f : F} (hf : f ≠ 0)
    (hfin : {ℓ : Submodule k F | ∃ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
        ℓ = k ∙ basePointsRepresentation (H := H) F g f}.Finite) :
    IsZariskiClosed k (orbitCone k H f) :=
  isZariskiClosed_orbitCone_of_tmul hw₀ (isZariskiClosed_orbitCone_tmul hw₀ hX hf hfin)

theorem isZariskiClosed_orbitCone_of_relIndex_ne_zero [FiniteDimensional k W]
    [FiniteDimensional k F] {w₀ : W} (hw₀ : w₀ ≠ 0) (hX : IsZariskiClosed k (orbitCone k H w₀))
    {f : F} (hf : f ≠ 0) (B P : Subgroup (WithConv (H →ₐ[k] k)))
    (hP : ∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀)
    (hBf : ∀ b ∈ B, basePointsRepresentation (H := H) F b f ∈ k ∙ f) (hidx : B.relIndex P ≠ 0) :
    IsZariskiClosed k (orbitCone k H f) :=
  isZariskiClosed_orbitCone_of_finite_lines hw₀ hX hf
    (finite_lines_of_relIndex_ne_zero B P hP hBf hidx)

end CFSG.LieType.AlgebraicGroups.ClosedCone
