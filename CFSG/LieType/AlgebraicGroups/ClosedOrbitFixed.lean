module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitCone
public import CFSG.LieType.AlgebraicGroups.ConeIncidence
public import CFSG.LieType.AlgebraicGroups.ClosedSubgroupComponent
public import CFSG.Mathlib.RingTheory.KrullDimensionComparison
public import TauCeti.Algebra.Coalgebra.Comodule.Product

public noncomputable section

open WithConv TauCeti.Comodule MvPolynomial
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u

variable {k : Type u} [Field k] {H : Type u} [CommRing H] [HopfAlgebra k H]

section Coordinates

variable {M W : Type u} [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W]

@[expose] def coordPullback {m n : ℕ} (bM : Module.Basis (Fin m) k M)
    (bW : Module.Basis (Fin n) k W) (T : M →ₗ[k] W) :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin m) k :=
  aeval fun i => ∑ j, C (bW.coord i (T (bM j))) * X j

theorem aeval_coordPullback {m n : ℕ} (bM : Module.Basis (Fin m) k M)
    (bW : Module.Basis (Fin n) k W) (T : M →ₗ[k] W) (x : M) (p : MvPolynomial (Fin n) k) :
    aeval (bM.equivFun x) (coordPullback bM bW T p) = aeval (bW.equivFun (T x)) p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [AlgHom.comp_apply, coordPullback, aeval_X, aeval_X, map_sum]
  conv_rhs => rw [← bM.sum_equivFun x]
  rw [map_sum, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, map_smul,
    Pi.smul_apply, smul_eq_mul, Module.Basis.coord_apply, Module.Basis.equivFun_apply]
  ring

end Coordinates

section Kernel

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {M : Type u} [AddCommGroup M] [Module k M] [TauCeti.Comodule k H M]

theorem mem_ker_orbitComap_iff {n : ℕ} (b : Module.Basis (Fin n) k M) (v : M)
    (p : MvPolynomial (Fin n) k) :
    p ∈ RingHom.ker (orbitComap H b v) ↔ ∀ w ∈ orbitCone k H v, aeval (b.equivFun w) p = 0 :=
  ⟨fun hp _w hw => (MvPolynomial.mem_zeroLocus_iff.mp (orbitCone_subset_orbitClosure b v hw)) p hp,
    mem_ker_orbitComap b v⟩

theorem ker_orbitComap_eq_of_orbitCone_eq {n : ℕ} (b : Module.Basis (Fin n) k M) {v w : M}
    (h : orbitCone k H v = orbitCone k H w) :
    RingHom.ker (orbitComap H b v) = RingHom.ker (orbitComap H b w) := by
  ext p
  rw [mem_ker_orbitComap_iff, mem_ker_orbitComap_iff, h]

omit [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H] in
theorem orbitCone_eq_of_mem {v w : M} (hw : w ∈ orbitCone k H v) (hw0 : w ≠ 0) :
    orbitCone k H w = orbitCone k H v := by
  obtain ⟨g, c, rfl⟩ := hw
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw0 (zero_smul k _)
  ext x
  constructor
  · rintro ⟨h, d, rfl⟩
    refine ⟨h * g, d * c, ?_⟩
    rw [map_smul, map_mul, Module.End.mul_apply, smul_smul]
  · rintro ⟨h, d, rfl⟩
    refine ⟨h * g⁻¹, d * c⁻¹, ?_⟩
    rw [map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, mul_assoc,
      inv_mul_cancel₀ hc, mul_one]

theorem isZariskiClosed_orbitCone_of_ker_le {n : ℕ} (b : Module.Basis (Fin n) k M) {v : M}
    (h : ∀ w ∈ orbitClosure H b v, w ≠ 0 →
      RingHom.ker (orbitComap H b w) ≤ RingHom.ker (orbitComap H b v)) :
    IsZariskiClosed k (orbitCone k H v) := by
  obtain ⟨a, ha, hlift⟩ := exists_forall_exists_comp_eq (orbitComap H b v)
  suffices hsub : orbitClosure H b v ⊆ orbitCone k H v by
    rw [show orbitCone k H v = orbitClosure H b v from
      subset_antisymm (orbitCone_subset_orbitClosure b v) hsub]
    exact isZariskiClosed_orbitClosure b v
  intro w hw
  by_cases hw0 : w = 0
  · exact ⟨1, 0, by rw [hw0, zero_smul]⟩
  have heq : RingHom.ker (orbitComap H b w) = RingHom.ker (orbitComap H b v) :=
    le_antisymm (h w hw hw0) (ker_orbitComap_le_of_mem_orbitClosure b hw)
  have haw : orbitComap H b w a ≠ 0 := fun h0 =>
    ha (RingHom.mem_ker.mp (heq ▸ RingHom.mem_ker.mpr h0))
  have hX : ((1 : H) ⊗ₜ[k] (Polynomial.X : Polynomial k)) ≠ 0 := by
    intro h0
    have := congrArg (tensorPoint (1 : WithConv (H →ₐ[k] k)) (1 : k)) h0
    rw [tensorPoint_X, map_zero] at this
    exact one_ne_zero this
  obtain ⟨z, hz⟩ := TauCeti.exists_algHom_apply_ne_zero_of_ne_zero (k := k) (K := k)
    (mul_ne_zero haw hX)
  rw [map_mul] at hz
  have hza : z (orbitComap H b w a) ≠ 0 := left_ne_zero_of_mul hz
  have hzX : z (1 ⊗ₜ Polynomial.X) ≠ 0 := right_ne_zero_of_mul hz
  set g' := toConv (z.comp Algebra.TensorProduct.includeLeft)
  set c' := z (1 ⊗ₜ Polynomial.X)
  set w' := c' • basePointsRepresentation (H := H) M g' w
  have hw'v : w' ∈ orbitClosure H b w := orbitCone_subset_orbitClosure b w ⟨g', c', rfl⟩
  have hw'v' : b.equivFun w' ∈ MvPolynomial.zeroLocus k (RingHom.ker (orbitComap H b v)) := by
    rw [← heq]
    exact hw'v
  have haw' : MvPolynomial.aeval (b.equivFun w') a ≠ 0 := by
    rw [← comp_orbitComap b w z] at *
    exact hza
  obtain ⟨z₂, hz₂⟩ := hlift (MvPolynomial.aeval (b.equivFun w'))
    (fun p hp => (MvPolynomial.mem_zeroLocus_iff.mp hw'v') p (RingHom.mem_ker.mpr hp)) haw'
  obtain ⟨g₂, c₂, hgc⟩ := (mem_orbitCone_iff b v w').mpr ⟨z₂, hz₂⟩
  refine ⟨g'⁻¹ * g₂, c'⁻¹ * c₂, ?_⟩
  have h1 : basePointsRepresentation (H := H) M g'⁻¹ w' = c' • w := by
    simp only [w', map_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  rw [hgc, map_smul, ← Module.End.mul_apply, ← map_mul] at h1
  rw [mul_smul, h1, smul_smul, inv_mul_cancel₀ hzX, one_smul]

end Kernel

section Tensor

attribute [local instance] TauCeti.Comodule.tensor

variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]

theorem basePointsRepresentation_tmul (g : WithConv (H →ₐ[k] k)) (w : W) (f : F) :
    basePointsRepresentation (H := H) (W ⊗[k] F) g (w ⊗ₜ f) =
      basePointsRepresentation (H := H) W g w ⊗ₜ basePointsRepresentation (H := H) F g f := by
  have h := TauCeti.Comodule.endOfPoint_tensor_tmul (R := k) (H := H) (A := k) g.ofConv 1 1 w f
  rw [mul_one] at h
  rw [basePointsRepresentation_apply, ← h, basePointsRepresentation_apply,
    basePointsRepresentation_apply]
  generalize endOfPoint W g.ofConv (1 ⊗ₜ[k] w) = x
  generalize endOfPoint F g.ofConv (1 ⊗ₜ[k] f) = y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂, map_add,
      TensorProduct.add_tmul]
  | tmul a w' =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, map_add,
        TensorProduct.tmul_add]
    | tmul b f' =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, TensorProduct.lid_tmul,
        TensorProduct.lid_tmul, TensorProduct.lid_tmul, TensorProduct.smul_tmul_smul]

end Tensor


section Contraction

attribute [local instance] TauCeti.Comodule.tensor

variable {W F : Type u} [AddCommGroup W] [Module k W] [AddCommGroup F] [Module k F]

@[expose] def contract (φ : Module.Dual k F) : W ⊗[k] F →ₗ[k] W :=
  (TensorProduct.rid k W).toLinearMap ∘ₗ LinearMap.lTensor W φ

@[simp]
theorem contract_tmul (φ : Module.Dual k F) (w : W) (f : F) :
    contract φ (w ⊗ₜ f) = φ f • w := by
  simp [contract]

variable (k F) in
@[expose] def tensorCone (X : Set W) : Set (W ⊗[k] F) :=
  {z | ∃ w ∈ X, ∃ e : F, z = w ⊗ₜ e}

theorem isZariskiClosed_tensorCone [FiniteDimensional k W] [FiniteDimensional k F] {X : Set W}
    (hX : IsZariskiClosed k X) (hc : IsCone k X) (h0 : (0 : W) ∈ X) :
    IsZariskiClosed k (tensorCone k F X) := by
  classical
  let bW := Module.finBasis k W
  let bF := Module.finBasis k F
  let bT := bW.tensorProduct bF
  let c : Fin (Module.finrank k W) × Fin (Module.finrank k F) → Module.Dual k (W ⊗[k] F) :=
    fun ij => bT.coord ij
  let S : Set (MvPolynomial (Module.Dual k (W ⊗[k] F)) k) :=
    Set.range fun q : (Fin (Module.finrank k W) × Fin (Module.finrank k F)) ×
        (Fin (Module.finrank k W) × Fin (Module.finrank k F)) =>
      MvPolynomial.X (c (q.1.1, q.1.2)) * MvPolynomial.X (c (q.2.1, q.2.2)) -
        MvPolynomial.X (c (q.1.1, q.2.2)) * MvPolynomial.X (c (q.2.1, q.1.2))
  have key : tensorCone k F X = zeroSet k S ∩ ⋂ j, (contract (W := W) (bF.coord j)) ⁻¹' X := by
    ext z
    constructor
    · rintro ⟨w, hw, e, rfl⟩
      refine ⟨?_, Set.mem_iInter.mpr fun j => ?_⟩
      · rintro _ ⟨q, rfl⟩
        simp only [map_sub, map_mul, polyEval_X, c, bT, Module.Basis.coord_apply,
          Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
        ring
      · rw [Set.mem_preimage, contract_tmul]
        exact hc _ _ hw
    · rintro ⟨hS, hX'⟩
      rw [Set.mem_iInter] at hX'
      by_cases hz : z = 0
      · exact ⟨0, h0, 0, by rw [hz, TensorProduct.tmul_zero]⟩
      obtain ⟨⟨i₀, j₀⟩, hij⟩ : ∃ ij, bT.repr z ij ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hz (bT.repr.injective (Finsupp.ext fun ij => by simpa using hcon ij))
      set d := bT.repr z (i₀, j₀) with hd
      have hminor : ∀ i j, bT.repr z (i, j) * d = bT.repr z (i, j₀) * bT.repr z (i₀, j) := by
        intro i j
        have h := hS _ ⟨((i, j), (i₀, j₀)), rfl⟩
        simp only [map_sub, map_mul, polyEval_X, c, Module.Basis.coord_apply, sub_eq_zero] at h
        exact h
      set w := bW.equivFun.symm fun i => bT.repr z (i, j₀)
      set e := bF.equivFun.symm fun j => bT.repr z (i₀, j) / d
      have hw : ∀ i, bW.repr w i = bT.repr z (i, j₀) := fun i => by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      have he : ∀ j, bF.repr e j = bT.repr z (i₀, j) / d := fun j => by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      have hze : z = w ⊗ₜ e := by
        refine bT.repr.injective (Finsupp.ext fun ij => ?_)
        obtain ⟨i, j⟩ := ij
        rw [Module.Basis.tensorProduct_repr_tmul_apply, he, hw, smul_eq_mul]
        field_simp
        rw [mul_comm (bT.repr z (i₀, j)), ← hminor]
      refine ⟨w, ?_, e, hze⟩
      have h := hX' j₀
      rw [Set.mem_preimage, hze, contract_tmul, Module.Basis.coord_apply, he, ← hd,
        div_self hij, one_smul] at h
      exact h
  rw [key]
  exact (isZariskiClosed_zeroSet S).inter (isZariskiClosed_iInter fun j => hX.preimage _)

end Contraction


section Diagonal

attribute [local instance] TauCeti.Comodule.tensor

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]

theorem aeval_eq_zero_of_forall_contract {n : ℕ} (bW : Module.Basis (Fin n) k W) {w' : W}
    {e' : F} {φ : Module.Dual k F} (hφ : φ e' ≠ 0) {p : MvPolynomial (Fin n) k}
    (hp : ∀ (g : WithConv (H →ₐ[k] k)) (c : k),
      aeval (bW.equivFun ((c * φ (basePointsRepresentation (H := H) F g e')) •
        basePointsRepresentation (H := H) W g w')) p = 0)
    (g : WithConv (H →ₐ[k] k)) (μ : k) :
    aeval (bW.equivFun (μ • basePointsRepresentation (H := H) W g w')) p = 0 := by
  let h : H := aeval (fun i => μ • matrixCoefficient (C := H) (bW.coord i) w') p
  let γ : H := matrixCoefficient (C := H) φ e'
  have hh : ∀ x : WithConv (H →ₐ[k] k),
      x.ofConv h = aeval (bW.equivFun (μ • basePointsRepresentation (H := H) W x w')) p := by
    intro x
    rw [show x.ofConv h = aeval (fun i =>
        x.ofConv (μ • matrixCoefficient (C := H) (bW.coord i) w')) p from
      MvPolynomial.comp_aeval_apply _ x.ofConv p]
    congr 2
    funext i
    rw [map_smul, apply_matrixCoefficient, map_smul, Module.Basis.coord_apply, Pi.smul_apply,
      Module.Basis.equivFun_apply, smul_eq_mul]
  have hγ : ∀ x : WithConv (H →ₐ[k] k),
      x.ofConv γ = φ (basePointsRepresentation (H := H) F x e') :=
    fun x => apply_matrixCoefficient x φ e'
  have hzero : h * γ = 0 := by
    apply TauCeti.eq_of_forall_algHom_apply_eq (k := k) (K := k)
    intro f
    rw [map_mul, map_zero]
    have hfh : f h = (toConv f).ofConv h := rfl
    have hfγ : f γ = (toConv f).ofConv γ := rfl
    by_cases hx0 : f γ = 0
    · rw [hx0, mul_zero]
    · have h1 := hp (toConv f) (μ / f γ)
      rw [← hγ (toConv f), ← hfγ, div_mul_cancel₀ μ hx0, ← hh (toConv f), ← hfh] at h1
      rw [h1, zero_mul]
  have hγ0 : γ ≠ 0 := by
    intro h0
    have h1 := hγ 1
    rw [h0, map_zero, map_one, Module.End.one_apply] at h1
    exact hφ h1.symm
  have hh0 : h = 0 := (mul_eq_zero.mp hzero).resolve_right hγ0
  rw [← hh g, hh0, map_zero]

omit [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H] in
theorem finite_orbitCone_tmul_contract_eq {w₀ : W} (hw₀ : w₀ ≠ 0) {f : F}
    (hfin : {ℓ : Submodule k F | ∃ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
        ℓ = k ∙ basePointsRepresentation (H := H) F g f}.Finite)
    (φ : Module.Dual k F) (g₁ : WithConv (H →ₐ[k] k)) {c₁ : k}
    (hc₁ : c₁ * φ (basePointsRepresentation (H := H) F g₁ f) ≠ 0) :
    {x | x ∈ orbitCone k H (w₀ ⊗ₜ[k] f) ∧
      contract φ x = contract φ (c₁ • basePointsRepresentation (H := H) (W ⊗[k] F) g₁
        (w₀ ⊗ₜ[k] f))}.Finite := by
  set κ := c₁ * φ (basePointsRepresentation (H := H) F g₁ f) with hκ
  have hT : (⋃ ℓ ∈ {ℓ : Submodule k F | ∃ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
        ℓ = k ∙ basePointsRepresentation (H := H) F g f},
      {v : F | v ∈ ℓ ∧ φ (basePointsRepresentation (H := H) F g₁ v) = κ}).Finite := by
    refine hfin.biUnion fun ℓ hℓ => Set.Subsingleton.finite ?_
    obtain ⟨g, -, rfl⟩ := hℓ
    rintro _ ⟨hv, hvκ⟩ _ ⟨hv', hv'κ⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨s', rfl⟩ := Submodule.mem_span_singleton.mp hv'
    rw [map_smul, map_smul, smul_eq_mul] at hvκ hv'κ
    have hsκ : s * φ (basePointsRepresentation (H := H) F g₁
        (basePointsRepresentation (H := H) F g f)) ≠ 0 := by
      rw [hvκ]
      exact hc₁
    rw [mul_right_cancel₀ (right_ne_zero_of_mul hsκ) (hvκ.trans hv'κ.symm)]
  refine (hT.image fun v => basePointsRepresentation (H := H) W g₁ w₀ ⊗ₜ[k]
    basePointsRepresentation (H := H) F g₁ v).subset ?_
  rintro _ ⟨⟨g, c, rfl⟩, hx⟩
  rw [map_smul, map_smul, basePointsRepresentation_tmul, basePointsRepresentation_tmul,
    contract_tmul, contract_tmul, smul_smul, smul_smul, ← hκ] at hx
  have hg₁w : basePointsRepresentation (H := H) W g₁ w₀ ≠ 0 := by
    intro h0
    apply hw₀
    have := congrArg (basePointsRepresentation (H := H) W g₁⁻¹) h0
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  have ha0 : c * φ (basePointsRepresentation (H := H) F g f) ≠ 0 := by
    intro h0
    rw [h0, zero_smul, eq_comm, smul_eq_zero] at hx
    exact hx.elim hc₁ hg₁w
  set a := c * φ (basePointsRepresentation (H := H) F g f) with ha
  have hgw : basePointsRepresentation (H := H) W g w₀ =
      (a⁻¹ * κ) • basePointsRepresentation (H := H) W g₁ w₀ := by
    rw [mul_smul, ← hx, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  refine ⟨(c * (a⁻¹ * κ)) • basePointsRepresentation (H := H) F (g₁⁻¹ * g) f,
    Set.mem_biUnion ⟨g₁⁻¹ * g, ?_, rfl⟩
      ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩, ?_⟩
  · refine Submodule.mem_span_singleton.mpr ⟨a⁻¹ * κ, ?_⟩
    rw [map_mul, Module.End.mul_apply, hgw, map_smul, ← Module.End.mul_apply, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_apply]
  · rw [map_smul, map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, smul_eq_mul]
    calc c * (a⁻¹ * κ) * φ (basePointsRepresentation (H := H) F g f)
        = c * φ (basePointsRepresentation (H := H) F g f) * a⁻¹ * κ := by ring
      _ = κ := by rw [← ha, mul_inv_cancel₀ ha0, one_mul]
  · show basePointsRepresentation (H := H) W g₁ w₀ ⊗ₜ[k] basePointsRepresentation (H := H) F g₁
        ((c * (a⁻¹ * κ)) • basePointsRepresentation (H := H) F (g₁⁻¹ * g) f) =
      c • basePointsRepresentation (H := H) (W ⊗[k] F) g (w₀ ⊗ₜ[k] f)
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left,
      basePointsRepresentation_tmul, hgw, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul]

end Diagonal


section Dimension

attribute [local instance] TauCeti.Comodule.tensor

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]

theorem ringKrullDim_orbitComap_tmul_le {m n : ℕ} (bM : Module.Basis (Fin m) k (W ⊗[k] F))
    (bW : Module.Basis (Fin n) k W) {w₀ : W} (hw₀ : w₀ ≠ 0) {f : F} {φ : Module.Dual k F}
    (hφ : φ f ≠ 0)
    (hfin : {ℓ : Submodule k F | ∃ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
        ℓ = k ∙ basePointsRepresentation (H := H) F g f}.Finite) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ RingHom.ker (orbitComap H bM (w₀ ⊗ₜ[k] f))) ≤
      ringKrullDim (MvPolynomial (Fin n) k ⧸ RingHom.ker (orbitComap H bW w₀)) := by
  classical
  set KX := RingHom.ker (orbitComap H bW w₀) with hKX
  set K0 := RingHom.ker (orbitComap H bM (w₀ ⊗ₜ[k] f)) with hK0
  have : KX.IsPrime := RingHom.ker_isPrime _
  have : K0.IsPrime := RingHom.ker_isPrime _
  have hL : KX ≤ K0.comap (coordPullback bM bW (contract φ)) := by
    intro p hp
    rw [Ideal.mem_comap, hK0, mem_ker_orbitComap_iff]
    rintro _ ⟨g, c, rfl⟩
    rw [aeval_coordPullback]
    rw [hKX, mem_ker_orbitComap_iff] at hp
    apply hp
    rw [map_smul, basePointsRepresentation_tmul, contract_tmul, smul_smul]
    exact ⟨g, c * φ (basePointsRepresentation (H := H) F g f), rfl⟩
  let φ0 := Ideal.quotientMapₐ K0 (coordPullback bM bW (contract φ)) hL
  obtain ⟨a, ha, hlift⟩ := exists_forall_exists_comp_eq (orbitComap H bM (w₀ ⊗ₜ[k] f))
  set ā : MvPolynomial (Fin m) k ⧸ K0 := Ideal.Quotient.mk K0 a with hā_def
  have hā : ā ≠ 0 := fun h0 =>
    ha (RingHom.mem_ker.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0))
  let S := Localization.Away ā
  have : IsDomain S :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hā)
  have : Algebra.FinitePresentation (MvPolynomial (Fin m) k ⧸ K0) S :=
    IsLocalization.Away.finitePresentation ā
  have : Algebra.FiniteType k S :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin m) k ⧸ K0) inferInstance inferInstance
  rw [← TauCeti.ringKrullDim_localization_away k hā]
  let ι : (MvPolynomial (Fin m) k ⧸ K0) →ₐ[k] S :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin m) k ⧸ K0) S
  obtain ⟨θ, hθ⟩ : ∃ θ : Module.Dual k W, θ w₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw₀ ((Module.forall_dual_apply_eq_zero_iff k w₀).mp hcon)
  let pθ : MvPolynomial (Fin m) k := ∑ i, C (θ (contract φ (bM i))) * X i
  have hpθ : ∀ x, aeval (bM.equivFun x) pθ = θ (contract φ x) := by
    intro x
    simp only [pθ, map_sum, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    conv_rhs => rw [← bM.sum_equivFun x]
    simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have hb : orbitComap H bM (w₀ ⊗ₜ[k] f) pθ ≠ 0 := by
    intro h0
    have h1 : ((tensorPoint (1 : WithConv (H →ₐ[k] k)) (1 : k)).comp
        (orbitComap H bM (w₀ ⊗ₜ[k] f))) pθ = 0 := by
      rw [AlgHom.comp_apply, h0, map_zero]
    rw [comp_orbitComap, tensorPoint_X, tensorPoint_comp_includeLeft, hpθ, one_smul, map_one,
      Module.End.one_apply, contract_tmul, map_smul, smul_eq_mul] at h1
    exact mul_ne_zero hφ hθ h1
  obtain ⟨t₁, ht₁⟩ := TauCeti.exists_algHom_apply_ne_zero_of_ne_zero (k := k) (K := k)
    (mul_ne_zero ha hb)
  rw [map_mul] at ht₁
  have ht₁a := left_ne_zero_of_mul ht₁
  have ht₁b := right_ne_zero_of_mul ht₁
  set g₁ := toConv (t₁.comp Algebra.TensorProduct.includeLeft)
  set c₁ := t₁ (1 ⊗ₜ Polynomial.X)
  set x₁ := c₁ • basePointsRepresentation (H := H) (W ⊗[k] F) g₁ (w₀ ⊗ₜ[k] f) with hx₁
  have hy₁ : t₁.comp (orbitComap H bM (w₀ ⊗ₜ[k] f)) = aeval (bM.equivFun x₁) :=
    comp_orbitComap bM _ t₁
  have hc₁ : c₁ * φ (basePointsRepresentation (H := H) F g₁ f) ≠ 0 := by
    have h1 : t₁ (orbitComap H bM (w₀ ⊗ₜ[k] f) pθ) =
        (c₁ * φ (basePointsRepresentation (H := H) F g₁ f)) *
          θ (basePointsRepresentation (H := H) W g₁ w₀) := by
      have h2 := congrArg (fun z : MvPolynomial (Fin m) k →ₐ[k] k => z pθ) hy₁
      simp only [AlgHom.comp_apply] at h2
      rw [h2, hpθ, hx₁, map_smul, basePointsRepresentation_tmul, contract_tmul, smul_smul,
        map_smul, smul_eq_mul]
    rw [h1] at ht₁b
    exact left_ne_zero_of_mul ht₁b
  have hy₁K : ∀ p ∈ K0, aeval (bM.equivFun x₁) p = 0 := by
    intro p hp
    rw [← hy₁, AlgHom.comp_apply, RingHom.mem_ker.mp hp, map_zero]
  let yb₁ := Ideal.Quotient.liftₐ K0 (aeval (bM.equivFun x₁)) hy₁K
  have hyb₁ : ∀ p, yb₁ (Ideal.Quotient.mk K0 p) = aeval (bM.equivFun x₁) p := fun p => rfl
  have hyb₁a : yb₁ ā ≠ 0 := by
    rw [hā_def, hyb₁, ← hy₁, AlgHom.comp_apply]
    exact ht₁a
  have hunit : ∀ y : Submonoid.powers ā, IsUnit (yb₁ y) := by
    rintro ⟨_, j, rfl⟩
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr hyb₁a).pow j
  let s : S →ₐ[k] k := IsLocalization.liftAlgHom (M := Submonoid.powers ā) (S := S) hunit
  have hs : ∀ r, s (ι r) = yb₁ r := fun r => by
    rw [IsLocalization.liftAlgHom_apply]
    exact IsLocalization.lift_eq _ r
  refine CFSG.ringKrullDim_le_of_finite_fiber (ι.comp φ0) s ?_
  let vec : (S →ₐ[k] k) → W ⊗[k] F := fun s' =>
    bM.equivFun.symm fun i => s' (ι (Ideal.Quotient.mk K0 (X i)))
  have hvec : ∀ s' : S →ₐ[k] k,
      (s'.comp ι).comp (Ideal.Quotient.mkₐ k K0) = aeval (bM.equivFun (vec s')) := by
    intro s'
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [aeval_X, LinearEquiv.apply_symm_apply]
    rfl
  have hinj : Function.Injective vec := by
    intro s₁ s₂ h
    have h1 : (s₁.comp ι).comp (Ideal.Quotient.mkₐ k K0) =
        (s₂.comp ι).comp (Ideal.Quotient.mkₐ k K0) := by
      rw [hvec, hvec, h]
    have h2 : s₁.comp ι = s₂.comp ι := Ideal.Quotient.algHom_ext k h1
    exact IsLocalization.algHom_ext (Submonoid.powers ā) h2
  refine ((finite_orbitCone_tmul_contract_eq hw₀ hfin φ g₁ hc₁).preimage
    hinj.injOn).subset ?_
  intro s' hs'
  rw [Set.mem_setOf_eq] at hs'
  have hy' := hvec s'
  refine ⟨?_, ?_⟩
  · obtain ⟨z₂, hz₂⟩ := hlift (aeval (bM.equivFun (vec s'))) (fun p hp => by
        rw [← hy', AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.mpr (RingHom.mem_ker.mpr hp), map_zero, map_zero])
      (by
        rw [← hy', AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← hā_def]
        exact ((IsLocalization.Away.algebraMap_isUnit (S := S) ā).map s').ne_zero)
    exact (mem_orbitCone_iff bM _ _).mpr ⟨z₂, hz₂⟩
  · refine bW.equivFun.injective (funext fun i => ?_)
    have h1 := congrArg (fun t : (MvPolynomial (Fin n) k ⧸ KX) →ₐ[k] k =>
      t (Ideal.Quotient.mk KX (X i))) hs'
    simp only [AlgHom.comp_apply] at h1
    rw [show φ0 (Ideal.Quotient.mk KX (X i)) =
      Ideal.Quotient.mk K0 (coordPullback bM bW (contract φ) (X i)) from rfl, hs, hyb₁] at h1
    have h2 : s' (ι (Ideal.Quotient.mk K0 (coordPullback bM bW (contract φ) (X i)))) =
        aeval (bM.equivFun (vec s')) (coordPullback bM bW (contract φ) (X i)) := by
      rw [← hy']
      rfl
    rw [h2, aeval_coordPullback, aeval_coordPullback, aeval_X, aeval_X] at h1
    exact h1

end Dimension

section Closed

attribute [local instance] TauCeti.Comodule.tensor

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]
variable {W F : Type u} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]
  [AddCommGroup F] [Module k F] [TauCeti.Comodule k H F]

theorem isZariskiClosed_orbitCone_tmul [FiniteDimensional k W] [FiniteDimensional k F]
    {w₀ : W} (hw₀ : w₀ ≠ 0) (hX : IsZariskiClosed k (orbitCone k H w₀)) {f : F} (hf : f ≠ 0)
    (hfin : {ℓ : Submodule k F | ∃ g : WithConv (H →ₐ[k] k),
      basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
        ℓ = k ∙ basePointsRepresentation (H := H) F g f}.Finite) :
    IsZariskiClosed k (orbitCone k H (w₀ ⊗ₜ[k] f)) := by
  classical
  let bM := Module.finBasis k (W ⊗[k] F)
  let bW := Module.finBasis k W
  have hXc : IsCone k (orbitCone k H w₀) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  have hX0 : (0 : W) ∈ orbitCone k H w₀ := ⟨1, 0, by rw [zero_smul]⟩
  have hcl : orbitClosure H bM (w₀ ⊗ₜ[k] f) ⊆ tensorCone k F (orbitCone k H w₀) :=
    orbitClosure_subset bM _ (isZariskiClosed_tensorCone hX hXc hX0) (by
      rintro _ ⟨g, c, rfl⟩
      rw [basePointsRepresentation_tmul, TensorProduct.smul_tmul']
      exact ⟨_, ⟨g, c, rfl⟩, _, rfl⟩)
  refine isZariskiClosed_orbitCone_of_ker_le bM fun w hw hw0 => ?_
  by_contra hne
  set KX := RingHom.ker (orbitComap H bW w₀) with hKX
  set K0 := RingHom.ker (orbitComap H bM (w₀ ⊗ₜ[k] f)) with hK0
  set Kw := RingHom.ker (orbitComap H bM w) with hKw
  have : KX.IsPrime := RingHom.ker_isPrime _
  have : K0.IsPrime := RingHom.ker_isPrime _
  have : Kw.IsPrime := RingHom.ker_isPrime _
  have hle : K0 ≤ Kw := ker_orbitComap_le_of_mem_orbitClosure bM hw
  have hii : ringKrullDim (MvPolynomial (Fin (Module.finrank k (W ⊗[k] F))) k ⧸ Kw) <
      ringKrullDim (MvPolynomial (Fin (Module.finrank k (W ⊗[k] F))) k ⧸ K0) := by
    have hne' : Kw.map (Ideal.Quotient.mk K0) ≠ ⊥ := by
      intro hbot
      apply hne
      intro p hp
      have h0 : Ideal.Quotient.mk K0 p = 0 := by
        rw [← Ideal.mem_bot, ← hbot]
        exact Ideal.mem_map_of_mem _ hp
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    rw [← ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)]
    exact CFSG.ringKrullDim_quotient_lt_of_ne_bot (k := k) hne'
  have hiii : ringKrullDim (MvPolynomial (Fin (Module.finrank k W)) k ⧸ KX) ≤
      ringKrullDim (MvPolynomial (Fin (Module.finrank k (W ⊗[k] F))) k ⧸ Kw) := by
    obtain ⟨w', hw'X, e', hwe⟩ := hcl hw
    have hw'0 : w' ≠ 0 := by
      rintro rfl
      exact hw0 (by rw [hwe, TensorProduct.zero_tmul])
    have he'0 : e' ≠ 0 := by
      rintro rfl
      exact hw0 (by rw [hwe, TensorProduct.tmul_zero])
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k F, φ e' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he'0 ((Module.forall_dual_apply_eq_zero_iff k e').mp hcon)
    have hcone : orbitCone k H w' = orbitCone k H w₀ := orbitCone_eq_of_mem hw'X hw'0
    have hmapX : KX ≤ Kw.comap (coordPullback bM bW (contract φ)) := by
      intro p hp
      rw [Ideal.mem_comap, hKw, mem_ker_orbitComap_iff]
      rintro _ ⟨g, c, rfl⟩
      rw [aeval_coordPullback]
      rw [hKX, mem_ker_orbitComap_iff] at hp
      apply hp
      rw [hwe, map_smul, basePointsRepresentation_tmul, contract_tmul, smul_smul, ← hcone]
      exact ⟨g, c * φ (basePointsRepresentation (H := H) F g e'), rfl⟩
    refine CFSG.ringKrullDim_le_of_injective (k := k)
      (Ideal.quotientMapₐ Kw (coordPullback bM bW (contract φ)) hmapX) ?_
    refine Ideal.quotientMap_injective' (H := hmapX) fun p hp => ?_
    rw [Ideal.mem_comap, hKw, mem_ker_orbitComap_iff] at hp
    rw [hKX, ← ker_orbitComap_eq_of_orbitCone_eq bW hcone, mem_ker_orbitComap_iff]
    rintro _ ⟨g, μ, rfl⟩
    refine aeval_eq_zero_of_forall_contract bW hφ (fun g' c => ?_) g μ
    have h1 : aeval (bM.equivFun (c • basePointsRepresentation (H := H) (W ⊗[k] F) g' w))
        (coordPullback bM bW (contract φ) p) = 0 := hp _ ⟨g', c, rfl⟩
    rwa [aeval_coordPullback, hwe, map_smul, basePointsRepresentation_tmul, contract_tmul,
      smul_smul] at h1
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : Module.Dual k F, φ₀ f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf ((Module.forall_dual_apply_eq_zero_iff k f).mp hcon)
  have hi := ringKrullDim_orbitComap_tmul_le bM bW hw₀ hφ₀ hfin
  exact lt_irrefl _ ((hiii.trans_lt hii).trans_le hi)

end Closed


section Ratio

variable [IsAlgClosed k]
variable {M W : Type u} [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W]

theorem exists_ideal_iff_exists_eq_smul [FiniteDimensional k M] [FiniteDimensional k W]
    {Y : Set M} (hY : IsZariskiClosed k Y) (hc : IsCone k Y) (A L : M →ₗ[k] W) :
    ∃ J : Ideal (Polynomial k), ∀ t : k,
      (∀ a ∈ J, a.eval t = 0) ↔ ∃ y ∈ Y, y ≠ 0 ∧ A y = t • L y := by
  classical
  let bM := Module.finBasis k M
  let bW := Module.finBasis k W
  obtain ⟨S₀, hS₀, hY'⟩ := hY.exists_isHomogeneous hc bM
  let lin : Fin (Module.finrank k W) → MvPolynomial (Fin (Module.finrank k M)) (Polynomial k) :=
    fun i => ∑ j, C (Polynomial.C (bW.coord i (A (bM j))) -
      Polynomial.X * Polynomial.C (bW.coord i (L (bM j)))) * X j
  let S : Set (MvPolynomial (Fin (Module.finrank k M)) (Polynomial k)) :=
    map (algebraMap k (Polynomial k)) '' S₀ ∪ Set.range lin
  have hS : ∀ f ∈ S, ∃ n, f.IsHomogeneous n := by
    rintro f (⟨p, hp, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨n, hn⟩ := hS₀ p hp
      exact ⟨n, hn.map _⟩
    · exact ⟨1, IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ j⟩
  have hmap : ∀ (t : k) (p : MvPolynomial (Fin (Module.finrank k M)) k),
      map ((Polynomial.aeval t : Polynomial k →ₐ[k] k) : Polynomial k →+* k)
        (map (algebraMap k (Polynomial k)) p) = p := fun t p => by
    rw [map_map, AlgHom.comp_algebraMap, Algebra.algebraMap_self, map_id]
  have hlin : ∀ (t : k) (y : M) (i : Fin (Module.finrank k W)),
      eval (bM.equivFun y) (map ((Polynomial.aeval t : Polynomial k →ₐ[k] k) : Polynomial k →+* k)
        (lin i)) = bW.equivFun (A y) i - t * bW.equivFun (L y) i := by
    intro t y i
    simp only [lin, map_sum, map_mul, map_C, map_X, eval_X, eval_C, RingHom.coe_coe, map_sub,
      Polynomial.aeval_C, Polynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    conv_rhs => rw [← bM.sum_equivFun y]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.coord_apply, Module.Basis.equivFun_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨CFSG.eliminationIdeal S, fun t => ?_⟩
  have key := CFSG.forall_mem_eliminationIdeal_iff hS (Polynomial.aeval t)
  simp only [Polynomial.coe_aeval_eq_eval] at key
  rw [key]
  constructor
  · rintro ⟨v, hv, hvS⟩
    have hy0 : bM.equivFun.symm v ≠ 0 := fun h0 => hv (by
      rw [← bM.equivFun.apply_symm_apply v, h0, map_zero])
    refine ⟨bM.equivFun.symm v, (hY' _).mpr fun p hp => ?_, hy0, ?_⟩
    · have h := hvS _ (Or.inl ⟨p, hp, rfl⟩)
      rwa [hmap, ← bM.equivFun.apply_symm_apply v] at h
    · refine bW.equivFun.injective (funext fun i => ?_)
      have h := hvS _ (Or.inr ⟨i, rfl⟩)
      rw [← bM.equivFun.apply_symm_apply v, hlin, sub_eq_zero] at h
      rw [h, map_smul, Pi.smul_apply, smul_eq_mul]
  · rintro ⟨y, hyY, hy0, hAy⟩
    refine ⟨bM.equivFun y, fun h => hy0 (bM.equivFun.injective (by rw [h, map_zero])), ?_⟩
    rintro f (⟨p, hp, rfl⟩ | ⟨i, rfl⟩)
    · rw [hmap]
      exact (hY' y).mp hyY p hp
    · rw [hlin, hAy, map_smul, Pi.smul_apply, smul_eq_mul, sub_self]

end Ratio

section Fixed

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H]

omit [IsAlgClosed k] [Algebra.FiniteType k H] [IsDomain H] in
theorem basePointsRepresentation_comm_hom {V V' : Type u} [AddCommGroup V] [Module k V]
    [TauCeti.Comodule k H V] [AddCommGroup V'] [Module k V'] [TauCeti.Comodule k H V']
    (f : TauCeti.Comodule.Hom k H V V') (g : WithConv (H →ₐ[k] k)) (v : V) :
    f.toLinearMap (basePointsRepresentation (H := H) V g v) =
      basePointsRepresentation (H := H) V' g (f.toLinearMap v) := by
  have h := LinearMap.congr_fun (TauCeti.Comodule.baseChange_comp_endOfPoint (A := k) f g.ofConv)
    (1 ⊗ₜ v)
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul] at h
  rw [basePointsRepresentation_apply, basePointsRepresentation_apply, ← h]
  generalize endOfPoint V g.ofConv (1 ⊗ₜ[k] v) = x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a w => simp only [TensorProduct.lid_tmul, LinearMap.baseChange_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

attribute [local instance] TauCeti.Comodule.tensor

theorem basePointsRepresentation_eq_of_finite {W E : Type u} [AddCommGroup W] [Module k W]
    [TauCeti.Comodule k H W] [FiniteDimensional k W] [AddCommGroup E] [Module k E]
    [TauCeti.Comodule k H E] [FiniteDimensional k E]
    {w₀ : W} (hw₀ : w₀ ≠ 0) (hX : IsZariskiClosed k (orbitCone k H w₀)) {u : E}
    (hfin : {y | ∃ g : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀ ∧
      y = basePointsRepresentation (H := H) E g u}.Finite)
    (g : WithConv (H →ₐ[k] k)) : basePointsRepresentation (H := H) E g u = u := by
  classical
  let : TauCeti.Comodule k H k := TauCeti.Comodule.trivial
  let : TauCeti.Comodule k H (E × k) := TauCeti.Comodule.Prod
  have hfst : ∀ (h : WithConv (H →ₐ[k] k)) (x : E × k),
      (basePointsRepresentation (H := H) (E × k) h x).1 =
        basePointsRepresentation (H := H) E h x.1 :=
    fun h x => basePointsRepresentation_comm_hom TauCeti.Comodule.prodFst h x
  have hsnd : ∀ (h : WithConv (H →ₐ[k] k)) (x : E × k),
      (basePointsRepresentation (H := H) (E × k) h x).2 = x.2 := by
    intro h x
    have h1 := basePointsRepresentation_comm_hom
      (TauCeti.Comodule.prodSnd (R := k) (C := H) (M := E) (N := k)) h x
    refine h1.trans (basePointsRepresentation_eq_of_coact_eq_tmul_one _ rfl h)
  let f : E × k := (u, 1)
  let ψ : Module.Dual k (E × k) := LinearMap.snd k E k
  have hψ : ∀ (h : WithConv (H →ₐ[k] k)) (x : E × k),
      ψ (basePointsRepresentation (H := H) (E × k) h x) = ψ x := fun h x => hsnd h x
  have hfin' : {y | ∃ h : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) W h w₀ ∈ k ∙ w₀ ∧
      y = basePointsRepresentation (H := H) (E × k) h f}.Finite := by
    refine (hfin.image fun e => ((e, 1) : E × k)).subset ?_
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨basePointsRepresentation (H := H) E h u, ⟨h, hh, rfl⟩,
      Prod.ext (hfst h f).symm (hsnd h f).symm⟩
  have hf0 : f ≠ 0 := by
    intro h0
    have h1 := congrArg Prod.snd h0
    simp [f] at h1
  have hY := isZariskiClosed_orbitCone_tmul hw₀ hX hf0 ((hfin'.image fun y => k ∙ y).subset (by
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨_, ⟨h, hh, rfl⟩, rfl⟩))
  have hYc : IsCone k (orbitCone k H (w₀ ⊗ₜ[k] f)) := by
    rintro c _ ⟨h, d, rfl⟩
    exact ⟨h, c * d, by rw [smul_smul]⟩
  have hpt : ∀ (φ : Module.Dual k (E × k)) (h : WithConv (H →ₐ[k] k)) (c : k),
      contract (W := W) φ (c • basePointsRepresentation (H := H) (W ⊗[k] (E × k)) h (w₀ ⊗ₜ f)) =
        (c * φ (basePointsRepresentation (H := H) (E × k) h f)) •
          basePointsRepresentation (H := H) W h w₀ := by
    intro φ h c
    rw [map_smul, basePointsRepresentation_tmul, contract_tmul, smul_smul]
  have hgw : ∀ h : WithConv (H →ₐ[k] k), basePointsRepresentation (H := H) W h w₀ ≠ 0 := by
    intro h h0
    apply hw₀
    have := congrArg (basePointsRepresentation (H := H) W h⁻¹) h0
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  suffices hconst : ∀ φ : Module.Dual k E, ∀ h : WithConv (H →ₐ[k] k),
      φ (basePointsRepresentation (H := H) E h u) = φ u by
    have h0 : ∀ φ : Module.Dual k E, φ (basePointsRepresentation (H := H) E g u - u) = 0 :=
      fun φ => by rw [map_sub, hconst φ g, sub_self]
    exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff k _).mp h0)
  intro φ
  let φ' : Module.Dual k (E × k) := φ ∘ₗ LinearMap.fst k E k
  have hφ' : ∀ h : WithConv (H →ₐ[k] k),
      φ' (basePointsRepresentation (H := H) (E × k) h f) =
        φ (basePointsRepresentation (H := H) E h u) := fun h => by
    simp only [φ', LinearMap.comp_apply, LinearMap.fst_apply, hfst, f]
  obtain ⟨J₁, hJ₁⟩ := exists_ideal_iff_exists_eq_smul hY hYc (contract (W := W) φ')
    (contract (W := W) ψ)
  obtain ⟨J₂, hJ₂⟩ := exists_ideal_iff_exists_eq_smul hY hYc (contract (W := W) ψ)
    (contract (W := W) φ')
  have hne0 : ∀ h : WithConv (H →ₐ[k] k),
      (1 : k) • basePointsRepresentation (H := H) (W ⊗[k] (E × k)) h (w₀ ⊗ₜ f) ≠ 0 := by
    intro h h0
    have h1 := congrArg (contract (W := W) ψ) h0
    rw [hpt, map_zero, hψ] at h1
    simp only [ψ, f, LinearMap.snd_apply, mul_one, one_smul] at h1
    exact hgw h h1
  have hval : ∀ t : k, (∀ a ∈ J₁, a.eval t = 0) ↔
      ∃ h : WithConv (H →ₐ[k] k), φ (basePointsRepresentation (H := H) E h u) = t := by
    intro t
    rw [hJ₁]
    constructor
    · rintro ⟨_, ⟨h, c, rfl⟩, hy0, hy⟩
      rw [hpt, hpt, hψ, hφ', smul_smul] at hy
      have hc : c ≠ 0 := by
        rintro rfl
        exact hy0 (zero_smul k _)
      refine ⟨h, ?_⟩
      have h2 := (smul_left_injective k (hgw h)) hy
      simp only [ψ, f, LinearMap.snd_apply, mul_one] at h2
      exact mul_left_cancel₀ hc (by rw [h2, mul_comm])
    · rintro ⟨h, rfl⟩
      refine ⟨_, ⟨h, 1, rfl⟩, hne0 h, ?_⟩
      rw [hpt, hpt, hψ, hφ', smul_smul]
      simp only [ψ, f, LinearMap.snd_apply, one_mul, mul_one]
  have hinv : ∀ t : k, (∀ a ∈ J₂, a.eval t = 0) ↔
      ∃ h : WithConv (H →ₐ[k] k), t * φ (basePointsRepresentation (H := H) E h u) = 1 := by
    intro t
    rw [hJ₂]
    constructor
    · rintro ⟨_, ⟨h, c, rfl⟩, hy0, hy⟩
      rw [hpt, hpt, hψ, hφ', smul_smul] at hy
      have hc : c ≠ 0 := by
        rintro rfl
        exact hy0 (zero_smul k _)
      refine ⟨h, ?_⟩
      have h2 := (smul_left_injective k (hgw h)) hy
      simp only [ψ, f, LinearMap.snd_apply, mul_one] at h2
      exact mul_left_cancel₀ hc (by linear_combination (-1 : k) * h2)
    · rintro ⟨h, ht⟩
      refine ⟨_, ⟨h, 1, rfl⟩, hne0 h, ?_⟩
      rw [hpt, hpt, hψ, hφ', smul_smul]
      simp only [ψ, f, LinearMap.snd_apply, one_mul]
      rw [ht]
  by_cases hJ : J₁ = ⊥
  · exfalso
    have hall : ∀ t : k, t ≠ 0 → ∀ a ∈ J₂, a.eval t = 0 := by
      intro t ht
      rw [hinv]
      obtain ⟨h, hh⟩ := (hval t⁻¹).mp fun a ha => by
        rw [hJ, Ideal.mem_bot] at ha
        rw [ha, Polynomial.eval_zero]
      exact ⟨h, by rw [hh, mul_inv_cancel₀ ht]⟩
    have h0 : ¬ ∀ a ∈ J₂, a.eval (0 : k) = 0 := by
      rw [hinv]
      rintro ⟨h, hh⟩
      rw [zero_mul] at hh
      exact zero_ne_one hh
    push Not at h0
    obtain ⟨a, haJ, ha0⟩ := h0
    have hane : a ≠ 0 := fun h => ha0 (by rw [h, Polynomial.eval_zero])
    apply hane
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono (fun t ht => ?_)
      (Set.infinite_univ.diff (Set.finite_singleton (0 : k)))
    exact hall t ht.2 a haJ
  · obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    have hroot : ∀ h : WithConv (H →ₐ[k] k),
        φ (basePointsRepresentation (H := H) E h u) ∈ a.roots.toFinset := by
      intro h
      rw [Multiset.mem_toFinset, Polynomial.mem_roots ha0, Polynomial.IsRoot.def]
      exact (hval _).mpr ⟨h, rfl⟩ a haJ
    let mc : H := matrixCoefficient (C := H) φ u
    have hmc : ∀ h : WithConv (H →ₐ[k] k),
        h.ofConv mc = φ (basePointsRepresentation (H := H) E h u) :=
      fun h => apply_matrixCoefficient h φ u
    obtain ⟨i, hi⟩ := TorusConjugacy.exists_forall_apply_eq_zero_of_forall_exists (k := k)
      (Z := H) (fun i : a.roots.toFinset => ({mc - algebraMap k H i} : Set H)) fun y => by
        refine ⟨⟨_, hroot (toConv y)⟩, ?_⟩
        rintro _ rfl
        rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero]
        exact hmc (toConv y)
    have hev : ∀ h : WithConv (H →ₐ[k] k), φ (basePointsRepresentation (H := H) E h u) = i := by
      intro h
      have h1 := hi h.ofConv _ rfl
      rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h1
      rw [← hmc]
      exact h1
    intro h
    rw [hev h, ← hev 1, map_one, Module.End.one_apply]

end Fixed

end CFSG.LieType.AlgebraicGroups.ClosedCone
