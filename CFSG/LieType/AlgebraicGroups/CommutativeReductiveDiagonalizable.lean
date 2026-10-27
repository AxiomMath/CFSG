module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Trigonalizable
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Basic
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Naturality
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Character
public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Naturality
public import TauCeti.LinearAlgebra.JordanChevalley.Functoriality
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
public import TauCeti.Algebra.Coalgebra.Subcomodule.Finite
public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Comap
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
public import TauCeti.Algebra.AlgebraicGroup.Connected.GroupScheme
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity
public import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
public import TauCeti.RingTheory.FiniteType.PointSeparation
public import TauCeti.RingTheory.FiniteType.Tensor.Product
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.Algebra.Algebra.Operations
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Basic
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization
public import TauCeti.Algebra.AlgebraicGroup.Smooth.GeometricallyReduced

public noncomputable section

open CategoryTheory TauCeti TauCeti.Comodule WithConv
open scoped TensorProduct

namespace CFSG.LieType.AlgebraicGroups.CommutativeReductive

universe u

section LinearAlgebra

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem eq_of_apply_eq_smul_of_mem_maxGenEigenspace {f : Module.End K V} {μ ν : K} {v : V}
    (hv : v ≠ 0) (hgen : v ∈ f.maxGenEigenspace μ) (hf : f v = ν • v) : ν = μ := by
  by_contra hne
  have hν : v ∈ f.maxGenEigenspace ν :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hf)
  exact hv (Submodule.disjoint_def.mp (Module.End.disjoint_genEigenspace f hne ⊤ ⊤) v hν hgen)

variable [PerfectField K] [FiniteDimensional K V]

theorem unipotentPart_eq_inv_smul_of_isNilpotent (P : LinearMap.GeneralLinearGroup K V) {c : K}
    (hc : c ≠ 0)
    (hn : IsNilpotent ((P : Module.End K V) - algebraMap K (Module.End K V) c)) :
    (LinearMap.GeneralLinearGroup.unipotentPart P : Module.End K V) =
      c⁻¹ • (P : Module.End K V) := by
  let s : LinearMap.GeneralLinearGroup K V :=
    Units.map (algebraMap K (Module.End K V)).toMonoidHom (Units.mk0 c hc)
  have hs : (s : Module.End K V) = algebraMap K (Module.End K V) c := rfl
  have hsinv : ((s⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      algebraMap K (Module.End K V) c⁻¹ := rfl
  let u : LinearMap.GeneralLinearGroup K V := s⁻¹ * P
  have hu : (u : Module.End K V) = c⁻¹ • (P : Module.End K V) := by
    rw [Units.val_mul, hsinv, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hsc : ∀ x : LinearMap.GeneralLinearGroup K V, Commute s x := fun x =>
    Commute.units_of_val (by rw [hs]; exact Algebra.commutes c (x : Module.End K V))
  have hjd : (s, u) = LinearMap.GeneralLinearGroup.jordanDecomposition P := by
    rw [LinearMap.GeneralLinearGroup.eq_jordanDecomposition_iff]
    refine ⟨?_, ?_, hsc u, ?_⟩
    · rw [LinearMap.GeneralLinearGroup.isSemisimple_def, hs, Algebra.algebraMap_eq_smul_one]
      exact Module.End.IsSemisimple_smul c Module.End.isSemisimple_id
    · rw [LinearMap.GeneralLinearGroup.isUnipotent_def, hu]
      have h1 : c⁻¹ • (P : Module.End K V) - 1 =
          c⁻¹ • ((P : Module.End K V) - algebraMap K (Module.End K V) c) := by
        rw [smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h1]
      exact hn.smul c⁻¹
    · simp only [u, mul_inv_cancel_left]
  rw [LinearMap.GeneralLinearGroup.unipotentPart_def, ← hjd, hu]

end LinearAlgebra

section Restriction

variable {R : Type*} {H : Type*} {M : Type*} [CommRing R] [Semiring H] [HopfAlgebra R H]
  [Module.Flat R H] [AddCommMonoid M] [Module R M] [Comodule R H M]

theorem coe_basePointsRepresentation_subcomodule (N : Subcomodule R H M)
    (g : WithConv (H →ₐ[R] R)) (n : N) :
    ((basePointsRepresentation (R := R) (H := H) N g n : N) : M) =
      basePointsRepresentation (R := R) (H := H) M g n := by
  rw [basePointsRepresentation_apply, basePointsRepresentation_apply, endOfPoint_tmul,
    endOfPoint_tmul, one_smul, one_smul, TensorProduct.lid_comm, TensorProduct.lid_comm,
    ← Subcomodule.subtype_rTensor_coact]
  induction Comodule.coact (R := R) (C := H) (M := N) n using TensorProduct.induction_on with
  | zero => simp
  | tmul x c => simp
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

omit [Module.Flat R H] in
theorem basePointsRepresentation_eq_smul_of_coact_eq_tmul (g : WithConv (H →ₐ[R] R)) {v : M}
    {c : H} (h : Comodule.coact (R := R) (C := H) v = v ⊗ₜ[R] c) :
    basePointsRepresentation (R := R) (H := H) M g v = g.ofConv c • v := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, one_smul, TensorProduct.lid_comm, h,
    LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  rfl

end Restriction

section Regular

variable {K : Type*} {B : Type*} [Field K] [CommRing B] [HopfAlgebra K B]

theorem counit_basePointsRepresentation_self (g : WithConv (B →ₐ[K] K)) (b : B) :
    Coalgebra.counit (R := K) (basePointsRepresentation (R := K) (H := B) B g b) =
      g.ofConv b := by
  rw [basePointsRepresentation_apply, endOfPoint_tmul, one_smul, TensorProduct.lid_comm,
    instSelf_coact]
  have h : ∀ x : B ⊗[K] B,
      Coalgebra.counit (R := K)
          (TensorProduct.rid K B (LinearMap.lTensor B g.ofConv.toLinearMap x)) =
        g.ofConv (TensorProduct.lid K B (LinearMap.rTensor B (Coalgebra.counit (R := K)) x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h, Coalgebra.rTensor_counit_comul, TensorProduct.lid_tmul, one_smul]

end Regular

section Jordan

variable {K : Type u} [Field K] [PerfectField K] {B : Type u} [CommRing B] [HopfAlgebra K B]

theorem basePointsRepresentation_unipotentPart_eq_inv_smul (V : Type u) [AddCommGroup V]
    [Module K V] [Comodule K B V] [Module.Finite K V] (g : WithConv (B →ₐ[K] K)) {c : K}
    (hc : c ≠ 0)
    (hn : IsNilpotent (basePointsRepresentation (R := K) (H := B) V g -
      algebraMap K (Module.End K V) c)) :
    basePointsRepresentation (R := K) (H := B) V (HopfAlgebra.Point.unipotentPart K B K g) =
      c⁻¹ • basePointsRepresentation (R := K) (H := B) V g := by
  let M := FGComoduleCat.of (R := K) (C := B) V
  let P := LinearMap.GeneralLinearGroup.ofLinearEquiv (Comodule.pointsAction M g)
  let e := TensorProduct.lid K V
  let Q := LinearMap.GeneralLinearGroup.congrLinearEquiv e P
  have hQ : (Q : Module.End K V) = basePointsRepresentation (R := K) (H := B) V g := by
    ext m
    rw [basePointsRepresentation_apply]
    simp only [Q, P, e, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
      LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearEquiv.trans_apply,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv, TensorProduct.lid_symm_apply]
    exact congrArg (TensorProduct.lid K V)
      (LinearMap.congr_fun (Comodule.pointsAction_toLinearMap M g) _)
  have hQu : (LinearMap.GeneralLinearGroup.unipotentPart Q : Module.End K V) =
      basePointsRepresentation (R := K) (H := B) V (HopfAlgebra.Point.unipotentPart K B K g) := by
    have h1 : LinearMap.GeneralLinearGroup.unipotentPart Q =
        LinearMap.GeneralLinearGroup.congrLinearEquiv e
          (LinearMap.GeneralLinearGroup.unipotentPart P) := by
      simp only [Q]
      rw [LinearMap.GeneralLinearGroup.congrLinearEquiv_apply]
      exact LinearMap.GeneralLinearGroup.unipotentPart_congrLinearEquiv e P
    rw [h1]
    ext m
    rw [basePointsRepresentation_apply]
    simp only [e, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
      LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearEquiv.trans_apply,
      LinearMap.GeneralLinearGroup.coe_toLinearEquiv, TensorProduct.lid_symm_apply]
    exact congrArg (TensorProduct.lid K V)
      (LinearMap.congr_fun (HopfAlgebra.Point.endOfPoint_unipotentPart K B K g M) _).symm
  rw [← hQu, unipotentPart_eq_inv_smul_of_isNilpotent Q hc (hQ ▸ hn), hQ]

end Jordan

section Weights

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B] [IsReduced B] [Coalgebra.IsCocomm K B]
variable {V : Type u} [AddCommGroup V] [Module K V] [Comodule K B V] [FiniteDimensional K V]

def genWeightSpace (χ : WithConv (B →ₐ[K] K) → K) : Submodule K V :=
  ⨅ g, (basePointsRepresentation (R := K) (H := B) V g).maxGenEigenspace (χ g)

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] [FiniteDimensional K V] in
theorem commute_basePointsRepresentation (g h : WithConv (B →ₐ[K] K)) :
    Commute (basePointsRepresentation (R := K) (H := B) V g)
      (basePointsRepresentation (R := K) (H := B) V h) :=
  (Commute.all g h).map _

omit [Algebra.FiniteType K B] [IsReduced B] in
theorem iSup_genWeightSpace : ⨆ χ, genWeightSpace (K := K) (B := B) (V := V) χ = ⊤ :=
  Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute _
    (fun g h _ => commute_basePointsRepresentation g h)
    fun _ => Module.End.iSup_maxGenEigenspace_eq_top _

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] [FiniteDimensional K V] in
theorem basePointsRepresentation_mem_genWeightSpace (χ : WithConv (B →ₐ[K] K) → K)
    (h : WithConv (B →ₐ[K] K)) {v : V} (hv : v ∈ genWeightSpace (B := B) χ) :
    basePointsRepresentation (R := K) (H := B) V h v ∈ genWeightSpace (B := B) χ := by
  simp only [genWeightSpace, Submodule.mem_iInf] at hv ⊢
  exact fun g => Module.End.mapsTo_maxGenEigenspace_of_comm
    (commute_basePointsRepresentation g h) (χ g) (hv g)

def genWeightSubcomodule (χ : WithConv (B →ₐ[K] K) → K) : Subcomodule K B V :=
  Subcomodule.ofEndOfPointStable (K := K) (genWeightSpace (B := B) (V := V) χ) (by
    intro g m hm
    rw [endOfPoint_tmul, one_smul, endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    exact Submodule.tmul_mem_baseChange_of_mem _
      (basePointsRepresentation_mem_genWeightSpace χ (toConv g) hm))

omit [FiniteDimensional K V] in
theorem genWeightSubcomodule_toSubmodule (χ : WithConv (B →ₐ[K] K) → K) :
    (genWeightSubcomodule (B := B) (V := V) χ).toSubmodule = genWeightSpace (B := B) χ :=
  Subcomodule.ofEndOfPointStable_toSubmodule _ _

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] [Coalgebra.IsCocomm K B]
  [FiniteDimensional K V] in
private theorem coe_pow_apply {N : Subcomodule K B V} (φ : Module.End K N)
    (ψ : Module.End K V) (h : ∀ x : N, ((φ x : N) : V) = ψ x) (n : ℕ) (x : N) :
    (((φ ^ n) x : N) : V) = (ψ ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, h, ih]

theorem exists_groupLike_genWeightSpace (χ : WithConv (B →ₐ[K] K) → K) :
    ∃ c : B, IsGroupLikeElem K c ∧ ∀ (g : WithConv (B →ₐ[K] K)) (v : V),
      v ∈ genWeightSpace (B := B) χ →
        basePointsRepresentation (R := K) (H := B) V g v =
          g.ofConv c • basePointsRepresentation (R := K) (H := B) V
            (HopfAlgebra.Point.unipotentPart K B K g) v := by
  classical
  by_cases hbot : genWeightSpace (B := B) (V := V) χ = ⊥
  · refine ⟨1, IsGroupLikeElem.one, fun g v hv => ?_⟩
    rw [hbot, Submodule.mem_bot] at hv
    simp [hv]
  set W := genWeightSubcomodule (B := B) (V := V) χ with hWdef
  have hWsub : W.toSubmodule = genWeightSpace (B := B) (V := V) χ :=
    genWeightSubcomodule_toSubmodule χ
  have hmemW : ∀ v : V, v ∈ W ↔ v ∈ genWeightSpace (B := B) (V := V) χ := fun v => by
    rw [← hWsub]; rfl
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  have : FiniteDimensional K W :=
    FiniteDimensional.of_injective (SMulMemClass.subtype W) fun a b h => Subtype.ext h
  have : Nontrivial W := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    exact ⟨⟨⟨v, (hmemW v).2 hv⟩, 0, fun h => hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨w, c, hw0, hc, hcoact⟩ := hasNonzeroWeightVector_iff.mp
    (hasNonzeroWeightVector_of_isCocomm (k := K) (H := B) (M := W))
  have hwV : (w : V) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hρV : ∀ h : WithConv (B →ₐ[K] K),
      basePointsRepresentation (R := K) (H := B) V h w = h.ofConv c • (w : V) := fun h => by
    rw [← coe_basePointsRepresentation_subcomodule,
      basePointsRepresentation_eq_smul_of_coact_eq_tmul h hcoact]
    rfl
  have hwmem : (w : V) ∈ genWeightSpace (B := B) (V := V) χ := (hmemW w).1 w.2
  have hχ : ∀ h : WithConv (B →ₐ[K] K), h.ofConv c = χ h := fun h => by
    apply eq_of_apply_eq_smul_of_mem_maxGenEigenspace hwV _ (hρV h)
    simp only [genWeightSpace, Submodule.mem_iInf] at hwmem
    exact hwmem h
  have hunit : ∀ g : WithConv (B →ₐ[K] K), g.ofConv c ≠ 0 := fun g =>
    ((hc.isUnit).map g.ofConv).ne_zero
  have hnil : ∀ g : WithConv (B →ₐ[K] K),
      IsNilpotent (basePointsRepresentation (R := K) (H := B) W g -
        algebraMap K (Module.End K W) (χ g)) := by
    intro g
    refine ⟨Module.finrank K V, LinearMap.ext fun x => Subtype.ext ?_⟩
    have hx : (x : V) ∈
        (basePointsRepresentation (R := K) (H := B) V g).maxGenEigenspace (χ g) := by
      have := (hmemW x).1 x.2
      simp only [genWeightSpace, Submodule.mem_iInf] at this
      exact this g
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
      LinearMap.mem_ker] at hx
    have hcoe := coe_pow_apply (N := W) (basePointsRepresentation (R := K) (H := B) W g -
        algebraMap K (Module.End K W) (χ g))
      (basePointsRepresentation (R := K) (H := B) V g - χ g • 1) (fun y => by
        rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
          LinearMap.smul_apply, Module.End.one_apply, ← coe_basePointsRepresentation_subcomodule]
        refine eq_sub_of_add_eq ?_
        rw [← SetLike.val_smul, ← AddMemClass.coe_add, sub_add_cancel])
      (Module.finrank K V) x
    rw [LinearMap.zero_apply, hcoe, hx]
    rfl
  refine ⟨c, hc, fun g v hv => ?_⟩
  have hJ := basePointsRepresentation_unipotentPart_eq_inv_smul (B := B) W g
    ((hχ g) ▸ hunit g) (hnil g)
  have hvW : v ∈ W := (hmemW v).2 hv
  have h1 := coe_basePointsRepresentation_subcomodule W
    (HopfAlgebra.Point.unipotentPart K B K g) ⟨v, hvW⟩
  have h2 := coe_basePointsRepresentation_subcomodule W g ⟨v, hvW⟩
  rw [hJ] at h1
  simp only [LinearMap.smul_apply] at h1
  rw [← h1, ← h2, hχ g]
  simp only [SetLike.val_smul, smul_smul, mul_inv_cancel₀ ((hχ g) ▸ hunit g), one_smul]

end Weights

section Main

variable {K : Type u} [Field K] [IsAlgClosed K] {B : Type u} [CommRing B] [HopfAlgebra K B]
  [Algebra.FiniteType K B]

omit [IsAlgClosed K] in
theorem exists_generating_subcomodule :
    ∃ N : Subcomodule K B B, Module.Finite K N.toSubmodule ∧
      Algebra.adjoin K (N : Set B) = ⊤ := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := K) (A := B)
  obtain ⟨N, hNfin, hsN⟩ :=
    Subcomodule.exists_finite_subcomodule_of_setFinite (R := K) (C := B) (M := B) s.finite_toSet
  refine ⟨N, hNfin, ?_⟩
  rw [eq_top_iff, ← hs]
  exact Algebra.adjoin_mono hsN

abbrev subcomoduleAddCommGroup (N : Subcomodule K B B) : AddCommGroup N :=
  Module.addCommMonoidToAddCommGroup K

attribute [local instance] subcomoduleAddCommGroup

variable [IsReduced B] [Coalgebra.IsCocomm K B]

section Fibers

variable (N : Subcomodule K B B) [FiniteDimensional K N]

omit [IsAlgClosed K] [Algebra.FiniteType K B] [IsReduced B] [Coalgebra.IsCocomm K B]
  [FiniteDimensional K N] in
theorem eval_eq_counit (g : WithConv (B →ₐ[K] K)) (v : N) :
    g.ofConv (v : B) =
      Coalgebra.counit (R := K) ((basePointsRepresentation (R := K) (H := B) N g v : N) : B) := by
  rw [coe_basePointsRepresentation_subcomodule, counit_basePointsRepresentation_self]

theorem exists_groupLike_eval (χ : WithConv (B →ₐ[K] K) → K) :
    ∃ c : B, IsGroupLikeElem K c ∧ ∀ (g : WithConv (B →ₐ[K] K)) (v : N),
      v ∈ genWeightSpace (B := B) (V := N) χ →
        g.ofConv (v : B) =
          g.ofConv c * (HopfAlgebra.Point.unipotentPart K B K g).ofConv (v : B) := by
  obtain ⟨c, hc, hkey⟩ := exists_groupLike_genWeightSpace (B := B) (V := N) χ
  refine ⟨c, hc, fun g v hv => ?_⟩
  rw [eval_eq_counit N g v, hkey g v hv, SetLike.val_smul, map_smul, smul_eq_mul,
    ← eval_eq_counit N]

def wtChar (χ : WithConv (B →ₐ[K] K) → K) : B :=
  Classical.choose (exists_groupLike_eval N χ)

theorem isGroupLikeElem_wtChar (χ : WithConv (B →ₐ[K] K) → K) :
    IsGroupLikeElem K (wtChar N χ) :=
  (Classical.choose_spec (exists_groupLike_eval N χ)).1

theorem eval_eq_wtChar_mul (χ : WithConv (B →ₐ[K] K) → K) (g : WithConv (B →ₐ[K] K)) (v : N)
    (hv : v ∈ genWeightSpace (B := B) (V := N) χ) :
    g.ofConv (v : B) =
      g.ofConv (wtChar N χ) * (HopfAlgebra.Point.unipotentPart K B K g).ofConv (v : B) :=
  (Classical.choose_spec (exists_groupLike_eval N χ)).2 g v hv

theorem eval_wtChar_ne_zero (χ : WithConv (B →ₐ[K] K) → K) (g : WithConv (B →ₐ[K] K)) :
    g.ofConv (wtChar N χ) ≠ 0 :=
  ((isGroupLikeElem_wtChar N χ).isUnit.map g.ofConv).ne_zero

variable {N} (hN : Algebra.adjoin K (N : Set B) = ⊤)
include hN

omit [IsReduced B] [Algebra.FiniteType K B] in
theorem point_eq_of_forall_genWeightSpace {p q : WithConv (B →ₐ[K] K)}
    (h : ∀ (χ : WithConv (B →ₐ[K] K) → K) (v : N), v ∈ genWeightSpace (B := B) (V := N) χ →
      p.ofConv (v : B) = q.ofConv v) : p = q := by
  refine WithConv.ext (AlgHom.ext_of_adjoin_eq_top hN fun x hx => ?_)
  have hv : (⟨x, hx⟩ : N) ∈ ⨆ χ, genWeightSpace (K := K) (B := B) (V := N) χ := by
    rw [iSup_genWeightSpace]; exact Submodule.mem_top
  exact Submodule.iSup_induction _ (motive := fun v : N => p.ofConv (v : B) = q.ofConv (v : B))
    hv (fun χ v hv => h χ v hv) (by simp)
    (fun x y hx hy => by simp only [AddMemClass.coe_add, map_add, hx, hy])

variable (N) in
def jordanFiberIdeal (u : WithConv (B →ₐ[K] K)) : Ideal B :=
  Ideal.span {b | ∃ (χ : WithConv (B →ₐ[K] K) → K) (v : N),
    v ∈ genWeightSpace (B := B) (V := N) χ ∧ b = (v : B) - u.ofConv (v : B) • wtChar N χ}

omit hN in
theorem jordanFiberIdeal_le_ker_iff (hN : Algebra.adjoin K (N : Set B) = ⊤)
    (g u : WithConv (B →ₐ[K] K)) :
    jordanFiberIdeal N u ≤ RingHom.ker g.ofConv ↔
      HopfAlgebra.Point.unipotentPart K B K g = u := by
  constructor
  · intro hle
    refine point_eq_of_forall_genWeightSpace hN fun χ v hv => ?_
    have hmem : (v : B) - u.ofConv (v : B) • wtChar N χ ∈ RingHom.ker g.ofConv :=
      hle (Ideal.subset_span ⟨χ, v, hv, rfl⟩)
    rw [RingHom.mem_ker, map_sub, map_smul, smul_eq_mul, eval_eq_wtChar_mul N χ g v hv,
      sub_eq_zero] at hmem
    exact mul_left_cancel₀ (eval_wtChar_ne_zero N χ g) (hmem.trans (mul_comm _ _))
  · rintro rfl
    rw [jordanFiberIdeal, Ideal.span_le]
    rintro b ⟨χ, v, hv, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_smul, smul_eq_mul,
      eval_eq_wtChar_mul N χ g v hv, mul_comm, sub_self]

theorem unipotentPart_eq_one [ConnectedSpace (PrimeSpectrum B)]
    (hfin : (Set.range (HopfAlgebra.Point.unipotentPart K B K)).Finite)
    (g : WithConv (B →ₐ[K] K)) : HopfAlgebra.Point.unipotentPart K B K g = 1 := by
  classical
  set F := hfin.toFinset.erase 1
  set I₁ := jordanFiberIdeal N 1
  set I' := F.inf (jordanFiberIdeal N)
  have hcover : ∀ h : WithConv (B →ₐ[K] K),
      I₁ ≤ RingHom.ker h.ofConv ∨ I' ≤ RingHom.ker h.ofConv := by
    intro h
    by_cases hu : HopfAlgebra.Point.unipotentPart K B K h = 1
    · exact Or.inl ((jordanFiberIdeal_le_ker_iff hN h 1).mpr hu)
    · refine Or.inr ((Finset.inf_le (Finset.mem_erase.mpr
        ⟨hu, hfin.mem_toFinset.mpr ⟨h, rfl⟩⟩)).trans ?_)
      exact (jordanFiberIdeal_le_ker_iff hN h _).mpr rfl
  have htop : I₁ ⊔ I' = ⊤ := by
    by_contra hne
    have h1 : (1 : B) ∉ (I₁ ⊔ I').radical := fun h =>
      hne (Ideal.radical_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h))
    obtain ⟨f, hf, -⟩ :=
      exists_algHom_apply_ne_zero_of_notMem_radical (k := K) (K := K) (I₁ ⊔ I') h1
    have hI1 : I₁ ≤ RingHom.ker (toConv f).ofConv := le_sup_left.trans hf
    have hI' : I' ≤ RingHom.ker (toConv f).ofConv := le_sup_right.trans hf
    have hu1 := (jordanFiberIdeal_le_ker_iff hN (toConv f) 1).mp hI1
    obtain ⟨w, hw, hwle⟩ := (Ideal.IsPrime.inf_le' (RingHom.ker_isPrime _)).mp hI'
    have hw' := (jordanFiberIdeal_le_ker_iff hN (toConv f) w).mp hwle
    exact (Finset.mem_erase.mp hw).1 (hw'.symm.trans hu1)
  have hzero : ∀ x ∈ I₁ ⊓ I', x = 0 := by
    intro x hx
    apply eq_of_forall_algHom_apply_eq (k := K) (K := K)
    intro f
    rw [map_zero]
    rcases hcover (toConv f) with h | h
    · exact RingHom.mem_ker.mp (h (Ideal.mem_inf.mp hx).1)
    · exact RingHom.mem_ker.mp (h (Ideal.mem_inf.mp hx).2)
  obtain ⟨a, ha, e, he, hae⟩ :=
    Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : B) ∈ I₁ ⊔ I')
  have hidem : IsIdempotentElem e := by
    have hea : e * a = 0 :=
      hzero _ (Ideal.mem_inf.mpr ⟨I₁.mul_mem_left e ha, I'.mul_mem_right a he⟩)
    change e * e = e
    calc e * e = e * (a + e) - e * a := by ring
      _ = e := by rw [hae, mul_one, hea, sub_zero]
  have he1 : e = 1 := by
    rcases eq_zero_or_eq_one_of_isIdempotentElem hidem with h0 | h1
    · exfalso
      have hεa : (1 : WithConv (B →ₐ[K] K)).ofConv a = 0 :=
        RingHom.mem_ker.mp ((jordanFiberIdeal_le_ker_iff hN 1 1).mpr
          (HopfAlgebra.Point.unipotentPart_one K B K) ha)
      have := congrArg (1 : WithConv (B →ₐ[K] K)).ofConv hae
      rw [map_add, hεa, h0, map_zero, map_one, add_zero] at this
      exact zero_ne_one this
    · exact h1
  by_contra hg
  have hI' : I' ≤ RingHom.ker g.ofConv := (hcover g).resolve_left fun h =>
    hg ((jordanFiberIdeal_le_ker_iff hN g 1).mp h)
  have h0 := RingHom.mem_ker.mp (hI' he)
  rw [he1, map_one] at h0
  exact one_ne_zero h0

theorem unipotentPart_eq_self_of_forall_groupLike (p : WithConv (B →ₐ[K] K))
    (hp : ∀ x : GroupLike K B, p.ofConv x = 1) :
    HopfAlgebra.Point.unipotentPart K B K p = p := by
  refine point_eq_of_forall_genWeightSpace hN fun χ v hv => ?_
  have h := eval_eq_wtChar_mul N χ p v hv
  rw [show p.ofConv (wtChar N χ) = 1 from hp ⟨wtChar N χ, isGroupLikeElem_wtChar N χ⟩,
    one_mul] at h
  exact h.symm

theorem span_groupLike_eq_top
    (hall : ∀ g : WithConv (B →ₐ[K] K), HopfAlgebra.Point.unipotentPart K B K g = 1) :
    Submodule.span K (Set.range (GroupLike.val (R := K) (A := B))) = ⊤ := by
  set S := Submodule.span K (Set.range (GroupLike.val (R := K) (A := B)))
  have hmemS : ∀ v : N, (v : B) ∈ S := by
    intro v
    have hv : v ∈ ⨆ χ, genWeightSpace (K := K) (B := B) (V := N) χ := by
      rw [iSup_genWeightSpace]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun v : N => (v : B) ∈ S) hv ?_ (by simp)
      (fun x y hx hy => by rw [AddMemClass.coe_add]; exact S.add_mem hx hy)
    intro χ v hv
    have heq : (v : B) = Coalgebra.counit (R := K) (v : B) • wtChar N χ := by
      apply eq_of_forall_algHom_apply_eq (k := K) (K := K)
      intro f
      have h := eval_eq_wtChar_mul N χ (toConv f) v hv
      rw [hall, AlgHom.convOne_apply] at h
      rw [map_smul, smul_eq_mul]
      simpa [mul_comm] using h
    rw [heq]
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨wtChar N χ, isGroupLikeElem_wtChar N χ⟩, rfl⟩)
  have hone : (1 : B) ∈ S := Submodule.subset_span ⟨1, GroupLike.val_one⟩
  have hmul : ∀ x y : B, x ∈ S → y ∈ S → x * y ∈ S := by
    intro x y hx hy
    have hxy : x * y ∈ S * S := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at hxy
    refine Submodule.span_mono ?_ hxy
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact ⟨a * b, GroupLike.val_mul a b⟩
  have hadj : Algebra.adjoin K (N : Set B) ≤ S.toSubalgebra hone hmul :=
    Algebra.adjoin_le fun x hx => hmemS ⟨x, hx⟩
  rw [hN] at hadj
  rw [eq_top_iff]
  intro x _
  exact hadj (Algebra.mem_top : x ∈ (⊤ : Subalgebra K B))

end Fibers

end Main

section CharacterKernel

variable {K : Type u} [Field K] [IsAlgClosed K]

def characterKernel (B : FiniteTypeCommHopfAlgCat.{u, u} K) : HopfIdeal K B :=
  (HopfIdeal.augmentation K (MonoidAlgebra K (GroupLike K B))).map
    (GroupLike.evaluationBialgHom K B)

omit [IsAlgClosed K] in
theorem characterKernel_le_ker_iff (B : FiniteTypeCommHopfAlgCat.{u, u} K)
    (p : WithConv (B →ₐ[K] K)) :
    (characterKernel B).toIdeal ≤ RingHom.ker p.ofConv ↔
      ∀ x : GroupLike K B, p.ofConv x = 1 := by
  rw [characterKernel, HopfIdeal.map_toIdeal, Ideal.map_le_iff_le_comap]
  constructor
  · intro h x
    have hmem : MonoidAlgebra.single x (1 : K) - 1 ∈
        (HopfIdeal.augmentation K (MonoidAlgebra K (GroupLike K B))).toIdeal := by
      rw [HopfIdeal.mem_toIdeal, HopfIdeal.mem_augmentation]
      simp
    have h1 := h hmem
    rw [Ideal.mem_comap, RingHom.mem_ker] at h1
    simpa [GroupLike.evaluationBialgHom_single, sub_eq_zero] using h1
  · intro h y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hy0 : Coalgebra.counit (R := K) y = 0 :=
      (HopfIdeal.mem_augmentation K _).mp (HopfIdeal.mem_toIdeal.mp hy)
    have key : ∀ z : MonoidAlgebra K (GroupLike K B),
        p.ofConv (GroupLike.evaluationBialgHom K B z) = Coalgebra.counit (R := K) z := by
      intro z
      induction z using MonoidAlgebra.induction_on with
      | of x => simp [GroupLike.evaluationBialgHom_single, h x]
      | add a b ha hb => simp only [map_add, ha, hb]
      | smul r a ha => simp only [map_smul, ha]
    rw [← hy0]
    exact key y

theorem unipotentPart_apply_groupLike {B : Type u} [CommRing B] [HopfAlgebra K B]
    (g : WithConv (B →ₐ[K] K)) (x : GroupLike K B) :
    (HopfAlgebra.Point.unipotentPart K B K g).ofConv x = 1 :=
  HopfAlgebra.IsUnipotentPoint.apply_groupLike_eq_one
    ((HopfAlgebra.isUnipotentPoint_def _).mpr fun M =>
      HopfAlgebra.Point.isUnipotent_pointsAction_unipotentPart K B K g M) x

theorem finite_setOf_forall_groupLike_eq_one (B : FiniteTypeCommHopfAlgCat.{u, u} K)
    [IsReduced B] [Coalgebra.IsCocomm K B]
    (hU : ∀ I : HopfIdeal K B, I.IsNormal →
      geometricallyConnectedCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient B I).obj →
      smoothUnipotentCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient B I) →
      I = HopfIdeal.augmentation K B)
    (hJ : ∀ p : WithConv (B →ₐ[K] K), (∀ x : GroupLike K B, p.ofConv x = 1) →
      HopfAlgebra.Point.unipotentPart K B K p = p) :
    {p : WithConv (B →ₐ[K] K) | ∀ x : GroupLike K B, p.ofConv x = 1}.Finite := by
  let J := characterKernel B
  let Q := FiniteTypeCommHopfAlgCat.quotient B J
  have : IsReduced ((Q ⧸ nilradical Q) ⊗[K] (Q ⧸ nilradical Q)) :=
    instIsReducedTensorProductOfIsAlgClosed K (Q ⧸ nilradical Q) (Q ⧸ nilradical Q)
  let Rd := HopfIdeal.reduction K Q
  let Qr := FiniteTypeCommHopfAlgCat.quotient Q Rd
  let I0 := HopfAlgebra.identityComponentHopfIdeal (k := K) (H := Qr)
  let π : B.obj ⟶ Qr.obj :=
    CommHopfAlgCat.mkQuotient B.obj J ≫ CommHopfAlgCat.mkQuotient Q.obj Rd
  have hπ : Function.Surjective π.hom :=
    (CommHopfAlgCat.mkQuotient_surjective Q.obj Rd).comp
      (CommHopfAlgCat.mkQuotient_surjective B.obj J)
  let Ic := I0.comapOfSurjective π.hom hπ
  have hJIc : ∀ a : B, a ∈ J → a ∈ Ic := by
    intro a ha
    rw [HopfIdeal.mem_comapOfSurjective]
    have h0 : (CommHopfAlgCat.mkQuotient B.obj J).hom a = 0 :=
      (CommHopfAlgCat.mkQuotient_eq_zero_iff B.obj J a).mpr (HopfIdeal.mem_toIdeal.mpr ha)
    change (CommHopfAlgCat.mkQuotient Q.obj Rd).hom ((CommHopfAlgCat.mkQuotient B.obj J).hom a) ∈ I0
    rw [h0, map_zero]
    exact I0.toIdeal.zero_mem
  let eK := CommHopfAlgCat.quotientIsoOfSurjective π hπ I0
  have hcent : (⊥ : HopfIdeal K B).IsCentral :=
    HopfIdeal.isCentral_bot_iff_isCocomm.mpr inferInstance
  have hIcN : Ic.IsNormal := HopfIdeal.IsCentral.isNormal (H := B.obj) (hcent.mono bot_le)
  have hconn : geometricallyConnectedCommHopfAlgProperty K
      (FiniteTypeCommHopfAlgCat.quotient B Ic).obj :=
    (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso eK.symm
      (FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent Qr)
  have : IsReduced Qr := HopfIdeal.isReduced_quotient_reduction K Q
  have : Algebra.Smooth K Qr := (smoothCommHopfAlgProperty_iff Qr.obj).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced K Qr.obj)
  have hzsm : Algebra.Smooth K (FiniteTypeCommHopfAlgCat.identityComponent Qr) :=
    FiniteTypeCommHopfAlgCat.smooth_identityComponent Qr
  have hIsm : Algebra.Smooth K (FiniteTypeCommHopfAlgCat.quotient B Ic) :=
    (smoothCommHopfAlgProperty_iff _).mp
      ((smoothCommHopfAlgProperty K).prop_of_iso eK.symm
        ((smoothCommHopfAlgProperty_iff _).mpr hzsm))
  have hunip : ∀ g : WithConv (FiniteTypeCommHopfAlgCat.quotient B Ic →ₐ[K] AlgebraicClosure K),
      HopfAlgebra.IsUnipotentPoint g := by
    intro g
    let e : K ≃ₐ[K] AlgebraicClosure K := AlgEquiv.ofBijective
      (Algebra.ofId K (AlgebraicClosure K)) IsAlgClosed.algebraMap_bijective_of_isIntegral
    let g₀ : FiniteTypeCommHopfAlgCat.quotient B Ic →ₐ[K] K := e.symm.toAlgHom.comp g.ofConv
    have hg : g = toConv ((e.toAlgHom).comp (toConv g₀).ofConv) := by
      apply WithConv.ext
      ext x
      simp [g₀]
    rw [hg, HopfAlgebra.isUnipotentPoint_toConv_comp_iff]
    let mk : B →ₐc[K] FiniteTypeCommHopfAlgCat.quotient B Ic :=
      (CommHopfAlgCat.mkQuotient B.obj Ic).hom
    have hmk : Function.Surjective mk := CommHopfAlgCat.mkQuotient_surjective B.obj Ic
    let p : WithConv (B →ₐ[K] K) := toConv (g₀.comp (mk : B →ₐ[K] _))
    have hpJ : ∀ x : GroupLike K B, p.ofConv x = 1 := by
      rw [← characterKernel_le_ker_iff]
      intro a ha
      rw [RingHom.mem_ker]
      have h0 : mk a = 0 := (CommHopfAlgCat.mkQuotient_eq_zero_iff B.obj Ic a).mpr
        (HopfIdeal.mem_toIdeal.mpr (hJIc a (HopfIdeal.mem_toIdeal.mp ha)))
      change g₀ (mk a) = 0
      rw [h0, map_zero]
    have hpu := hJ p hpJ
    rw [HopfAlgebra.Point.isUnipotentPoint_iff_unipotentPart_eq_self K _ K]
    have hnat := HopfAlgebra.Point.unipotentPart_toConv_comp mk (toConv g₀)
    apply WithConv.ext
    apply AlgHom.ext
    intro y
    obtain ⟨b, rfl⟩ := hmk y
    have h1 := congrArg (fun q : WithConv (B →ₐ[K] K) => q.ofConv b) (hnat.symm.trans hpu)
    simpa [p] using h1
  have hsu : smoothUnipotentCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient B Ic) :=
    (smoothUnipotentCommHopfAlgProperty_iff K _).mpr ⟨hIsm, hunip⟩
  have hIc := hU Ic hIcN hconn hsu
  have hI0 : I0 = HopfIdeal.augmentation K Qr := by
    apply (HopfIdeal.comapOfSurjective_eq_comapOfSurjective_iff π.hom hπ).mp
    rw [HopfIdeal.comapOfSurjective_augmentation]
    exact hIc
  have : Module.Finite K Qr :=
    FiniteTypeCommHopfAlgCat.moduleFinite_of_identityComponentHopfIdeal_eq_augmentation Qr hI0
  refine (Set.finite_range fun r : Qr →ₐ[K] K =>
    (toConv ((r.comp (Ideal.Quotient.mkₐ K Rd.toIdeal)).comp (Ideal.Quotient.mkₐ K J.toIdeal)) :
      WithConv (B →ₐ[K] K))).subset ?_
  intro p hp
  have hpJ : ∀ a ∈ J.toIdeal, p.ofConv a = 0 := fun a ha =>
    RingHom.mem_ker.mp (((characterKernel_le_ker_iff B p).mpr hp) ha)
  let p₁ : (B ⧸ J.toIdeal) →ₐ[K] K := Ideal.Quotient.liftₐ J.toIdeal p.ofConv hpJ
  have hp₁ : ∀ a ∈ Rd.toIdeal, p₁ a = 0 := by
    intro a ha
    rw [HopfIdeal.reduction_toIdeal] at ha
    exact ((mem_nilradical.mp ha).map p₁).eq_zero
  refine ⟨Ideal.Quotient.liftₐ Rd.toIdeal p₁ hp₁, ?_⟩
  apply WithConv.ext
  ext b
  rfl

end CharacterKernel

section Diagonalizable

attribute [local instance] subcomoduleAddCommGroup

theorem groupLikeSetSpan_eq_top_of_isCocomm {K : Type u} [Field K] [IsAlgClosed K]
    (B : FiniteTypeCommHopfAlgCat.{u, u} K) [IsReduced B] [Coalgebra.IsCocomm K B]
    [ConnectedSpace (PrimeSpectrum B)]
    (hU : ∀ I : HopfIdeal K B, I.IsNormal →
      geometricallyConnectedCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient B I).obj →
      smoothUnipotentCommHopfAlgProperty K (FiniteTypeCommHopfAlgCat.quotient B I) →
      I = HopfIdeal.augmentation K B) :
    Subcoalgebra.groupLikeSetSpan (R := K) (C := B) Set.univ = ⊤ := by
  obtain ⟨N, hNfin, hN⟩ := exists_generating_subcomodule (K := K) (B := B)
  have : FiniteDimensional K N := hNfin
  have hfinJ := finite_setOf_forall_groupLike_eq_one B hU
    (fun p hp => unipotentPart_eq_self_of_forall_groupLike hN p hp)
  have hfin : (Set.range (HopfAlgebra.Point.unipotentPart K B K)).Finite :=
    hfinJ.subset (by
      rintro _ ⟨g, rfl⟩
      exact fun x => unipotentPart_apply_groupLike g x)
  rw [Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top]
  exact span_groupLike_eq_top hN (unipotentPart_eq_one hN hfin)

end Diagonalizable

section Reductive

variable {k : Type u} [Field k]

theorem multiplicativeType_of_reductive_of_isCocomm (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [Coalgebra.IsCocomm k H] (hH : reductiveCommHopfAlgProperty k H) :
    multiplicativeTypeCommHopfAlgProperty k H := by
  rw [multiplicativeTypeCommHopfAlgProperty_iff,
    DiagonalizableGroup.groupLikeSpannedProperty_iff]
  let B := FiniteTypeCommHopfAlgCat.baseChange (K := AlgebraicClosure k) H
  have : Coalgebra.IsCocomm (AlgebraicClosure k) B :=
    inferInstanceAs (Coalgebra.IsCocomm (AlgebraicClosure k)
      (TensorProduct k (AlgebraicClosure k) H))
  have : Algebra.Smooth (AlgebraicClosure k) B :=
    @Algebra.Smooth.baseChange k _ H (AlgebraicClosure k) _ _ _ _ hH.smooth
  have : IsReduced B :=
    (smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed (AlgebraicClosure k) B.obj).mp
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)
  have : ConnectedSpace (PrimeSpectrum B) :=
    hH.geometricallyConnected.connectedSpace_algebraicClosureBaseChange
  exact groupLikeSetSpan_eq_top_of_isCocomm B fun I hI hc hu => hH.eq_augmentation I hI hc hu

end Reductive

end CFSG.LieType.AlgebraicGroups.CommutativeReductive
