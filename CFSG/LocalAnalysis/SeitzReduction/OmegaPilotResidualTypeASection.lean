module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeABlock
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeAFix

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module QuadraticMap CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n ℓ m : ℕ} (P : LowPairing n ℓ)

omit [Finite K] in
theorem projLift_mem_lowSpan_of_mem_core (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)} (hx : x ∈ typeACore K P)
    {v : Fin (2 * n) → K} (hv : v ∈ lowSpan K n ℓ) : projLift hQ x v ∈ lowSpan K n ℓ := by
  rw [← range_lowNil P] at hv ⊢
  exact mem_range_of_commute (g := (projLift hQ x : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)))
    (projLift_lowNil_of_mem_core hQ hx) v hv

omit [Finite K] in
theorem projLift_mem_lowPerp_of_mem_core (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)} (hx : x ∈ typeACore K P)
    {v : Fin (2 * n) → K} (hv : v ∈ lowPerp K n ℓ) : projLift hQ x v ∈ lowPerp K n ℓ := by
  rw [← ker_lowNil P] at hv ⊢
  exact mem_ker_of_commute (g := (projLift hQ x : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)))
    (projLift_lowNil_of_mem_core hQ hx) v hv

omit [Finite K] in
theorem kerQuotHom_eq_one_iff_forall {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (hQ : ∃ v, Q v ≠ 0)
    {X : Subgroup (matrixProjectiveDerived Q)} (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v)) (x : ↥X) :
    kerQuotHom hQ X N hXN x = 1 ↔ ∀ v ∈ LinearMap.ker N,
      projLift hQ (x : matrixProjectiveDerived Q) v - v ∈ LinearMap.range N := by
  refine ⟨fun h1 v hv => ?_, kerQuotHom_eq_one_of hQ N hXN x⟩
  have h := congrArg (fun f : Module.End K (LinearMap.ker N ⧸ rangeInKer N) =>
    f (Submodule.Quotient.mk ⟨v, hv⟩)) h1
  change kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk ⟨v, hv⟩) =
    Submodule.Quotient.mk ⟨v, hv⟩ at h
  rw [kerQuotMap_mk'] at h
  have h' := (Submodule.Quotient.eq _).mp h
  simpa [rangeInKer] using h'

omit [Finite K] in
theorem kerQuotHom_eq_one_iff (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0) (x : typeACore K P) :
    kerQuotHom hQ (typeACore K P) (lowNil P) (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x =
      1 ↔ ∀ v ∈ lowPerp K n ℓ,
        projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) v - v ∈
          lowSpan K n ℓ := by
  rw [kerQuotHom_eq_one_iff_forall, ker_lowNil, range_lowNil]

variable (h : ℓ + m = n) (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)

omit [Finite K] in
theorem blockPart_projLift_comp {x y : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ typeACore K P) (hy : y ∈ typeACore K P) :
    blockPart h ((projLift hQ x : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) ∘ₗ
      (projLift hQ y : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K))) =
        blockPart h (projLift hQ x) ∘ₗ blockPart h (projLift hQ y) :=
  blockPart_comp h (fun _ hv => projLift_mem_lowSpan_of_mem_core P hQ hx hv)
    fun _ hv => projLift_mem_lowPerp_of_mem_core P hQ hy hv

omit [Finite K] in
theorem blockPart_projLift_mul {x y : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ typeACore K P) (hy : y ∈ typeACore K P) :
    blockPart h (projLift hQ (x * y) : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) =
      blockPart h (projLift hQ x) ∘ₗ blockPart h (projLift hQ y) := by
  rw [← blockPart_projLift_comp P h hQ hx hy, projLift_mul]
  rfl

omit [Finite K] in
theorem blockPart_projLift_one :
    blockPart h (projLift hQ (1 : matrixProjectiveDerived (coordinateQuadPlus n K)) :
      (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) = LinearMap.id := by
  rw [projLift_one']
  exact blockPart_id h

@[expose] noncomputable def coreBlockEquiv (x : typeACore K P) :
    (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K) :=
  LinearEquiv.ofLinearMap (blockPart h (projLift hQ (x : matrixProjectiveDerived _)))
    (blockPart h (projLift hQ ((x⁻¹ : typeACore K P) : matrixProjectiveDerived _)))
    (by rw [← blockPart_projLift_mul P h hQ x.2 (x⁻¹).2, Subgroup.coe_inv, mul_inv_cancel,
      blockPart_projLift_one])
    (by rw [← blockPart_projLift_mul P h hQ (x⁻¹).2 x.2, Subgroup.coe_inv, inv_mul_cancel,
      blockPart_projLift_one])

omit [Finite K] in
theorem coreBlockEquiv_toLinearMap (x : typeACore K P) :
    (coreBlockEquiv P h hQ x).toLinearMap =
      blockPart h (projLift hQ (x : matrixProjectiveDerived _)) :=
  rfl

@[expose] noncomputable def coreBlockHom :
    typeACore K P →* ((Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) where
  toFun x := coreBlockEquiv P h hQ x
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    rw [coreBlockEquiv_toLinearMap, Subgroup.coe_one, blockPart_projLift_one]
    rfl
  map_mul' x y := by
    apply LinearEquiv.toLinearMap_injective
    rw [coreBlockEquiv_toLinearMap, Subgroup.coe_mul, blockPart_projLift_mul P h hQ x.2 y.2]
    rfl

omit [Finite K] in
theorem coreBlockHom_toLinearMap (x : typeACore K P) :
    (coreBlockHom P h hQ x).toLinearMap =
      blockPart h (projLift hQ (x : matrixProjectiveDerived _)) :=
  rfl

omit [Finite K] in
theorem coreBlockHom_eq_one_iff (x : typeACore K P) :
    coreBlockHom P h hQ x = 1 ↔
      kerQuotHom hQ (typeACore K P) (lowNil P)
        (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v) x = 1 := by
  rw [kerQuotHom_eq_one_iff]
  refine Iff.trans ?_ (blockPart_eq_id_iff h
    (g := (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) :
      (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)))
    (fun _ hv => projLift_mem_lowSpan_of_mem_core P hQ x.2 hv)
    (fun _ hv => projLift_mem_lowPerp_of_mem_core P hQ x.2 hv))
  rw [← coreBlockHom_toLinearMap]
  constructor
  · intro h1
    rw [h1]
    rfl
  · intro h1
    apply LinearEquiv.toLinearMap_injective
    rw [h1]
    rfl

omit [Finite K] in
theorem coreBlockHom_ker :
    (coreBlockHom P h hQ).ker = (kerQuotHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  exact coreBlockHom_eq_one_iff P h hQ x

omit [Finite K] in
theorem coordinateQuadPlus_projLift (x : matrixProjectiveDerived (coordinateQuadPlus n K))
    (v : Fin (2 * n) → K) : coordinateQuadPlus n K (projLift hQ x v) = coordinateQuadPlus n K v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
    (Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ x)) v

omit [Finite K] in
theorem coreBlockHom_mem_orthogonalGroup (x : typeACore K P) :
    coreBlockHom P h hQ x ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  change coordinateQuadPlus m K (blockPart h (projLift hQ (x : matrixProjectiveDerived _) :
    (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) w) = _
  exact coordinateQuadPlus_blockPart h (fun v => coordinateQuadPlus_projLift hQ _ v)
    (fun _ hv => projLift_mem_lowPerp_of_mem_core P hQ x.2 hv) w

theorem isPerfect_typeACore : Group.IsPerfect (typeACore K P) :=
  Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)

theorem range_coreBlockHom_le :
    (coreBlockHom P h hQ).range ≤ orthDerived (coordinateQuadPlus m K) := by
  have := isPerfect_typeACore (K := K) P
  rw [← Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (coreBlockHom P h hQ))]
  have hO : (coreBlockHom P h hQ).range ≤
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus m K) := by
    rintro _ ⟨x, rfl⟩
    exact coreBlockHom_mem_orthogonalGroup P h hQ x
  exact Subgroup.commutator_mono hO hO

omit [Finite K] [CharP K 2] in
theorem blockExtend_lowNil (g : (Fin (2 * m) → K) ≃ₗ[K] (Fin (2 * m) → K)) (v : Fin (2 * n) → K) :
    blockExtend h g (lowNil P v) = lowNil P (blockExtend h g v) := by
  rw [blockExtend_apply_of_mem_lowSpan h g (lowNil_mem_lowSpan P v)]
  refine ext_plus (fun i => ?_) fun i => by rw [lowNil_inr, lowNil_inr]
  rw [lowNil_inl, lowNil_inl]
  split_ifs with hi
  · rw [blockExtend_apply_inr h g v ((P.lt_iff i).mpr hi)]
  · rfl

@[expose] noncomputable def blockLeviP :
    orthDerived (coordinateQuadPlus m K) →* matrixProjectiveDerived (coordinateQuadPlus n K) :=
  (projHom _).comp
    (((blockExtend h).comp (orthDerived (coordinateQuadPlus m K)).subtype).codRestrict
      _ fun g => map_orthDerived_blockExtend_le h ⟨g, g.2, rfl⟩)

omit [Finite K] in
theorem projLift_blockLeviP (g : orthDerived (coordinateQuadPlus m K)) :
    projLift hQ (blockLeviP h g) = blockExtend h g :=
  projLift_projHom hQ _

include hQ in
theorem range_blockLeviP_le (hm : 3 ≤ m) : (blockLeviP (K := K) h).range ≤ typeACore K P := by
  have : Group.IsPerfect (orthDerived (coordinateQuadPlus m K)) :=
    Subgroup.isPerfect_iff.mpr (commutator_orthDerived_coordinateQuadPlus hm)
  refine le_perfectCore_of_perfect ?_
    (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (blockLeviP (K := K) h)))
  rintro _ ⟨g, rfl⟩
  refine mem_autFixSubgroup_of_commute hQ (lowRep P) fun v => ?_
  rw [projLift_blockLeviP h hQ]
  change blockExtend h g (matrixLinearEquiv (lowRepGL P) v) =
    matrixLinearEquiv (lowRepGL P) (blockExtend h g v)
  rw [matrixLinearEquiv_lowRepGL, matrixLinearEquiv_lowRepGL, map_add, blockExtend_lowNil]

theorem exists_coreBlockHom_eq (hm : 3 ≤ m) (g : orthDerived (coordinateQuadPlus m K)) :
    ∃ x : typeACore K P, coreBlockHom P h hQ x = g := by
  refine ⟨⟨blockLeviP h g, range_blockLeviP_le P h hQ hm ⟨g, rfl⟩⟩, ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [coreBlockHom_toLinearMap]
  change blockPart h (projLift hQ (blockLeviP h g) : (Fin (2 * n) → K) →ₗ[K] (Fin (2 * n) → K)) = _
  rw [projLift_blockLeviP h hQ, blockPart_blockExtend]

@[expose] noncomputable def coreSectionHom :
    typeACore K P →* orthDerived (coordinateQuadPlus m K) :=
  (coreBlockHom P h hQ).codRestrict _ fun x => range_coreBlockHom_le P h hQ ⟨x, rfl⟩

theorem coreSectionHom_surjective (hm : 3 ≤ m) : Function.Surjective (coreSectionHom P h hQ) := by
  intro g
  obtain ⟨x, hx⟩ := exists_coreBlockHom_eq P h hQ hm g
  exact ⟨x, Subtype.ext hx⟩

theorem coreSectionHom_ker :
    (coreSectionHom P h hQ).ker = (kerQuotHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker := by
  rw [coreSectionHom, MonoidHom.ker_codRestrict, coreBlockHom_ker]

@[expose] noncomputable def coreSectionEquiv (hm : 3 ≤ m) :
    typeACore K P ⧸ (kerQuotHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker ≃*
        orthDerived (coordinateQuadPlus m K) :=
  (QuotientGroup.quotientMulEquivOfEq (coreSectionHom_ker P h hQ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (coreSectionHom_surjective P h hQ hm))

theorem kerQuotHom_ker_eq_top_of_one (h₁ : ℓ + 1 = n) :
    (kerQuotHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker = ⊤ := by
  have := isPerfect_typeACore (K := K) P
  have hrange : (coreBlockHom P h₁ hQ).range = ⊥ := by
    refine eq_bot_of_commutator_eq_self_of_le_orthogonalGroup_one ?_
      (Subgroup.isPerfect_iff.mp (Group.IsPerfect.range (coreBlockHom P h₁ hQ)))
    rintro _ ⟨x, rfl⟩
    exact coreBlockHom_mem_orthogonalGroup P h₁ hQ x
  rw [← coreBlockHom_ker P h₁ hQ, eq_top_iff]
  intro x _
  rw [MonoidHom.mem_ker]
  have hx : coreBlockHom P h₁ hQ x ∈ (coreBlockHom P h₁ hQ).range := ⟨x, rfl⟩
  rwa [hrange, Subgroup.mem_bot] at hx

omit [Finite K] in
theorem kerQuotHom_ker_eq_top_of_eq (hℓ : ℓ = n) :
    (kerQuotHom hQ (typeACore K P) (lowNil P)
      (fun _ hx v => projLift_lowNil_of_mem_core hQ hx v)).ker = ⊤ := by
  refine eq_top_iff.mpr fun x _ => MonoidHom.mem_ker.mpr
    ((kerQuotHom_eq_one_iff P hQ x).mpr fun v hv => ?_)
  have hvS : v ∈ lowSpan K n ℓ := fun i => ⟨hv i (by omega), fun hi => absurd hi (by omega)⟩
  exact sub_mem (projLift_mem_lowSpan_of_mem_core P hQ x.2 hvS) hvS

end CFSG.SeitzReduction.OmegaPilot
