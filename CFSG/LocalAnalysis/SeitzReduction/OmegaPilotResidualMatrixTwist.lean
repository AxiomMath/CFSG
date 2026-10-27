module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldExtension
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityOrthCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualField

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (unitMultiplierPairs)
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)
open LinearPilot (autFixSubgroup mem_autFixSubgroup)

section Semilinear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem semilinear_eichler_conj {σ : K ≃+* K} {T : V ≃+ V}
    (hT : ∀ (a : K) x, T (a • x) = σ a • T x) (hTQ : ∀ x, Q (T x) = σ (Q x)) (u w x : V) :
    T (eichler Q u w (T.symm x)) = eichler Q (T u) (T w) x := by
  have hpol : ∀ a b, polar Q (T a) (T b) = σ (polar Q a b) := fun a b => by
    have := polar_map_of_semisim (Q := Q) (φ := T) (σ := σ) (μ := 1)
      (fun y => by rw [hTQ, one_mul]) a b
    rwa [one_mul] at this
  have hx : ∀ y, σ (polar Q (T.symm x) y) = polar Q x (T y) := fun y => by
    rw [← hpol, AddEquiv.apply_symm_apply]
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hu : Q (T u) = 0 := by rw [hTQ, h.1, map_zero]
    have hw : polar Q (T u) (T w) = 0 := by rw [hpol, h.2, map_zero]
    rw [eichler_apply h.1 h.2, eichler_apply hu hw, map_sub, map_add, hT, hT,
      AddEquiv.apply_symm_apply, hx, map_add, map_mul, hx, hx, ← hTQ]
  · have h' : ¬(Q (T u) = 0 ∧ polar Q (T u) (T w) = 0) := by
      rwa [hTQ, hpol, map_eq_zero_iff σ σ.injective, map_eq_zero_iff σ σ.injective]
    rw [eichler_of_not h, eichler_of_not h']
    exact AddEquiv.apply_symm_apply T x

end Semilinear

section Descent

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {σ : K ≃+* K}
  {T : V →ₛₗ[(σ : K →+* K)] V} {Q : QuadraticForm K V} (hTQ : ∀ v, Q (T v) = σ (Q v))

theorem coe_eichler_descentForm {x y : fixSpace T} (hx : descentForm hTQ x = 0)
    (hxy : polar (descentForm hTQ) x y = 0) (z : fixSpace T) :
    ((eichler (descentForm hTQ) x y z : fixSpace T) : V) = eichler Q (x : V) (y : V) (z : V) := by
  have hx' : Q (x : V) = 0 := by rw [← coe_descentForm hTQ, hx]; rfl
  have hxy' : polar Q (x : V) (y : V) = 0 := by
    rw [← CFSG.ComponentClassification.UnbalancedCatalog.coe_polar_descentForm hTQ, hxy]; rfl
  rw [eichler_apply hx hxy, eichler_apply hx' hxy']
  simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Subfield.smul_def,
    Subfield.coe_add, Subfield.coe_mul, CFSG.ComponentClassification.UnbalancedCatalog.coe_polar_descentForm, coe_descentForm]

end Descent

section Coordinates

variable {K : Type*} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem kappa_projHom (S : similarityPairs Q) (E E' : orthDerived Q)
    (h : ∀ x, (E' : (Fin d → K) ≃ₗ[K] (Fin d → K)) x =
      coordinateSemilinearMap S.val ((E : (Fin d → K) ≃ₗ[K] (Fin d → K))
        ((coordinateSemilinearMap S.val).symm x))) :
    matrixProjectiveConjugationHom Q S (projHom Q E) = projHom Q E' := by
  change matrixProjectiveConjugation Q S
      (matrixProjectiveProjection Q ((derivedEquiv Q).symm E)) =
    matrixProjectiveProjection Q ((derivedEquiv Q).symm E')
  rw [matrixProjectiveConjugation_mk]
  congr 1
  apply (derivedEquiv Q).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_derivedEquiv]
  apply LinearEquiv.ext
  intro x
  rw [h]
  have hy := congrArg (fun F : orthDerived Q => (F : (Fin d → K) ≃ₗ[K] (Fin d → K)))
    ((derivedEquiv Q).apply_symm_apply E)
  simp only [coe_derivedEquiv] at hy
  change matrixLinearEquiv (matrixConjugation S.val ((derivedEquiv Q).symm E).val) x = _
  rw [matrixConjugation_vector, ← hy]
  rfl

end Coordinates

section Image

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {S : similarityPairs Q}
  {hS : S ∈ unitMultiplierPairs Q}
  (e : ↥(pairCentralizer S) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)))

@[expose] noncomputable def descentIsometry :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)) →*
      ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (Subgroup.inclusion inf_le_left).comp e.symm.toMonoidHom

theorem descentIsometry_mem_orthDerived
    {g : TauCeti.QuadraticMap.orthogonalGroup (pairDescentForm hS)}
    (hg : (g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) ∈ pairDescentDerived hS) :
    ((descentIsometry e g : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ orthDerived Q :=
  mem_commutator_subtype_iff.mp (map_mem_commutator (descentIsometry e)
    (mem_commutator_subtype_iff.mpr hg))

@[expose] noncomputable def descentDerivedExt : ↥(pairDescentDerived hS) →* orthDerived Q :=
  (((TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp (descentIsometry e)).comp
    (Subgroup.inclusion (Subgroup.commutator_le_self _))).codRestrict (orthDerived Q)
      fun g => descentIsometry_mem_orthDerived e g.2

@[expose] noncomputable def descentImage : Subgroup (matrixProjectiveDerived Q) :=
  ((projHom Q).comp (descentDerivedExt e)).range

theorem kappa_descentImage {x : matrixProjectiveDerived Q} (hx : x ∈ descentImage e) :
    matrixProjectiveConjugationHom Q S x = x := by
  obtain ⟨g, rfl⟩ := hx
  refine kappa_projHom S _ _ fun v => ?_
  have h1 := (e.symm (Subgroup.inclusion (Subgroup.commutator_le_self _) g)).2.2
    ((coordinateSemilinearMap S.val).symm v)
  change _ = coordinateSemilinearMap S.val
    (((e.symm (Subgroup.inclusion (Subgroup.commutator_le_self _) g) : pairCentralizer S) :
      (Fin d → K) ≃ₗ[K] (Fin d → K)) ((coordinateSemilinearMap S.val).symm v))
  rw [← pairSemilinearMap_apply, ← h1, pairSemilinearMap_apply, AddEquiv.apply_symm_apply]
  rfl

theorem descentImage_le_autFixSubgroup :
    descentImage e ≤ autFixSubgroup (matrixProjectiveConjugationHom Q S) := fun _ hx =>
  mem_autFixSubgroup.mpr (kappa_descentImage e hx)

theorem commutator_descentImage (hJ : commutator ↥(pairDescentDerived hS) = ⊤) :
    ⁅descentImage e, descentImage e⁆ = descentImage e := by
  rw [descentImage, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hJ]

theorem descentImage_le_perfectCore (hJ : commutator ↥(pairDescentDerived hS) = ⊤) :
    descentImage e ≤ perfectCore (autFixSubgroup (matrixProjectiveConjugationHom Q S)) :=
  le_perfectCore_of_perfect (descentImage_le_autFixSubgroup e) (commutator_descentImage e hJ)

theorem coe_descentDerivedExt_eichler
    (he : ∀ g w, (((e g : pairFix S ≃ₗ[descentField S.val.right] pairFix S) w : pairFix S) :
      Fin d → K) = (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) w)
    (hspan : Submodule.span K (pairFix S : Set (Fin d → K)) = ⊤)
    {x y : pairFix S} (hx : pairDescentForm hS x = 0) (hxy : polar (pairDescentForm hS) x y = 0)
    (hE : eichler (pairDescentForm hS) x y ∈ pairDescentDerived hS) :
    ((descentDerivedExt e ⟨_, hE⟩ : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) =
      eichler Q (x : Fin d → K) (y : Fin d → K) := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.ext_on hspan fun z hz => ?_
  have h1 := he (e.symm ⟨eichler (pairDescentForm hS) x y, Subgroup.commutator_le_self _ hE⟩)
    ⟨z, hz⟩
  rw [MulEquiv.apply_symm_apply] at h1
  change ((e.symm ⟨eichler (pairDescentForm hS) x y, Subgroup.commutator_le_self _ hE⟩ :
    pairCentralizer S) : (Fin d → K) ≃ₗ[K] (Fin d → K)) z = eichler Q (x : Fin d → K) y z
  rw [← h1]
  exact coe_eichler_descentForm (pairSemilinearMap_quad hS) hx hxy ⟨z, hz⟩

end Image

section Plus

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

theorem exists_fieldPair_plus (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα2 : α ^ 2 = 1)
    (hfp : plusFieldPart (LinearPilot.one_le_of_card_eq_two_pow hK) hK hn α ≠ 1) :
    ∃ S : similarityPairs (coordinateQuadPlus n K), S ∈ unitMultiplierPairs _ ∧
      matrixProjectiveConjugationHom _ S = α ∧ S.val.right * S.val.right = 1 ∧
      S.val.right ≠ 1 ∧
      ∀ v, coordinateSemilinearMap S.val (coordinateSemilinearMap S.val v) = v := by
  have hf := LinearPilot.one_le_of_card_eq_two_pow hK
  have hαE : α ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [plusImage_eq_top hn]
    exact Subgroup.mem_top α
  obtain ⟨S, hS, rfl⟩ := exists_unit_rep hαE
  have hσ : plusFieldPart hf hK hn (matrixProjectiveConjugationHom _ S) = S.val.right :=
    orthAutFieldPart_kappa _ _ S
  rw [hσ] at hfp
  have hα1 : matrixProjectiveConjugationHom _ S ≠ 1 := fun h => hfp (by
    rw [← hσ, h, map_one])
  have hord : orderOf (matrixProjectiveConjugationHom _ S) = 2 := orderOf_eq_prime hα2 hα1
  obtain ⟨-, -, -, -, -, -, -, -, hinv⟩ := plusRealization hf hK (n := n) (by omega)
  obtain ⟨hSS, hTT, -⟩ := hinv _ ⟨S, rfl⟩ hord S hS rfl
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus n K) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  exact ⟨S, hS, rfl, hσσ, hfp, hTT⟩

end Plus

end CFSG.SeitzReduction.OmegaPilot
