module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusRes

public section

namespace CFSG.AGLEmbedding.LeviBlock

open QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r t : ℕ}

@[expose] def orthResExt (ht : t ≤ r) (B : Module.End K ((Fin (r - t) ⊕ Fin (r - t) → K) × A)) :
    Module.End K ((Fin r ⊕ Fin r → K) × A) :=
  1 + (orthResIncl K A ht).comp ((B - 1).comp (orthResProj K A ht))

theorem orthResExt_apply (ht : t ≤ r) (B : Module.End K ((Fin (r - t) ⊕ Fin (r - t) → K) × A))
    (v : (Fin r ⊕ Fin r → K) × A) :
    orthResExt ht B v =
      v + orthResIncl K A ht (B (orthResProj K A ht v) - orthResProj K A ht v) :=
  rfl

theorem orthResProj_orthResExt (ht : t ≤ r)
    (B : Module.End K ((Fin (r - t) ⊕ Fin (r - t) → K) × A)) (v : (Fin r ⊕ Fin r → K) × A) :
    orthResProj K A ht (orthResExt ht B v) = B (orthResProj K A ht v) := by
  rw [orthResExt_apply, map_add, orthResProj_orthResIncl, add_sub_cancel]

variable (K A) in
@[expose] def orthResExtHom (ht : t ≤ r) :
    Module.End K ((Fin (r - t) ⊕ Fin (r - t) → K) × A) →* Module.End K ((Fin r ⊕ Fin r → K) × A)
    where
  toFun := orthResExt ht
  map_one' := LinearMap.ext fun v => by rw [orthResExt_apply]; simp
  map_mul' B C := LinearMap.ext fun v => by
    rw [Module.End.mul_apply, orthResExt_apply, orthResExt_apply (v := v),
      orthResExt_apply (v := v + _), map_add, orthResProj_orthResIncl, Module.End.mul_apply]
    rw [add_sub_cancel, add_assoc, ← map_add]
    congr 2
    abel

variable (K A) in
@[expose] noncomputable def orthLeviRes (ht : t ≤ r) :
    (((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A)) →*
      (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).toMonoidHom.comp
    ((Units.map (orthResExtHom K A ht)).comp
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K _).symm.toMonoidHom)

theorem orthLeviRes_apply (ht : t ≤ r)
    (B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A))
    (v : (Fin r ⊕ Fin r → K) × A) :
    orthLeviRes K A ht B v = orthResExt ht (B : Module.End K _) v :=
  rfl

theorem orthLeviRes_apply_of_mem (ht : t ≤ r)
    (B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A))
    {v : (Fin r ⊕ Fin r → K) × A} (hv : v ∈ tailFlag K A r t) : orthLeviRes K A ht B v = v := by
  rw [orthLeviRes_apply, orthResExt_apply, orthResProj_eq_zero_of_mem ht hv, map_zero, sub_zero,
    map_zero, add_zero]

theorem orthLeviRes_mem_orthogonalGroup {qA : QuadraticForm K A} (ht : t ≤ r)
    {B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A)}
    (hB : B ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail (r - t) qA)) :
    orthLeviRes K A ht B ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  have hlow : ∀ (c : Fin r → Fin r ⊕ Fin r) (hc : ∀ p, c p = .inl p ∨ c p = .inr p) (i : Fin t),
      (orthLeviRes K A ht B v).1 (c (splitIdx ht (.inl i))) = v.1 (c (splitIdx ht (.inl i))) := by
    intro c hc i
    rw [orthLeviRes_apply, orthResExt_apply, Prod.fst_add, Pi.add_apply, add_eq_left]
    rcases hc (splitIdx ht (.inl i)) with h | h <;> rw [h] <;> simp [orthResIncl_apply, joinHi]
  rw [quadTail_eq_add_highPart ht, quadTail_eq_add_highPart ht (v := v)]
  have h2 : (hiPart ht (orthLeviRes K A ht B v).1, (orthLeviRes K A ht B v).2) =
      B (orthResProj K A ht v) := by
    rw [← orthResProj_apply, orthLeviRes_apply, orthResProj_orthResExt]
    rfl
  rw [h2, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hB]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hlow _ (fun p => Or.inl rfl) i, hlow _ (fun p => Or.inr rfl) i]

theorem orthLeviRes_mem_commutator {qA : QuadraticForm K A} (ht : t ≤ r)
    {B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A)}
    (hB : B ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail (r - t) qA),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail (r - t) qA)⁆) :
    orthLeviRes K A ht B ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA)⁆ := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (quadTail (r - t) qA)).map
      (orthLeviRes K A ht) ≤ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) := by
    rintro _ ⟨C, hC, rfl⟩
    exact orthLeviRes_mem_orthogonalGroup ht hC
  have h := Subgroup.mem_map_of_mem (orthLeviRes K A ht) hB
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hle hle h

theorem orthResMat_orthLeviRes (ht : t ≤ r)
    (B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A)) :
    orthResMat ht (orthLeviRes K A ht B) = (B : Module.End K _) :=
  LinearMap.ext fun u => by
    rw [orthResMat_apply, orthLeviRes_apply, orthResProj_orthResExt, orthResProj_orthResIncl]

theorem orthCoefMat_orthLeviRes_apply (ht : t ≤ r)
    (B : ((Fin (r - t) ⊕ Fin (r - t) → K) × A) ≃ₗ[K] ((Fin (r - t) ⊕ Fin (r - t) → K) × A))
    (i : Fin r) {j : Fin r} (hj : (j : ℕ) < t) :
    orthCoefMat (orthLeviRes K A ht B) i j = (1 : Matrix (Fin r) (Fin r) K) i j := by
  rw [orthCoefMat_apply, orthLeviRes_apply_of_mem ht B (orthHypVec_mem_tailFlag hj)]
  simp [hypVec, Pi.single_apply, Matrix.one_apply]

end CFSG.AGLEmbedding.LeviBlock
