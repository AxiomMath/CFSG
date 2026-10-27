module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedNormal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed

open CatalogueBOrthogonalScalarSquare

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem polar_similarity (Q : QuadraticForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) (x y : V) :
    Q.polarBilin (A x) (A y) = (μ : K) * Q.polarBilin x y := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  rw [← A.map_add, hsim, hsim, hsim]
  ring

theorem inverse_quadratic_similarity (Q : QuadraticForm K V) (A : V ≃ₗ[K] V) (μ : Kˣ)
    (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) (x : V) :
    Q (A.symm x) = (↑μ⁻¹ : K) * Q x := by
  have h := hsim (A.symm x)
  rw [A.apply_symm_apply] at h
  calc
    Q (A.symm x) = (↑μ⁻¹ : K) * ((μ : K) * Q (A.symm x)) := by simp
    _ = (↑μ⁻¹ : K) * Q x := by rw [h]

theorem similarity_conjugation_preserves (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    A * g.val * A⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  apply TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
  intro x
  change Q (A (g.val (A.symm x))) = Q x
  rw [hsim, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.property,
    inverse_quadratic_similarity Q A μ hsim]
  simp

@[expose] def similarityConjugation (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) :
    MulAut (TauCeti.QuadraticMap.orthogonalGroup Q) where
  toFun g := ⟨A * g.val * A⁻¹, similarity_conjugation_preserves Q A μ hsim g⟩
  invFun g := ⟨A⁻¹ * g.val * A, by
    simpa using similarity_conjugation_preserves Q A.symm μ⁻¹
      (inverse_quadratic_similarity Q A μ hsim) g⟩
  left_inv g := by apply Subtype.ext; change A⁻¹ * (A * g.val * A⁻¹) * A = g.val; group
  right_inv g := by apply Subtype.ext; change A * (A⁻¹ * g.val * A) * A⁻¹ = g.val; group
  map_mul' g h := by
    apply Subtype.ext
    change A * (g.val * h.val) * A⁻¹ = (A * g.val * A⁻¹) * (A * h.val * A⁻¹)
    group

theorem similarityConjugation_val (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    (similarityConjugation Q A μ hsim g).val = A * g.val * A⁻¹ := rfl

theorem similarityConjugation_symm_val (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    ((similarityConjugation Q A μ hsim).symm g).val = A⁻¹ * g.val * A := rfl

theorem fixed_similarityConjugation_eq (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) :
    FixedCommutingProduct.fixedSubgroup (similarityConjugation Q A μ hsim) =
      orthogonalOperatorCentralizer Q A.toLinearMap := by
  ext g
  change similarityConjugation Q A μ hsim g = g ↔ ∀ x, g.val (A x) = A (g.val x)
  constructor
  · intro hg x
    have h := congrArg (fun z : TauCeti.QuadraticMap.orthogonalGroup Q => z.val (A x)) hg
    change A (g.val (A.symm (A x))) = g.val (A x) at h
    rw [A.symm_apply_apply] at h
    exact h.symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change A (g.val (A.symm x)) = g.val x
    rw [← hg, A.apply_symm_apply]

@[expose] def fixedCentralizerEquiv (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) :
    FixedCommutingProduct.fixedSubgroup (similarityConjugation Q A μ hsim) ≃*
      orthogonalOperatorCentralizer Q A.toLinearMap :=
  MulEquiv.subgroupCongr (fixed_similarityConjugation_eq Q A μ hsim)

@[expose] def scalarSigns (Q : QuadraticForm K V) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) where
  carrier := {g | g = 1 ∨ g = QuadraticMap.negOrthogonal Q}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro g h (rfl | rfl) (rfl | rfl) <;> simp [QuadraticMap.negOrthogonal_mul_self]
  inv_mem' := by
    rintro g (rfl | rfl) <;> simp [QuadraticMap.negOrthogonal_inv]

theorem mem_scalarSigns_iff (Q : QuadraticForm K V)
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    g ∈ scalarSigns Q ↔ g = 1 ∨ g = QuadraticMap.negOrthogonal Q := Iff.rfl

theorem scalarSigns_central (Q : QuadraticForm K V) :
    scalarSigns Q ≤ Subgroup.center (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  intro z hz
  rcases hz with rfl | rfl
  · exact Subgroup.one_mem _
  · apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp [LinearEquiv.mul_apply, QuadraticMap.coe_negOrthogonal]

instance scalarSigns_normal (Q : QuadraticForm K V) : (scalarSigns Q).Normal :=
  Subgroup.normal_of_le_center (scalarSigns_central Q)

theorem similarityConjugation_scalarSigns (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (z : scalarSigns Q) : similarityConjugation Q A μ hsim z.val = z.val := by
  rcases z.property with hz | hz
  · rw [hz, map_one]
  · rw [hz]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    simp [similarityConjugation_val, LinearEquiv.mul_apply, QuadraticMap.coe_negOrthogonal]

theorem scalarSigns_invariant (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) :
    (scalarSigns Q).map (similarityConjugation Q A μ hsim).toMonoidHom = scalarSigns Q := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change similarityConjugation Q A μ hsim w ∈ scalarSigns Q
    rw [similarityConjugation_scalarSigns Q A μ hsim ⟨w, hw⟩]
    exact hw
  · intro hz
    exact ⟨z, hz, similarityConjugation_scalarSigns Q A μ hsim ⟨z, hz⟩⟩

abbrev orthogonalDerived (Q : QuadraticForm K V) :=
  commutator (TauCeti.QuadraticMap.orthogonalGroup Q)

theorem orthogonalDerived_invariant (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) :
    (orthogonalDerived Q).map (similarityConjugation Q A μ hsim).toMonoidHom =
      orthogonalDerived Q :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance (similarityConjugation Q A μ hsim)

abbrev projectiveDerived (Q : QuadraticForm K V) :=
  orthogonalDerived Q ⧸ (scalarSigns Q).subgroupOf (orthogonalDerived Q)

@[expose] def projectiveConjugation (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x) :
    MulAut (projectiveDerived Q) :=
  onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q)
    (similarityConjugation Q A μ hsim) (orthogonalDerived_invariant Q A μ hsim)
    (scalarSigns_invariant Q A μ hsim)

theorem projectiveConjugation_mk (Q : QuadraticForm K V)
    (A : V ≃ₗ[K] V) (μ : Kˣ) (hsim : ∀ x : V, Q (A x) = (μ : K) * Q x)
    (g : orthogonalDerived Q) :
    projectiveConjugation Q A μ hsim
      ((QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q))) g) =
      (QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q)))
        (restrictAutomorphism (orthogonalDerived Q) (similarityConjugation Q A μ hsim)
          (orthogonalDerived_invariant Q A μ hsim) g) :=
  onNormalCentralQuotient_mk _ _ _ _ _ g

end CFSG.ComponentClassification.CatalogueBOrthogonalLinearFixed
