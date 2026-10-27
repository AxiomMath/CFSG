module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalLinearFixedConjugation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentNormalization
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentRestriction

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalFieldFixed

open CatalogueBOrthogonalDescent CatalogueBOrthogonalLinearFixed

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem inverse_semilinear (sigma : K ≃+* K) (tau0 : V ≃+ V)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x) (a : K) (x : V) :
    tau0.symm (a • x) = sigma.symm a • tau0.symm x := by
  apply tau0.injective
  rw [tau0.apply_symm_apply, hsemi, sigma.apply_symm_apply, tau0.apply_symm_apply]

@[expose] def semilinearConjugatedLinear (sigma : K ≃+* K) (tau0 : V ≃+ V)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x) (g : V ≃ₗ[K] V) :
    V ≃ₗ[K] V :=
  { tau0.symm.trans (g.toAddEquiv.trans tau0) with
    map_smul' := by
      intro a x
      change tau0 (g (tau0.symm (a • x))) = a • tau0 (g (tau0.symm x))
      rw [inverse_semilinear sigma tau0 hsemi, g.map_smul, hsemi,
        sigma.apply_symm_apply] }

theorem semilinearConjugatedLinear_apply (sigma : K ≃+* K) (tau0 : V ≃+ V)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x) (g : V ≃ₗ[K] V) (x : V) :
    semilinearConjugatedLinear sigma tau0 hsemi g x = tau0 (g (tau0.symm x)) := rfl

theorem semilinear_conjugation_preserves (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    semilinearConjugatedLinear sigma tau0 hsemi g.val ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
  apply TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
  intro x
  rw [semilinearConjugatedLinear_apply, hsim,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.property, ← hsim,
    tau0.apply_symm_apply]

theorem inverse_semilinear_conjugation_preserves (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    semilinearConjugatedLinear sigma.symm tau0.symm
      (inverse_semilinear sigma tau0 hsemi) g.val ∈
        TauCeti.QuadraticMap.orthogonalGroup Q := by
  apply TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
  intro x
  apply sigma.injective
  apply mul_left_cancel₀ (Units.ne_zero mu)
  rw [← hsim]
  change Q (tau0 (tau0.symm (g.val (tau0 x)))) = (mu : K) * sigma (Q x)
  rw [tau0.apply_symm_apply, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.property,
    hsim]

@[expose] def semilinearConjugation (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) :
    MulAut (TauCeti.QuadraticMap.orthogonalGroup Q) where
  toFun g := ⟨semilinearConjugatedLinear sigma tau0 hsemi g.val,
    semilinear_conjugation_preserves Q sigma tau0 mu hsemi hsim g⟩
  invFun g := ⟨semilinearConjugatedLinear sigma.symm tau0.symm
    (inverse_semilinear sigma tau0 hsemi) g.val,
    inverse_semilinear_conjugation_preserves Q sigma tau0 mu hsemi hsim g⟩
  left_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change tau0.symm (tau0 (g.val (tau0.symm (tau0 x)))) = g.val x
    rw [tau0.symm_apply_apply, tau0.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change tau0 (tau0.symm (g.val (tau0 (tau0.symm x)))) = g.val x
    rw [tau0.apply_symm_apply, tau0.apply_symm_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    change tau0 (g.val (h.val (tau0.symm x))) =
      tau0 (g.val (tau0.symm (tau0 (h.val (tau0.symm x)))))
    rw [tau0.symm_apply_apply]

theorem semilinearConjugation_apply (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    (semilinearConjugation Q sigma tau0 mu hsemi hsim g).val x =
      tau0 (g.val (tau0.symm x)) := rfl

theorem semilinearConjugation_symm_apply (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (g : TauCeti.QuadraticMap.orthogonalGroup Q) (x : V) :
    ((semilinearConjugation Q sigma tau0 mu hsemi hsim).symm g).val x =
      tau0.symm (g.val (tau0 x)) := rfl

theorem fixed_semilinearConjugation_eq (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) :
    FixedCommutingProduct.fixedSubgroup (semilinearConjugation Q sigma tau0 mu hsemi hsim) =
      semilinearOrthogonalCentralizer Q tau0 := by
  ext g
  rw [mem_semilinearOrthogonalCentralizer_iff]
  change semilinearConjugation Q sigma tau0 mu hsemi hsim g = g ↔
    ∀ x, g.val (tau0 x) = tau0 (g.val x)
  constructor
  · intro hg x
    have h := congrArg (fun z : TauCeti.QuadraticMap.orthogonalGroup Q => z.val (tau0 x)) hg
    rw [semilinearConjugation_apply, tau0.symm_apply_apply] at h
    exact h.symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [semilinearConjugation_apply, ← hg, tau0.apply_symm_apply]

@[expose] def semilinearFixedCentralizerEquiv (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) :
    FixedCommutingProduct.fixedSubgroup (semilinearConjugation Q sigma tau0 mu hsemi hsim) ≃*
      semilinearOrthogonalCentralizer Q tau0 :=
  MulEquiv.subgroupCongr (fixed_semilinearConjugation_eq Q sigma tau0 mu hsemi hsim)

theorem semilinearConjugation_scalarSigns (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x))
    (z : scalarSigns Q) : semilinearConjugation Q sigma tau0 mu hsemi hsim z.val = z.val := by
  rcases z.property with hz | hz
  · rw [hz, map_one]
  · rw [hz]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [semilinearConjugation_apply]
    simp [QuadraticMap.coe_negOrthogonal]

theorem semilinear_scalarSigns_invariant (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) :
    (scalarSigns Q).map (semilinearConjugation Q sigma tau0 mu hsemi hsim).toMonoidHom =
      scalarSigns Q := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change semilinearConjugation Q sigma tau0 mu hsemi hsim w ∈ scalarSigns Q
    rw [semilinearConjugation_scalarSigns Q sigma tau0 mu hsemi hsim ⟨w, hw⟩]
    exact hw
  · intro hz
    exact ⟨z, hz, semilinearConjugation_scalarSigns Q sigma tau0 mu hsemi hsim ⟨z, hz⟩⟩

theorem semilinear_orthogonalDerived_invariant (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) :
    (orthogonalDerived Q).map (semilinearConjugation Q sigma tau0 mu hsemi hsim).toMonoidHom =
      orthogonalDerived Q :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance
    (semilinearConjugation Q sigma tau0 mu hsemi hsim)

@[expose] def projectiveSemilinearConjugation (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) :
    MulAut (projectiveDerived Q) :=
  onNormalCentralQuotient (orthogonalDerived Q) (scalarSigns Q)
    (semilinearConjugation Q sigma tau0 mu hsemi hsim)
    (semilinear_orthogonalDerived_invariant Q sigma tau0 mu hsemi hsim)
    (semilinear_scalarSigns_invariant Q sigma tau0 mu hsemi hsim)

theorem projectiveSemilinearConjugation_mk (Q : QuadraticForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hsim : ∀ x, Q (tau0 x) = (mu : K) * sigma (Q x)) (g : orthogonalDerived Q) :
    projectiveSemilinearConjugation Q sigma tau0 mu hsemi hsim
      ((QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q))) g) =
      (QuotientGroup.mk' ((scalarSigns Q).subgroupOf (orthogonalDerived Q)))
        (restrictAutomorphism (orthogonalDerived Q)
          (semilinearConjugation Q sigma tau0 mu hsemi hsim)
          (semilinear_orthogonalDerived_invariant Q sigma tau0 mu hsemi hsim) g) :=
  onNormalCentralQuotient_mk _ _ _ _ _ g

end CFSG.ComponentClassification.CatalogueBOrthogonalFieldFixed
