module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixedConjugation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFieldFixedPolarization

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSymplecticB

open LinearMap (BilinForm)
open CatalogueBAlternatingIsometry CatalogueBOrthogonalFieldFixed CatalogueBOrthogonalDescent

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

@[expose] def semilinearSymplecticCentralizer (B : BilinForm K V) (T : V ≃+ V) :
    Subgroup (isometryGroup B) :=
  (Subgroup.centralizer {T.toEquiv}).comap
    (linearPermutationAction.comp (isometryGroup B).subtype)

theorem mem_semilinearSymplecticCentralizer_iff (B : BilinForm K V) (T : V ≃+ V)
    (g : isometryGroup B) :
    g ∈ semilinearSymplecticCentralizer B T ↔ ∀ x, g.val (T x) = T (g.val x) := by
  change (linearPermutationAction g.val) ∈ Subgroup.centralizer {T.toEquiv} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h x
    exact congrArg (fun e : Equiv.Perm V => e x) h
  · intro h
    ext x
    exact h x

theorem semilinearSymplecticCentralizer_commutes (B : BilinForm K V) (T : V ≃+ V)
    (g : semilinearSymplecticCentralizer B T) (x : V) :
    g.val.val (T x) = T (g.val.val x) :=
  (mem_semilinearSymplecticCentralizer_iff B T g.val).mp g.property x

theorem semilinear_conjugation_preserves (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (g : isometryGroup B) :
    semilinearConjugatedLinear sigma tau0 hsemi g.val ∈ isometryGroup B := by
  apply (mem_isometryGroup_iff B _).mpr
  intro x y
  rw [semilinearConjugatedLinear_apply, semilinearConjugatedLinear_apply, hform,
    (mem_isometryGroup_iff B g.val).mp g.property, ← hform, tau0.apply_symm_apply,
    tau0.apply_symm_apply]

theorem inverse_semilinear_conjugation_preserves (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (g : isometryGroup B) :
    semilinearConjugatedLinear sigma.symm tau0.symm
      (inverse_semilinear sigma tau0 hsemi) g.val ∈ isometryGroup B := by
  apply (mem_isometryGroup_iff B _).mpr
  intro x y
  apply sigma.injective
  apply mul_left_cancel₀ (Units.ne_zero mu)
  rw [← hform, ← hform]
  change B (tau0 (tau0.symm (g.val (tau0 x)))) (tau0 (tau0.symm (g.val (tau0 y)))) =
    B (tau0 x) (tau0 y)
  rw [tau0.apply_symm_apply, tau0.apply_symm_apply,
    (mem_isometryGroup_iff B g.val).mp g.property]

@[expose] def semilinearConjugation (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) :
    MulAut (isometryGroup B) where
  toFun g := ⟨semilinearConjugatedLinear sigma tau0 hsemi g.val,
    semilinear_conjugation_preserves B sigma tau0 mu hsemi hform g⟩
  invFun g := ⟨semilinearConjugatedLinear sigma.symm tau0.symm
    (inverse_semilinear sigma tau0 hsemi) g.val,
    inverse_semilinear_conjugation_preserves B sigma tau0 mu hsemi hform g⟩
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

theorem semilinearConjugation_apply (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y))
    (g : isometryGroup B) (x : V) :
    (semilinearConjugation B sigma tau0 mu hsemi hform g).val x =
      tau0 (g.val (tau0.symm x)) := rfl

theorem fixed_semilinearConjugation_eq (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) :
    FixedCommutingProduct.fixedSubgroup (semilinearConjugation B sigma tau0 mu hsemi hform) =
      semilinearSymplecticCentralizer B tau0 := by
  ext g
  rw [mem_semilinearSymplecticCentralizer_iff]
  change semilinearConjugation B sigma tau0 mu hsemi hform g = g ↔
    ∀ x, g.val (tau0 x) = tau0 (g.val x)
  constructor
  · intro hg x
    have h := congrArg (fun z : isometryGroup B => z.val (tau0 x)) hg
    rw [semilinearConjugation_apply, tau0.symm_apply_apply] at h
    exact h.symm
  · intro hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [semilinearConjugation_apply, ← hg, tau0.apply_symm_apply]

@[expose] def semilinearFixedCentralizerEquiv (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) :
    FixedCommutingProduct.fixedSubgroup (semilinearConjugation B sigma tau0 mu hsemi hform) ≃*
      semilinearSymplecticCentralizer B tau0 :=
  MulEquiv.subgroupCongr (fixed_semilinearConjugation_eq B sigma tau0 mu hsemi hform)

theorem semilinearConjugation_negIsometry (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) :
    semilinearConjugation B sigma tau0 mu hsemi hform (negIsometry B) = negIsometry B := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [semilinearConjugation_apply]
  change tau0 (-(tau0.symm x)) = -x
  rw [map_neg, tau0.apply_symm_apply]

theorem semilinear_scalarSigns_invariant (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) :
    (scalarSigns B).map (semilinearConjugation B sigma tau0 mu hsemi hform).toMonoidHom =
      scalarSigns B :=
  scalarSigns_map_eq B _ (semilinearConjugation_negIsometry B sigma tau0 mu hsemi hform)

@[expose] def projectiveSemilinearConjugation (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) :
    MulAut (projectiveSymplectic B) :=
  CatalogueBFixedCentralQuotient.onQuotient (scalarSigns B)
    (semilinearConjugation B sigma tau0 mu hsemi hform)
    (semilinear_scalarSigns_invariant B sigma tau0 mu hsemi hform)

theorem projectiveSemilinearConjugation_mk (B : BilinForm K V)
    (sigma : K ≃+* K) (tau0 : V ≃+ V) (mu : Kˣ)
    (hsemi : ∀ a x, tau0 (a • x) = sigma a • tau0 x)
    (hform : ∀ x y, B (tau0 x) (tau0 y) = (mu : K) * sigma (B x y)) (g : isometryGroup B) :
    projectiveSemilinearConjugation B sigma tau0 mu hsemi hform
        (QuotientGroup.mk' (scalarSigns B) g) =
      QuotientGroup.mk' (scalarSigns B) (semilinearConjugation B sigma tau0 mu hsemi hform g) :=
  CatalogueBFixedCentralQuotient.onQuotient_mk _ _ _ g

end CFSG.ComponentClassification.CatalogueBSymplecticB
