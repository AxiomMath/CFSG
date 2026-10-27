module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFieldDegree

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

section AlgebraAction

variable {K A F : Type*} [CommSemiring K] [Semiring A] [Algebra K A] [Group F]

@[expose] def invariantSubalgebraAction (rho : F →* (A ≃ₐ[K] A))
    (S : Subalgebra K A) (hS : ∀ g : F, ∀ x ∈ S, rho g x ∈ S) :
    F →* (S ≃ₐ[K] S) where
  toFun g :=
    { toFun x := ⟨rho g x, hS g x x.property⟩
      invFun x := ⟨rho g⁻¹ x, hS g⁻¹ x x.property⟩
      left_inv x := by
        apply Subtype.ext
        change rho g⁻¹ (rho g x.val) = x.val
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv x := by
        apply Subtype.ext
        change rho g (rho g⁻¹ x.val) = x.val
        rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      map_mul' x y := Subtype.ext (map_mul (rho g) x.val y.val)
      map_add' x y := Subtype.ext (map_add (rho g) x.val y.val)
      commutes' r := Subtype.ext ((rho g).commutes r) }
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change rho 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change rho (g * h) x.val = rho g (rho h x.val)
    rw [map_mul, AlgEquiv.mul_apply]

theorem invariantSubalgebraAction_mem_ker (rho : F →* (A ≃ₐ[K] A))
    (S : Subalgebra K A) (hS : ∀ g : F, ∀ x ∈ S, rho g x ∈ S) (g : F) :
    g ∈ (invariantSubalgebraAction rho S hS).ker ↔
      ∀ x ∈ S, rho g x = x := by
  change invariantSubalgebraAction rho S hS g = 1 ↔ _
  constructor
  · intro hg x hx
    have h := congrArg (fun e : S ≃ₐ[K] S => (e ⟨x, hx⟩ : A)) hg
    exact h
  · intro hg
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact hg x.val x.property

theorem invariantSubalgebraAction_ker_index_dvd (rho : F →* (A ≃ₐ[K] A))
    (S : Subalgebra K A) (hS : ∀ g : F, ∀ x ∈ S, rho g x ∈ S) :
    (invariantSubalgebraAction rho S hS).ker.index ∣ Nat.card (S ≃ₐ[K] S) := by
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

end AlgebraAction

section EndomorphismAction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def endomorphismConjugation :
    LinearMap.GeneralLinearGroup K V →* (Module.End K V ≃ₐ[K] Module.End K V) where
  toFun g := g.toLinearEquiv.conjAlgEquiv K
  map_one' := by
    ext S v
    simp only [LinearEquiv.conjAlgEquiv_apply_apply]
    rfl
  map_mul' g h := by
    ext S v
    simp only [AlgEquiv.mul_apply, LinearEquiv.conjAlgEquiv_apply_apply]
    rfl

theorem rationalCommutant_normalizer_kernel_index_dvd_four
    [Finite K] [FiniteDimensional K V] [Nontrivial V]
    {F : Type*} [Group F] (rho : F →* LinearMap.GeneralLinearGroup K V)
    (T : Module.End K V)
    (hirr : ∀ U : Submodule K V, (∀ v ∈ U, T v ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdim : Module.finrank K V = 4)
    (hS : ∀ g : F, ∀ S ∈ rationalCommutant T,
      endomorphismConjugation (rho g) S ∈ rationalCommutant T) :
    (invariantSubalgebraAction (endomorphismConjugation.comp rho)
      (rationalCommutant T) hS).ker.index ∣ 4 :=
  (invariantSubalgebraAction_ker_index_dvd
    (endomorphismConjugation.comp rho) (rationalCommutant T) hS).trans
      (rationalCommutant_card_aut_dvd_four T hirr hdim)

end EndomorphismAction

end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
