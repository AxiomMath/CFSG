module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open Matrix CatalogueBUnitaryIsometry

universe u v

variable {E : Type u} [Field E] [Finite E] {V : Type v}
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem odd_unitary_two_special_linear_isomorphism
    (r f : ℕ) [Fact r.Prime] (hr : r ≠ 2) (hf : 1 ≤ f)
    (hE : Nat.card E = (r ^ f) ^ 2)
    (h : V →ₛₗ[(unitaryFieldConjugation r f hE).toRingHom] V →ₗ[E] E)
    (hsym : h.IsSymm) (hnd : h.Nondegenerate) (hdim : Module.finrank E V = 2) :
    let sigma := unitaryFieldConjugation r f hE
    Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E sigma) = r ^ f ∧
      ∃ (B : (Fin 2 → E) ≃ₗ[E] V) (t : Eˣ)
        (e : specialIsometry h ≃*
          SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma)),
        (∀ x y, h (B x) (B y) = hyperbolicForm sigma x y) ∧
        (∀ i j, h (B (Pi.single i 1)) (B (Pi.single j 1)) = hyperbolicMatrix i j) ∧
        sigma (t : E) = -(t : E) ∧
        (∀ g : specialIsometry h,
          (fixedSLMap sigma (e g)).val = (diagonalGL t)⁻¹.val *
            LinearMap.toMatrix' ((B.trans g.val.val).trans B.symm).toLinearMap *
            (diagonalGL t).val) ∧
        (∀ N : SpecialLinearGroup (Fin 2) (CatalogueBLinearTwoDescent.fixedSubfield E sigma),
          LinearMap.toMatrix' ((B.trans (e.symm N).val.val).trans B.symm).toLinearMap =
            (diagonalGL t).val * (fixedSLMap sigma N).val * (diagonalGL t)⁻¹.val) := by
  have _ : Odd (r ^ f) := (Fact.out : r.Prime).odd_of_ne_two hr |>.pow
  have _ : f ≠ 0 := by omega
  exact unitary_field_two_special_linear_isomorphism r f hE h hsym hnd hdim

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
