module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoSpaces
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryTwo

open Matrix CatalogueBUnitaryIsometry

universe u v

variable {E : Type u} [Field E] [Finite E]

theorem unitaryFieldCharP (r f : ℕ) [Fact r.Prime]
    (hE : Nat.card E = (r ^ f) ^ 2) : CharP E r := by
  let : Fintype E := Fintype.ofFinite E
  apply charP_of_card_eq_prime_pow (f := f * 2)
  rw [pow_mul]
  simpa only [Nat.card_eq_fintype_card] using hE

@[expose] def unitaryFieldConjugation (r f : ℕ) [Fact r.Prime]
    (hE : Nat.card E = (r ^ f) ^ 2) : E ≃+* E := by
  letI : CharP E r := unitaryFieldCharP r f hE
  exact iterateFrobeniusEquiv E r f

theorem unitaryFieldConjugation_apply (r f : ℕ) [Fact r.Prime]
    (hE : Nat.card E = (r ^ f) ^ 2) (x : E) :
    unitaryFieldConjugation r f hE x = x ^ (r ^ f) := by
  let : CharP E r := unitaryFieldCharP r f hE
  exact iterateFrobeniusEquiv_def E r f x

theorem unitaryFieldConjugation_data (r f : ℕ) [Fact r.Prime]
    (hE : Nat.card E = (r ^ f) ^ 2) :
    (unitaryFieldConjugation r f hE) ^ 2 = 1 ∧
      unitaryFieldConjugation r f hE ≠ 1 ∧
      Nat.card (CatalogueBLinearTwoDescent.fixedSubfield E
        (unitaryFieldConjugation r f hE)) = r ^ f := by
  let : CharP E r := unitaryFieldCharP r f hE
  exact quadraticFrobenius_data r f hE

variable {V : Type v} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem unitary_field_two_special_linear_isomorphism (r f : ℕ) [Fact r.Prime]
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
  obtain ⟨hsigma, hne, hfixed⟩ := unitaryFieldConjugation_data r f hE
  exact ⟨hfixed, exists_unitary_two_special_linear_isomorphism
    (unitaryFieldConjugation r f hE) h hsym hnd hsigma hne hdim⟩

end CFSG.ComponentClassification.CatalogueBUnitaryTwo
