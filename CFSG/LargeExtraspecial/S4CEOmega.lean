module

public import CFSG.LargeExtraspecial.S4CEOmegaTwo
public import CFSG.LargeExtraspecial.S4SevenInput

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

theorem CEHyp.ker_eq_bot_of_omegaPair
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {K : Type*} [Group K] [Finite K] {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V}
    {Q : QuadraticForm (ZMod 2) V} (hQ : Q.polarBilin.Nondegenerate) (ha0 : a ≠ 0)
    (ha : Q a = 0) (h6 : 6 ≤ finrank (ZMod 2) V)
    (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) : π.ker = ⊥ :=
  h.ker_eq_bot_of_omega_of_odd hQ h6 (h.isPGroup_two hQ ha0 ha)
    (h.odd_card_ker_of_omega hQ ha0 ha h6)

theorem centralExtInput_omega
    (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V) (ha : a ≠ 0) (h6 : 6 ≤ finrank (ZMod 2) V)
    (hpair : 4 ≤ finrank (ZMod 2) V ∧ ∃ (Q : QuadraticForm (ZMod 2) V)
      (hQ : Q.polarBilin.Nondegenerate), Q a = 0 ∧ X = omegaGroup Q hQ ∧ E₀ = pointRadical Q a)
    (K : Type u) [Group K] [Finite K] (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K)
    (hrange : π.range = X) (hcen : π.ker ≤ center K) (hinf : E ⊓ π.ker = ⊥)
    (hmap : E.map π = E₀) (hgen : closure {k | ∃ x : K, ∃ e ∈ E, k = x * e * x⁻¹} = ⊤)
    (hnorm : ∀ x : K, π x a = a → x ∈ normalizer (E : Set K))
    (_hwc : ∀ x : K, E.map (MulAut.conj x).toMonoidHom ≤ normalizer (E : Set K) →
      E.map (MulAut.conj x).toMonoidHom = E) :
    π.ker = ⊥ ∨ (A6Pair X E₀ a ∧ Nat.card π.ker = 3) := by
  obtain ⟨-, Q, hQ, hQa, rfl, rfl⟩ := hpair
  exact Or.inl (CEHyp.ker_eq_bot_of_omegaPair hQ ha hQa h6
    ⟨hrange, hcen, hinf, hmap, hgen, hnorm⟩)

end CFSG.LargeExtraspecial.S4
