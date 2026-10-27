module

public import CFSG.LargeExtraspecial.S4Lin
public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S4SpU
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

universe u

variable {V : Type u} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def A6Pair (X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V) : Prop :=
  finrank (ZMod 2) V = 4 ∧ ∃ (β : LinearMap.BilinForm (ZMod 2) V) (hβ : β.IsAlt),
    β.Nondegenerate ∧
    X = ⁅TauCeti.BilinForm.isometryGroup β, TauCeti.BilinForm.isometryGroup β⁆ ∧
    E₀ ≤ spPointRadical β a ∧ Nat.card (spPointRadical β a) = 2 * Nat.card E₀ ∧
    spTransvection β hβ a ∉ E₀ ∧
    ∀ d (hd : β a d = 0), d ∉ (ZMod 2) ∙ a → spRho hβ hd 0 ∉ E₀

@[expose] def NaturalPair [FiniteDimensional (ZMod 2) V] (X E₀ : Subgroup (V ≃ₗ[ZMod 2] V))
    (a : V) : Prop :=
  (2 ≤ finrank (ZMod 2) V ∧ X = ⊤ ∧ E₀ = centreGroup V a) ∨
  (4 ≤ finrank (ZMod 2) V ∧ ∃ (β : LinearMap.BilinForm (ZMod 2) V) (_ : β.IsAlt),
    β.Nondegenerate ∧ X = TauCeti.BilinForm.isometryGroup β ∧ E₀ = spPointRadical β a) ∨
  A6Pair X E₀ a ∨
  (4 ≤ finrank (ZMod 2) V ∧ ∃ (Q : QuadraticForm (ZMod 2) V) (hQ : Q.polarBilin.Nondegenerate),
    Q a = 0 ∧ X = omegaGroup Q hQ ∧ E₀ = pointRadical Q a)

@[expose] def CentralExtInput : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (a : V), a ≠ 0 → NaturalPair X E₀ a →
    ∀ (K : Type u) [Group K] [Finite K] (π : K →* (V ≃ₗ[ZMod 2] V)) (E : Subgroup K),
      π.range = X → π.ker ≤ center K → E ⊓ π.ker = ⊥ → E.map π = E₀ →
      closure {k | ∃ x : K, ∃ e ∈ E, k = x * e * x⁻¹} = ⊤ →
      (∀ x : K, π x a = a → x ∈ normalizer (E : Set K)) →
      (∀ x : K, E.map (MulAut.conj x).toMonoidHom ≤ normalizer (E : Set K) →
        E.map (MulAut.conj x).toMonoidHom = E) →
      π.ker = ⊥ ∨ (A6Pair X E₀ a ∧ Nat.card π.ker = 3)

end CFSG.LargeExtraspecial.S4
