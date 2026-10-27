module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.InvertedSubgroup.InvertedSubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralCase

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace ExtraspecialDimensionBounds

open scoped MonoidAlgebra in
theorem finiteDimensional_of_irreducible' {F G V : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (h : ρ.IsIrreducible) :
    FiniteDimensional F V := by
  have : IsSimpleModule F[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  have : Module.Finite F[G] ρ.asModule := inferInstance
  have : Module.Finite F ρ.asModule := Module.Finite.trans F[G] ρ.asModule
  exact this

variable {G : Type} [Group G] [Finite G]

theorem exists_inverted {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.IsExtraspecialPGroup p ↥P) (hexp : Monoid.exponent ↥P = p)
    (hcard : Nat.card ↥P = p ^ (1 + 2 * n)) {t : G} (ht : orderOf t = 2)
    (htN : t ∈ Subgroup.normalizer (P : Set G)) (hPt : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ X : Subgroup G, X ≤ P ∧ Nat.card ↥X = p ∧ X ≠ centerP P ∧
      ∀ x ∈ X, t * x * t⁻¹ = x⁻¹ :=
  Section5.InvertedSubgroup.exists_subgroup hp hp2 hP hexp ht htN hPt

theorem central_case {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.IsExtraspecialPGroup p ↥P) (hexp : Monoid.exponent ↥P = p)
    (hcard : Nat.card ↥P = p ^ (1 + 2 * n)) (hPn : P.Normal)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {t : G} (ht : orderOf t = 2)
    (htc : t ∈ Subgroup.centralizer (P : Set G)) :
    p ^ (n - 1) * WeakClosure.dOfPrime p * (p - 1) ≤
      2 * Module.finrank (ZMod 2) ↥(BinaryRepresentations.commSpace ρ (Subgroup.zpowers t)) :=
  Section5.CentralCase.bound hp hp2 hP hexp hcard hPn ρ hρ hirr ht htc

end ExtraspecialDimensionBounds
end Section5
end CFSG.LocalAnalysis.RankThreeUC
