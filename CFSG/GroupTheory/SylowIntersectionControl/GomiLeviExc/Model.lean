module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Transfer
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.CharTwoSteinberg
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.SimplyLaced
public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.LeviRange
public import CFSG.LieType.Steinberg.Conclusion

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbeddingD2.ParabLevi

structure IsCharTwoModel {G : Type} [Group G] (DT : UniversalRootDatum G) (k : Type) [Field k]
    (xT : (Fin DT.rank → ℤ) → k → G) : Prop where
  conclusionB : ConclusionB DT k xT
  divisible : DT.divisible = ∅
  isSymm : DT.cartan.IsSymm
  steinberg : IsCharTwoSteinberg DT.roots xT
  isQuasisimple : CFSG.IsQuasisimple G
  odd_card_center : Odd (Nat.card (center G))
  isChevTwo : IsChevTwo (G ⧸ center G)

@[expose] def HasCharTwoModel (k : Type) [Field k] {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) :
    Prop :=
  ∃ (G : Type) (_ : Group G) (DT : UniversalRootDatum G) (xT : (Fin DT.rank → ℤ) → k → G)
    (σ : Fin r ≃ Fin DT.rank), (∀ i j, DT.cartan (σ i) (σ j) = A i j) ∧ IsCharTwoModel DT k xT

theorem roots_eq_of_cartan_eq {r : ℕ} {A A' : Matrix (Fin r) (Fin r) ℤ}
    (hA : TauCeti.IsFiniteType A) (hA' : TauCeti.IsFiniteType A') (h : A = A')
    (d : Set (Fin r)) :
    CFSG.LieType.RootSystem.roots hA d = CFSG.LieType.RootSystem.roots hA' d := by
  subst h
  rfl

theorem gomiLeviFactor_leviM_of_model {G K k : Type} [Group G] [Group K] [Finite K] [Field k]
    {DT : UniversalRootDatum G} {xT : (Fin DT.rank → ℤ) → k → G} (hM : IsCharTwoModel DT k xT)
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hdiv : D.divisible = ∅) {x : (Fin D.rank → ℤ) → k → K}
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    {e : Fin DT.rank → Fin D.rank} (he : Function.Injective e)
    (hcart : D.cartan.submatrix e e = DT.cartan) (hr : 1 ≤ DT.rank)
    (hx : IsCharTwoSteinberg (CFSG.LieType.RootSystem.roots (D.isFiniteType.submatrix he) ∅)
      fun γ c => x (Restrict.ext e γ) c) :
    GomiLeviFactor ↥(leviM D (Set.range e)) := by
  have hroots : CFSG.LieType.RootSystem.roots (D.isFiniteType.submatrix he) ∅ =
      (RootSystem.ofCartan DT.isFiniteType DT.divisible).roots := by
    rw [RootSystem.ofCartan_roots, hM.divisible]
    exact roots_eq_of_cartan_eq _ _ hcart ∅
  have hsl : ∀ α ∈ (RootSystem.ofCartan DT.isFiniteType DT.divisible).roots,
      ∀ β ∈ (RootSystem.ofCartan DT.isFiniteType DT.divisible).roots, α + β ≠ 0 →
        ∀ p ∈ expPairs (RootSystem.ofCartan DT.isFiniteType DT.divisible) α β, p = (1, 1) := by
    intro α hα β hβ hαβ p hp
    rw [hM.divisible] at hα hβ hp
    exact expPairs_eq_of_isSymm DT.isFiniteType hM.isSymm hα hβ hαβ hp
  have hx' : IsCharTwoSteinberg (RootSystem.ofCartan DT.isFiniteType DT.divisible).roots
      fun γ c => x (Restrict.ext e γ) c := by
    rw [← hroots]
    exact hx
  obtain ⟨φ, hφ⟩ := exists_hom_of_isCharTwoSteinberg hsl hM.conclusionB.2.1
    hM.conclusionB.2.2.1 hM.steinberg hx'
  have hrange : φ.range = leviM D (Set.range e) := by
    rw [range_eq_closure_of_presentationB hM.conclusionB.2.1 hM.conclusionB.2.2.1 φ hφ,
      ← hroots]
    exact closure_rootElements_ext_eq_leviM hct hdiv hpar he
  exact gomiLeviFactor_of_range_eq hM.isQuasisimple hM.odd_card_center hM.isChevTwo φ hrange
    (leviM_range_ne_bot hpar hr)

end CFSG.GroupTheory.GomiLeviExc
