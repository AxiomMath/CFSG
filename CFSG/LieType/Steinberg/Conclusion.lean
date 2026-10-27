module

public import CFSG.LieType.Steinberg.Presentation
public import CFSG.LieType.Steinberg.PartBAssembly

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

universe u w

variable {K : Type u} [Group K]

@[expose] def ConclusionA (D : UniversalRootDatum K) : Prop :=
  PresentationA.{0, u, w} (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup ∧
    D.SteinbergPresentation.{u, w}

@[expose] def ConclusionB (D : UniversalRootDatum K) (k : Type*) [Field k]
    (x : (Fin D.rank → ℤ) → k → K) : Prop :=
  IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x ∧
    Nonempty (CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)) ∧
    PresentationB (Φ := RootSystem.ofCartan D.isFiniteType D.divisible) x ∧
    RedundantR2 (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem conclusionA_of
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) : ConclusionA.{u, w} D :=
  ⟨presentationA_of hct hext, steinbergPresentation_of_extras hct hext⟩

theorem conclusionB_of {k : Type*} [Field k] [Finite k] {x : (Fin D.rank → ℤ) → k → K}
    (hD : D.divisible = ∅)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H)
    (hpar : IsParametrization (Φ := RootSystem.ofCartan D.isFiniteType D.divisible)
      D.rootGroup x)
    (hC : ∀ O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible),
      ∃ C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ,
        (∀ α ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).roots,
          ∀ β ∈ (RootSystem.ofCartan D.isFiniteType D.divisible).roots,
            ∀ p ∈ expPairs (RootSystem.ofCartan D.isFiniteType D.divisible) α β,
              (C α β p).natAbs ∈ ({1, 2, 3} : Set ℕ)) ∧ CommutatorFormula x O C)
    (hE : ∀ (O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible))
      (C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ),
        CommutatorFormula x O C → ChevalleyExtras D k x C O) :
    ConclusionB D k x := by
  have hbij := (bijective_stPi_of hct hext).2
  refine ⟨hpar, nonempty_commOrder_ofCartan D.isFiniteType hD, presentationB_of hD hC hE hbij,
    redundantR2_of hD (fun O => (hC O).imp fun _ h => h.2) hE hbij⟩

end CFSG.LieType.Steinberg
