module

public import CFSG.LieType.RootSystem.Cartan
public import CFSG.LieType.CurtisTits.Reduction

public section

namespace CFSG.LieType.Universal

open CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

universe u w

structure UniversalRootDatum (K : Type u) [Group K] where
  rank : ℕ
  cartan : Matrix (Fin rank) (Fin rank) ℤ
  isFiniteType : TauCeti.IsFiniteType cartan
  divisible : Set (Fin rank)
  rootGroup : (Fin rank → ℤ) → Subgroup K

@[expose] def IsNegMultiple {ι : Type*} (α β : ι → ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a • β = -(b • α)

namespace UniversalRootDatum

variable {K : Type u} [Group K] (D : UniversalRootDatum K)

abbrev roots : Set (Fin D.rank → ℤ) := RootSystem.roots D.isFiniteType D.divisible

@[expose] def cone (α β : Fin D.rank → ℤ) : Set (Fin D.rank → ℤ) :=
  {γ | γ ∈ D.roots ∧ ∃ a b : ℕ, γ = a • α + b • β}

@[expose] def relsR1 : Set (Set (Fin D.rank → ℤ)) :=
  {S | ∃ α ∈ D.roots, ∃ β ∈ D.roots, ¬ IsNegMultiple α β ∧ S = D.cone α β}

@[expose] def relsR2 : Set (Set (Fin D.rank → ℤ)) :=
  {S | ∃ i : Fin D.rank, S = {Pi.single i 1, -Pi.single i 1}}

abbrev levi (J : Finset (Fin D.rank)) : Subgroup K := CurtisTits.levi D.rootGroup J

abbrev leviAmalgam : {J : Finset (Fin D.rank) // J.card ≤ 2} → Subgroup K :=
  CurtisTits.leviAmalgam D.rootGroup

@[expose] def SteinbergPresentation : Prop :=
  (⨆ γ ∈ D.roots, D.rootGroup γ = ⊤) ∧
    IsPresentedBy.{u, w} D.roots D.rootGroup (D.relsR1 ∪ D.relsR2)

theorem rels_conj (S : Set (Fin D.rank → ℤ)) (hS : S ∈ D.relsR1 ∪ D.relsR2) :
    S ⊆ D.roots ∧ ∃ (u : (coxeterMatrix D.isFiniteType).Group) (J : Finset (Fin D.rank)),
      J.card ≤ 2 ∧ ∀ γ ∈ S, ∀ k ∉ J, weylAction D.isFiniteType u γ k = 0 := by
  rcases hS with ⟨α, hα, β, hβ, -, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨fun γ hγ => hγ.1, ?_⟩
    obtain ⟨u, J, hJ, hu⟩ := exists_weylAction_support_subset D.isFiniteType D.divisible hα hβ
    refine ⟨u, J, hJ, fun γ hγ => hu γ hγ.1 ?_⟩
    obtain ⟨-, a, b, rfl⟩ := hγ
    exact ⟨a, b, fun k => by simp⟩
  · have hΦ := isCTRootSystem D.isFiniteType D.divisible
    have hneg : -Pi.single i 1 ∈ D.roots := by
      have := hΦ.smul_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) _
        (hΦ.single_mem i)
      rwa [hΦ.simple_single] at this
    refine ⟨?_, 1, {i}, by simp, ?_⟩
    · rintro γ (rfl | rfl)
      exacts [hΦ.single_mem i, hneg]
    · rintro γ (rfl | rfl) k hk
      · simp [Pi.single_eq_of_ne (by simpa using hk : k ≠ i)]
      · simp [Pi.single_eq_of_ne (by simpa using hk : k ≠ i)]

theorem isUniversalCompletion_of_steinbergPresentation {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hK : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hSt : SteinbergPresentation.{u, max w u} D) :
    IsUniversalCompletion.{u, 0, w} D.leviAmalgam :=
  isUniversalCompletion_levi (isCTRootSystem D.isFiniteType D.divisible) hK _ D.rels_conj hSt.2

end UniversalRootDatum

end CFSG.LieType.Universal
