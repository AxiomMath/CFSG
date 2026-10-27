module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic

public section

namespace CFSG.GroupTheory

@[expose] def GomiHyp43Type (K : Type) [Group K] : Prop :=
  (IsGomiChevTwo K ∧ ¬ IsGomiU3 (K ⧸ Subgroup.center K) ∧ ¬ IsGomiSz (K ⧸ Subgroup.center K)) ∨
    ∃ n : ℕ, 7 ≤ n ∧ Nonempty (K ≃* alternatingGroup (Fin n))

variable {Ω : Type} [Group Ω] [Finite Ω]

structure GomiHyp43 (G : Subgroup Ω) : Prop where
  even : Even (Nat.card G)
  charTwo : CFSG.QuasithinUnique.CharTwo G
  sections : ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K →
    CFSG.SignalizerFunctorTheorem.IsSectionOf K ↥G → GomiInQ K → GomiHyp43Type K

omit [Finite Ω] in
theorem GomiHyp43.mono {G H : Subgroup Ω} (hG : GomiHyp43 G) (hHG : H ≤ G)
    (he : Even (Nat.card H)) (hc : CFSG.QuasithinUnique.CharTwo H) : GomiHyp43 H where
  even := he
  charTwo := hc
  sections K _ _ hK hsec hQ := by
    obtain ⟨K', f, hf⟩ := hsec
    refine hG.sections K hK ?_ hQ
    let ι : ↥H →* ↥G := Subgroup.inclusion hHG
    have hι : Function.Injective ι := Subgroup.inclusion_injective hHG
    let e : ↥K' ≃* ↥(K'.map ι) := K'.equivMapOfInjective ι hι
    exact ⟨K'.map ι, f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective⟩

@[expose] def GomiHyp43OfKnown : Prop :=
  ∀ {Ω : Type} [Group Ω] [Finite Ω] (G : Subgroup Ω), Even (Nat.card G) →
    CFSG.QuasithinUnique.CharTwo G →
    (∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      CFSG.SignalizerFunctorTheorem.IsSectionOf S ↥G → CFSG.Open.IsCatalogGroup S) →
    GomiHyp43 G

end CFSG.GroupTheory
