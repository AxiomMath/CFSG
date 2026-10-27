module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A6
public import CFSG.LieType.Multipliers.U43Action

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def A6InnerLieSmall : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], OddLieType S →
    ∀ z : S, orderOf z = 2 → Nat.card (centralizer ({z} : Set S)) ≤ 1440 →
    ∀ D : Subgroup (centralizer ({z} : Set S)), D.Normal →
      ¬ Nonempty (D ≃* alternatingGroup (Fin 6))

@[expose] def A6OuterLieSmall : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (OddLieType S ∨ EvenLieType S) →
    ∀ σ : MulAut S, orderOf σ = 2 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    Nat.card (fixedSubgroup σ) ≤ 720 →
    ∀ D : Subgroup (fixedSubgroup σ), D.Normal → Nonempty (D ≃* alternatingGroup (Fin 6)) →
    (∀ x : fixedSubgroup σ, orderOf x = 2 → x ∈ D) →
      Nonempty (S ≃* CFSG.LieType.Multipliers.U43.X₀) ∧ Nat.card (fixedSubgroup σ) = 720

theorem a6InnerOddLie_of_small (h : A6InnerLieSmall) : A6InnerOddLie := by
  rintro S _ _ _ hodd z hz ⟨e⟩
  have h2 := Nat.card_congr e.toEquiv
  rw [Nat.card_prod, natCard_multiplicative_zmod_two, alt6_card] at h2
  obtain ⟨D, hDn, hD⟩ := exists_normal_alt6_of_prod e
  exact h S hodd z hz (by omega) D hDn hD

theorem a6OuterLie_of_small (h : A6OuterLieSmall) : A6OuterLie := by
  rintro S _ _ _ hL σ hσ hout ⟨e⟩
  have h2 := Nat.card_congr e.toEquiv
  rw [alt6_card] at h2
  have eD : ↥(⊤ : Subgroup ↥(fixedSubgroup σ)) ≃* alternatingGroup (Fin 6) :=
    Subgroup.topEquiv.trans e
  have hn := h S hL σ hσ hout (by omega) ⊤ inferInstance ⟨eD⟩
    (fun x _ => Subgroup.mem_top x)
  have h3 := hn.2
  omega

theorem catZ2A6_of_small (hI : A6InnerLieSmall) (hO : A6OuterLieSmall) :
    CFSG.EvenSporadicStandard.CatNoAlmostSimpleZ2 (alternatingGroup (Fin 6)) :=
  catZ2A6_of_lie (a6InnerOddLie_of_small hI) (a6OuterLie_of_small hO)

end CFSG.ComponentClassification.CatFC
