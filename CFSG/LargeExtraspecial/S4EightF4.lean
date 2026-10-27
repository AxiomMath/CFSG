module

public import CFSG.LargeExtraspecial.S4EightF3
public import CFSG.LargeExtraspecial.S4EightF2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem LmodN_eq_or_tau_not_mem (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g}
    (hcase : SpCase H C ht ht1 hVQ ∨ A6Case H C ht ht1 hVQ ∨ OmegaCase H C ht ht1 hVQ ∨
      PGL25Case H C ht ht1 hVQ) :
    LmodN S g t = spPointRadical (beta H C ht ht1 hVQ) (aV ht) ∨
      spTransvection _ (beta_isAlt H C ht ht1 hVQ) (aV ht) ∉ LmodN S g t := by
  rcases hcase with hSp | hA | hΩ | hP
  · exact Or.inl hSp.LmodN_eq
  · exact Or.inr hA.tau_not_mem
  · exact Or.inr (radConfig H C ht ht1 hVQ hNo hΩ.not_transitive).tau_not_mem
  · exact Or.inr hP.tau_not_mem

theorem card_eq_three_or_exists_beta_ne_zero (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g)
    {F : Subgroup S.O} (hFodd : Odd (Nat.card F)) (hF1 : F ≠ ⊥) (hFR : F ≤ Rbar S g t)
    (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
    (hCF : ∀ f ∈ F, (∀ l ∈ S.Lbar g, l * f = f * l) → f = 1) :
    Nat.card F = 3 ∨ ∃ hVQ : ¬ V S g t ≤ S.Qa g,
      (SpCase H C ht ht1 hVQ ∨ A6Case H C ht ht1 hVQ ∨ OmegaCase H C ht ht1 hVQ ∨
        PGL25Case H C ht ht1 hVQ) ∧
      ∃ f₁, ∃ hf₁ : f₁ ∈ F, ∃ f₂, ∃ hf₂ : f₂ ∈ F,
        beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁)) (orbV H.conj_mem ht (hFR hf₂)) ≠ 0 := by
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hcase⟩
  · exact absurd hR' hR
  · left
    refine card_eq_three_of_closed H hFodd hFR hLF hCF (fun f₁ hf₁ f₂ hf₂ hne => ?_) hF1
      fun l hl u hu => act_lin H ht hFR hL hl hu
    obtain ⟨y, hy, hyc⟩ := exists_move_lin H ht hFR hL hf₁ hf₂ hne
    exact exists_apply_eq_add H hFodd hLF hf₁ hf₂ hy hyc
  · by_cases hperp : ∀ f₁ (hf₁ : f₁ ∈ F) f₂ (hf₂ : f₂ ∈ F),
        beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁)) (orbV H.conj_mem ht (hFR hf₂)) = 0
    · left
      have hτ := LmodN_eq_or_tau_not_mem H hNo C hcase
      refine card_eq_three_of_closed H hFodd hFR hLF hCF (fun f₁ hf₁ f₂ hf₂ hne => ?_) hF1
        fun l hl u hu => act_perp H ht hFR C ht1 hVQ (fun f hf => ?_) hl hu
      · obtain ⟨y, hy, hyc⟩ := exists_move_perp H ht hFR C ht1 hVQ hτ hf₁ hf₂ hne
          (hperp f₁ hf₁ f₂ hf₂)
        exact exists_apply_eq_add H hFodd hLF hf₁ hf₂ hy hyc
      · have := hperp 1 (one_mem _) f hf
        have e : orbV H.conj_mem ht (hFR (one_mem F)) = aV ht := Subtype.ext rfl
        rwa [e] at this
    · right
      push Not at hperp
      exact ⟨hVQ, hcase, hperp⟩

end CFSG.LargeExtraspecial.S4
