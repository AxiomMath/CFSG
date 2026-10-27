module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73ClBridge
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Main
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorGraphField
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorInner
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorOrthogonal
public import CFSG.LocalAnalysis.ComponentClassification.OddSelectorSplitFour

public section

namespace CFSG.GH74.GLS.IVK

open CFSG CFSG.Blueprint Subgroup CFSG.GH74.Uniqueness.Bender
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog

theorem linear_selector_five_false' {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal]
    (hCW : centralizer (W : Set A) = ⊥) {a : A} (ha : orderOf a = 2) {L : Subgroup A}
    (hLW : L ≤ W) (hL : CFSG.Assembly.IsComponentOf L (centralizer ({a} : Set A)))
    {p f : ℕ} (hp2 : p ≠ 2)
    (hsrc : StatedClassicalModel (L ⧸ center L) .PSL 2 p f ∨
      Nonempty (L ⧸ center L ≃* alternatingGroup (Fin 7)) ∨
      StatedClassicalModel (L ⧸ center L) .PSL 3 2 2)
    (hrank : Odd (Nat.card (center L)))
    {m ℓ e : ℕ} (hm : 5 ≤ m) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) {k : Type} [Field k]
    (hk : Nat.card k = ℓ ^ e) (φ : W ≃* projectiveSL m k) : False := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact pow_ne_zero _ hℓ.ne_zero)
  have hm3 : 3 ≤ m := by omega
  have hm4 : 4 ≤ m := by omega
  have hZ := center_projectiveSL_eq_bot (k := k) hm3
  obtain ⟨ρ, hinj, hρW, -, -⟩ := socle_extension hCW φ hZ
  obtain ⟨-, -, -, hL₁⟩ := socle_images φ hinj hρW hLW hL
  obtain ⟨-, hform⟩ := automorphism_generation (K := k) hm3
  obtain ⟨B, τ, ε, hε, hρa⟩ := hform (ρ a)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      obtain ⟨-, -, -, hm4'⟩ :=
        inner_case_reduction ha hm4 hℓ hℓ2 he hk hinj hL₁ hρa hp2 hsrc (fun _ => Or.inr hrank)
      omega
    · exact field_case_false ha hm3 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc
  · rw [pow_one] at hρa
    by_cases hτ : τ = 1
    · subst hτ
      rw [map_one, mul_one] at hρa
      have hα2 : (conjAut m k B * dualAut m k) ^ 2 = 1 := by
        rw [← hρa, ← map_pow, ← ha, pow_orderOf_eq_one, map_one]
      rcases transpose_eq_or_eq_neg_of_pureGraph hm3 B hα2 with hB | hB
      · exact orthogonal_case_false hm hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
      · exact symplectic_case_false hm4 hℓ hℓ2 he hk hinj hL₁ hρa hB hp2 hsrc
    · exact graph_field_case_false ha hm4 hℓ hℓ2 he hk hinj hL₁ hτ hρa hp2 hsrc

variable {N : Type} [Group N] [Finite N] {L K Q : Subgroup N}

theorem ivk73_l5 (p f : ℕ)
    (hp : p.Prime) (hf : 1 ≤ f) (hmod : p ^ f % 4 = 3) :
    Ivk73Empty (fun X _ => LieModel X .PSL 5 p f) := by
  intro N _ _ L K Q h hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : Even (2 ^ f) := Nat.even_pow.2 ⟨even_two, by omega⟩
    have := Nat.even_iff.1 h2
    omega
  obtain ⟨u, hu2, huC⟩ := h.exists_involution
  have hcomp := h.isComponentOf_centralizer hu2 huC
  obtain ⟨p', f', hp2', hsrc⟩ := h.exists_hsrc
  have hodd := odd_center_K h.kbar_cases
  have := h.normal
  have hCW := h.centralizer_eq_bot
  obtain ⟨⟨hr, hf', -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := Generic.S45.LQ.stated_of_lieModel_PSL hm
  let φ : ↥L ≃* projectiveSL 5 F :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
  exact linear_selector_five_false' (W := L) hCW hu2 h.K_le hcomp hp2' hsrc hodd (le_refl 5) hr
    hp2 hf' hF φ

end CFSG.GH74.GLS.IVK
