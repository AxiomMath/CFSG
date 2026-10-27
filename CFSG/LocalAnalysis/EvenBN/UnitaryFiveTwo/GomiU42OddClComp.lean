module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddCl
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentE16Tags

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Comp

variable {S : Type} [Group S] [Finite S] {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)}

theorem U42Hyp.nonabelian (h : U42Hyp σ J) : ∃ x y : ↥J, x * y ≠ y * x := by
  by_contra hne
  push Not at hne
  haveI := h.isSimpleGroup
  letI : CommGroup ↥J := { (inferInstance : Group ↥J) with mul_comm := fun x y => hne x y }
  have hp := IsSimpleGroup.prime_card (α := ↥J)
  rw [h.card_J] at hp
  exact absurd hp (by norm_num)

theorem U42Hyp.isComponent (h : U42Hyp σ J) : CFSG.IsComponent J := by
  haveI := h.isSimpleGroup
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian).1,
    h.normal.isSubnormal⟩

theorem U42Hyp.center_eq_bot (h : U42Hyp σ J) : center ↥J = ⊥ := by
  haveI := h.isSimpleGroup
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian).2

theorem U42Hyp.card_centerQuotient (h : U42Hyp σ J) : Nat.card (↥J ⧸ center ↥J) = 25920 := by
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h.center_eq_bot).trans
    QuotientGroup.quotientBot).toEquiv, h.card_J]

end Comp

theorem u42_tri_mul_ne_four {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) : n * (n - 1) / 2 * f ≠ 4 := by
  rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | h4
  · intro h
    norm_num at h
    omega
  · intro h
    have h12 := CFSG.ComponentClassification.CatFC.e16_tags_mul_pred_twelve h4
    have : 6 ≤ n * (n - 1) / 2 := by omega
    nlinarith

theorem u42_lieModel_card_25920 (hO : LieOrderFormulasInput) {Y : Type} [Group Y]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 3 f) (hm : LieModel Y t n 3 f)
    (hY : Nat.card Y = 25920) : t = .PSp ∧ n = 2 ∧ f = 1 := by
  obtain ⟨-, hord, hfac⟩ := hO Y t n 3 f hadm hm
  rw [hY, factorization_25920] at hfac
  have h4 : lieSylowExponent t n * f = 4 := by simpa using hfac.symm
  have hf : 1 ≤ f := hadm.2.1
  obtain ⟨-, -, hrest⟩ := hadm
  cases t
  ·
    obtain ⟨hn, -, hne⟩ := hrest
    have h4' : n * (n - 1) / 2 * f = 4 := h4
    have hn2 : n = 2 := by
      by_contra hn2
      exact u42_tri_mul_ne_four (by omega) hf h4'
    subst hn2
    have hf4 : f = 4 := by simpa using h4'
    subst hf4
    exfalso
    have h1 : lieOrderNumerator .PSL 2 (3 ^ 4) = 531360 := by decide
    have h2 : lieOrderDivisor .PSL 2 (3 ^ 4) = 2 := by decide
    rw [h1, h2, hY] at hord
    omega
  ·
    obtain ⟨hn, -⟩ := hrest
    have h4' : n * (n - 1) / 2 * f = 4 := h4
    exact absurd h4' (u42_tri_mul_ne_four hn hf)
  ·
    obtain ⟨hn, -⟩ := hrest
    have h4' : n ^ 2 * f = 4 := h4
    have hn4 := CFSG.ComponentClassification.CatFC.e16_tags_sq_ge_four hn
    have hn2 : n = 2 := by
      by_contra hne
      have : 3 ≤ n := by omega
      nlinarith
    subst hn2
    exact ⟨rfl, rfl, by omega⟩
  ·
    obtain ⟨hn, -⟩ := hrest
    have h4' : n ^ 2 * f = 4 := h4
    exfalso
    have : 9 ≤ n ^ 2 := by nlinarith
    nlinarith
  ·
    have h4' : n * (n - 1) * f = 4 := h4
    have h12 := CFSG.ComponentClassification.CatFC.e16_tags_mul_pred_twelve (show 4 ≤ n from hrest)
    exfalso
    nlinarith
  ·
    have h4' : n * (n - 1) * f = 4 := h4
    have h12 := CFSG.ComponentClassification.CatFC.e16_tags_mul_pred_twelve (show 4 ≤ n from hrest)
    exfalso
    nlinarith
  · exfalso; have h4' : 6 * f = 4 := h4; omega
  · exfalso; have h4' : 24 * f = 4 := h4; omega
  · exfalso; have h4' : 36 * f = 4 := h4; omega
  · exfalso; have h4' : 63 * f = 4 := h4; omega
  · exfalso; have h4' : 120 * f = 4 := h4; omega
  · exfalso; have h4' : 36 * f = 4 := h4; omega
  · exfalso; have h4' : 12 * f = 4 := h4; omega
  · exfalso; have h4' : 2 * f = 4 := h4; obtain ⟨-, hp2, -⟩ := hrest; omega
  · exfalso; obtain ⟨-, -, -, h3f⟩ := hrest; have h4' : 3 * f = 4 := h4; omega
  · exfalso; obtain ⟨-, hp2, -⟩ := hrest; omega
  · exfalso; obtain ⟨-, hp2, -⟩ := hrest; omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
