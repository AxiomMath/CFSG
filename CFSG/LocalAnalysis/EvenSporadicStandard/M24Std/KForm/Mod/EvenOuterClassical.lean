module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.CatZ2S6Socle
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.EvenOuterArith
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.EvenOuterBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.EvenOuterPSp
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2EvenOuterOmega

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.RankOne

theorem z2s6_even_PSL (hO : LieOrderFormulasInput) {S : Type} [Group S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSL n 2 e) (hm : LieModel S .PSL n 2 e) {σ : MulAut S}
    {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) : Z2S6Socle S := by
  rcases psl_outer_fixed_rank hadm hm σ hdata.order_two hout with hfield | hgf | hgraph
  · obtain ⟨hadm', hm', -⟩ := hfield J hdata.isPComponent
    exact (lieModel_two_not_a6data hO hadm' hm' hdata.dvd_card_J hdata.not_two_pow_six_J).elim
  · obtain ⟨hadm', hm'⟩ := hgf J hdata.isPComponent
    exact (lieModel_two_not_a6data hO hadm' hm' hdata.dvd_card_J hdata.not_two_pow_six_J).elim
  · rcases hgraph with ⟨k, _, _, r, hk, hr1, ⟨-, hnr⟩, ⟨Φ⟩⟩ | hnone
    · obtain ⟨hr2, hg1⟩ :=
        sp_fixed_two_part hk hr1 hadm.2.1 Φ hdata.dvd_card hdata.not_two_pow_six
      subst hr2
      subst hg1
      rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
      · exact Or.inl (CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hm)
      · exact Or.inr (Or.inr (Or.inl hm))
    · exact (hnone J hdata.isPComponent).elim

theorem z2s6_even_PSU (hO : LieOrderFormulasInput) {S : Type} [Group S] {n e : ℕ}
    (hadm : StatedLieAdmissible .PSU n 2 e) (hm : LieModel S .PSU n 2 e) {σ : MulAut S}
    {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) : Z2S6Socle S := by
  rcases psu_outer_fixed_rank hadm hm σ hdata.order_two hout with
    ⟨k, _, _, r, hk, hr1, hnr, ⟨Φ⟩⟩ | hnone
  · obtain ⟨hr2, hg1⟩ :=
      sp_fixed_two_part hk hr1 hadm.2.1 Φ hdata.dvd_card hdata.not_two_pow_six
    subst hr2
    subst hg1
    rcases (by omega : n = 4 ∨ n = 5) with rfl | rfl
    · exact Or.inr (Or.inl hm)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hm)))
  · exact (hnone J hdata.isPComponent).elim

theorem z2s6_even_PSp (hO : LieOrderFormulasInput) {S : Type}
    [Group S] {n e : ℕ} (hadm : StatedLieAdmissible .PSp n 2 e) (hm : LieModel S .PSp n 2 e)
    {σ : MulAut S} {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) : Z2S6Socle S := by
  rcases psp_outer_fixed_rank_even hadm hm σ hdata.order_two hout with
    ⟨k, _, _, hk, hpar, ⟨Φ⟩⟩ | ⟨-, hadmB, hmB⟩
  · have hg : 1 ≤ e / 2 := by
      by_contra h
      have h0 : e / 2 = 0 := by omega
      rw [h0, pow_zero] at hk
      have := (Finite.one_lt_card_iff_nontrivial (α := k)).2 inferInstance
      omega
    obtain ⟨hr2, hg1⟩ := sp_fixed_two_part hk (by have := hadm.2.2.1; omega) hg Φ hdata.dvd_card
      hdata.not_two_pow_six
    subst hr2
    obtain rfl : e = 2 := by omega
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
  · exact (lieModel_two_not_a6data hO hadmB hmB hdata.dvd_card hdata.not_two_pow_six).elim

theorem z2s6_even_Omega (hO : LieOrderFormulasInput) {t : StatedLieTag}
    (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {S : Type} [Group S] {n e : ℕ}
    (hadm : StatedLieAdmissible t n 2 e) (hm : LieModel S t n 2 e) {σ : MulAut S}
    {J : Subgroup ↥(fixedSubgroup σ)} (hdata : Z2S6ModData S σ J)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) : Z2S6Socle S := by
  have hn4 : 4 ≤ n := by rcases ht with rfl | rfl <;> exact hadm.2.2
  rcases omega_family_fixed_rank ht hadm hm σ hdata.order_two hout with hsp | hom
  · rcases hsp with ⟨k, _, _, r, hk, hr1, hrn, ⟨Φ⟩⟩ | hnone
    · obtain ⟨hr2, -⟩ := sp_fixed_two_part hk hr1 hadm.2.1 Φ hdata.dvd_card hdata.not_two_pow_six
      exfalso
      omega
    · exact (hnone J hdata.isPComponent).elim
  · obtain ⟨t', n', f', -, hadm', hm'⟩ := hom J hdata.isPComponent
    exact (lieModel_two_not_a6data hO hadm' hm' hdata.dvd_card_J hdata.not_two_pow_six_J).elim

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
