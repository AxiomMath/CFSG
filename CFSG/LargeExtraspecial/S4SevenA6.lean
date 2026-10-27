module

public import CFSG.LargeExtraspecial.S4SevenCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2

universe u

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem exists_spDer_apply_eq_of_eq_one (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {x y : V} (hxy : β x y = 1) :
    ∃ g ∈ spDer β hβ, g x = y := by
  obtain ⟨w, hw0, hxw, -⟩ := exists_ne_zero_perp_pair hnd h3 x x
  have hxy0 : x + y ≠ 0 := by
    intro h
    have : y = x := by
      have := congrArg (· + y) h
      simpa [add_assoc, vec_add_self] using this.symm
    rw [this, hβ.self_eq_zero] at hxy
    exact zero_ne_one hxy
  refine ⟨spTransvection β hβ (x + y) * spTransvection β hβ w,
    spTransvection_mul_mem_spDer hβ hxy0 hw0, ?_⟩
  have hw : spTransvection β hβ w x = x := by
    rw [spTransvection_apply, hxw, zero_smul, add_zero]
  rw [LinearEquiv.mul_apply, hw, spTransvection_add_apply hβ hxy]

theorem spDer_transitive (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g ∈ spDer β hβ, g x = y := by
  by_cases hxy : x = y
  · exact ⟨1, one_mem _, by rw [hxy]; rfl⟩
  by_cases h1 : β x y = 1
  · exact exists_spDer_apply_eq_of_eq_one hβ hnd h3 h1
  obtain ⟨w, hxw, hyw⟩ : ∃ w, β x w = 1 ∧ β y w = 1 := by
    have hx' : x ∉ Submodule.span (ZMod 2) {x + y, x + y} := by
      rw [Set.pair_eq_singleton]
      intro hmem
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
      rcases zmod2_eq_zero_or_eq_one k with rfl | rfl
      · rw [zero_smul] at hk
        exact hx hk.symm
      · rw [one_smul, add_eq_left] at hk
        exact hy hk
    obtain ⟨d, hd, -, hxd⟩ := exists_dual_triple hβ hnd hx'
    refine ⟨d, hxd, ?_⟩
    rw [map_add, LinearMap.add_apply, hxd] at hd
    exact (zmod2_eq_of_add_eq_zero hd).symm
  obtain ⟨g₁, hg₁, hg₁x⟩ := exists_spDer_apply_eq_of_eq_one hβ hnd h3 hxw
  obtain ⟨g₂, hg₂, hg₂w⟩ := exists_spDer_apply_eq_of_eq_one hβ hnd h3
    (show β w y = 1 by rw [isAlt_symm hβ, hyw])
  exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [LinearEquiv.mul_apply, hg₁x, hg₂w]⟩

end Abstract

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem not_a6Pair_of_card {t : S.O} (H : Hyp4 S g) (ht : t ∈ S.Lbar g)
    (hcard : Nat.card (LmodN S g t) = 2 ^ (finrank (ZMod 2) (Vt S g t) - 1)) :
    ¬ A6Pair (RmodN S g t) (LmodN S g t) (aV ht) := by
  rintro ⟨h4, β', hβ', hnd', -, -, hc, -, -⟩
  rw [card_spPointRadical hβ' hnd' (aV_ne_zero H ht), hcard, h4] at hc
  norm_num at hc

theorem not_a6Pair_of_linCase (H : Hyp4 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) : ¬ A6Pair (RmodN S g t) (LmodN S g t) (aV ht) :=
  not_a6Pair_of_card H ht (by rw [hL.LmodN_eq, card_centreGroup (aV_ne_zero H ht)])

theorem not_a6Pair_of_spCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} (hSp : SpCase H C ht ht1 hVQ) :
    ¬ A6Pair (RmodN S g t) (LmodN S g t) (aV ht) :=
  not_a6Pair_of_card H ht (by
    rw [hSp.LmodN_eq, card_spPointRadical (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) (aV_ne_zero H ht)])

theorem not_a6Pair_of_omegaCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} (hΩ : OmegaCase H C ht ht1 hVQ) :
    ¬ A6Pair (RmodN S g t) (LmodN S g t) (aV ht) := by
  rintro ⟨h4, β', hβ', hnd', hX, -⟩
  obtain ⟨v, hv0, hv⟩ := hΩ.not_transitive
  rw [commutator_isometryGroup_eq hβ' hnd'] at hX
  obtain ⟨x, hx, hxv⟩ := spDer_transitive hβ' hnd' (by omega) (aV_ne_zero H ht) hv0
  exact hv ⟨x, hX ▸ hx, hxv⟩

theorem timmesfeld_4_7_a_of_not_a6 (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hR : Rbar S g t ≠ S.Lbar g)
    (hP : ∀ hVQ : ¬ V S g t ≤ S.Qa g, ¬ PGL25Case H C ht ht1 hVQ)
    (hA : ∀ hVQ : ¬ V S g t ≤ S.Qa g, ¬ A6Case H C ht ht1 hVQ) :
    IsPGroup 2 (Nbar S g t) ∧ Nbar S g t = N0bar S g t ∧
      Nbar S g t = ⨆ X ∈ Dset S g t, X ⊓ Nbar S g t := by
  have key : DtEqConj S g t → NaturalPair (RmodN S g t) (LmodN S g t) (aV ht) →
      ¬ A6Pair (RmodN S g t) (LmodN S g t) (aV ht) →
      IsPGroup 2 (Nbar S g t) ∧ Nbar S g t = N0bar S g t ∧
        Nbar S g t = ⨆ X ∈ Dset S g t, X ⊓ Nbar S g t := by
    intro hD hpair hnA
    rcases Nbar_eq_N0bar_or hCE H C ht hD hpair with h | ⟨hA6, -⟩
    · refine ⟨h ▸ isPGroup_N0bar H ht, h, ?_⟩
      rw [← N0bar_eq_iSup_Dset H ht hD, h]
    · exact absurd hA6 hnA
  rcases timmesfeld_4_5 H hNo C ht ht1 with hR' | hL | ⟨hVQ, hSp | hA6 | hΩ | hPG⟩
  · exact absurd hR' hR
  · exact key (dtEqConj_of_linCase H hL) (naturalPair_of_linCase hL) (not_a6Pair_of_linCase H hL)
  · exact key (dtEqConj_of_transitive H ht hSp.transitive) (naturalPair_of_spCase H hNo C hSp)
      (not_a6Pair_of_spCase H C hSp)
  · exact absurd hA6 (hA hVQ)
  · exact key (dtEqConj_of_omegaCase H hNo C hΩ) (naturalPair_of_omegaCase H hNo C hΩ)
      (not_a6Pair_of_omegaCase H C hΩ)
  · exact absurd hPG (hP hVQ)

end CFSG.LargeExtraspecial.S4
