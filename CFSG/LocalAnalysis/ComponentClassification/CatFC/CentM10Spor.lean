module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2A6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.CatFC

open Subgroup CFSG CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


private theorem exists_normal_alt6_map {G H : Type} [Group G] [Group H] (φ : G ≃* H)
    (D : Subgroup G) [D.Normal] (eD : ↥D ≃* alternatingGroup (Fin 6)) :
    ∃ D' : Subgroup H, D'.Normal ∧ Nonempty (↥D' ≃* alternatingGroup (Fin 6)) :=
  ⟨D.map φ.toMonoidHom, Subgroup.Normal.map ‹D.Normal› φ.toMonoidHom φ.surjective,
    ⟨(Subgroup.equivMapOfInjective D φ.toMonoidHom φ.injective).symm.trans eD⟩⟩

theorem spor_inner_false {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) {z : S} (hz : orderOf z = 2)
    (hcard : Nat.card ↥(centralizer ({z} : Set S)) = 1440)
    (D : Subgroup ↥(centralizer ({z} : Set S))) [D.Normal]
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) : False := by
  have hI : Function.Injective (MulAut.conj : S →* MulAut S) :=
    CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hna
  have hσ : orderOf (MulAut.conj z : MulAut S) = 2 :=
    (orderOf_injective (MulAut.conj : S →* MulAut S) hI z).trans hz
  have hσr : (MulAut.conj z : MulAut S) ∈ (MulAut.conj : S →* MulAut S).range :=
    MonoidHom.mem_range.mpr ⟨z, rfl⟩
  have hfix : fixedSubgroup (MulAut.conj z : MulAut S) = centralizer ({z} : Set S) :=
    CFSG.SeitzReduction.SporadicRefine.fixedSubgroup_conj_eq_centralizerOf z
  obtain ⟨eD⟩ := hD
  obtain ⟨D', hDn', ⟨eD'⟩⟩ :=
    exists_normal_alt6_map (MulEquiv.subgroupCongr hfix).symm D eD
  haveI := hDn'
  have hcomp : CFSG.IsComponent D' := isComponent_of_alt6 D' eD'
  have hcard360 := card_quotient_center_alt6 eD'
  rcases sporadic_comp_360 hS hna e hσ hcomp hcard360 with ⟨rfl, -⟩ | ⟨-, hout⟩
  ·
    rcases CFSG.EvenSporadicStandard.HSStd.Zassenhaus.card_centralizer_of_involution_hs
      ⟨e⟩ z hz with h1 | h1 <;> omega
  ·
    exact hout hσr

theorem spor_outer_false {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {s : TauCeti.SporadicName}
    (e : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range)
    (hcard : Nat.card ↥(fixedSubgroup σ) = 360 ∨ Nat.card ↥(fixedSubgroup σ) = 720)
    (D : Subgroup ↥(fixedSubgroup σ)) [D.Normal]
    (hD : Nonempty (↥D ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨eD⟩ := hD
  have hcomp : CFSG.IsComponent D := isComponent_of_alt6 D eD
  have hcard360 := card_quotient_center_alt6 eD
  rcases sporadic_comp_360 hS hna e hσ hcomp hcard360 with ⟨rfl, hin⟩ | ⟨rfl, -⟩
  ·
    exact hout hin
  ·
    have h1 := he_outer_fixedSubgroup_card e hσ hout
    rcases hcard with h | h <;> omega

end CFSG.ComponentClassification.CatFC
