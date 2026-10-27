module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFBase
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporData
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafSpor
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7CF24Main
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases

public section

namespace CFSG.ComponentClassification.GrSLit.L34PF

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms

theorem not_isL34Type_of_sporCompData {s : TauCeti.SporadicName} (hd : HarrisLit.SporCompData s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier s) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) : ¬ IsL34Type (P ⧸ Open.fusionZStar P) := by
  intro hL
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree hd.oddCore hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hsL : SmallCentralQuotient L :=
    Or.inr (Or.inr (LieType.CurtisTits.lieModel_of_mulEquiv eZ hL))
  have key : ∀ {F : Subgroup S} (hF : fixedSubgroup σ = F),
      IsComponent (L.map (MulEquiv.subgroupCongr hF).toMonoidHom) ∧
        SmallCentralQuotient (L.map (MulEquiv.subgroupCongr hF).toMonoidHom) := by
    intro F hF
    set φ := MulEquiv.subgroupCongr hF
    exact ⟨⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
      Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩,
      smallCentralQuotient_of_mulEquiv (L.equivMapOfInjective φ.toMonoidHom φ.injective).symm
        hsL⟩
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      ext x
      rw [mem_centralizer_singleton_iff]
      change t * x * t⁻¹ = x ↔ x * t = t * x
      rw [mul_inv_eq_iff_eq_mul]
      exact eq_comm
    obtain ⟨hB, hsB⟩ := key hfix
    exact hd.inner S inferInstance hna ⟨e⟩ t ht2 _ hB hsB
  · have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
      ext x
      exact Iff.rfl
    obtain ⟨hB, hsB⟩ := key hfix
    exact hd.outer S inferInstance hna ⟨e⟩ σ (MulEquiv.ext fun y => h.1 y) hout' _ hB hsB

theorem false_of_not_dvd_card {S : Type} [Group S] [Finite S]
    {P : Subgroup S} (htype : IsL34Type (P ⧸ Open.fusionZStar P))
    (hS : ¬ 20160 ∣ Nat.card S) : False :=
  hS ((dvd_card_of_isL34Type htype).trans (Subgroup.card_subgroup_dvd_card P))

theorem false_of_J1 {S : Type}
    [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J1) {P : Subgroup S}
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : False := by
  refine false_of_not_dvd_card htype ?_
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (NativeSporadic.Carrier .J1) = Nat.card NativeSporadic.J1 from rfl,
    Sporadic.J1.card_J1]
  decide

theorem false_of_J3 {S : Type}
    [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J3) {P : Subgroup S}
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : False := by
  refine false_of_not_dvd_card htype ?_
  rw [Nat.card_congr e.toEquiv,
    show Nat.card (NativeSporadic.Carrier .J3) = Nat.card NativeSporadic.J3 from rfl,
    Sporadic.J3.card_J3]
  decide

theorem fusionZStar_eq_center_of_comp {S : Type} [Group S]
    [Finite S] {σ : MulAut S} {P : Subgroup S} (h : ProperFixedComponent σ P)
    (hcomp : IsComponent (P.subgroupOf (fixedSubgroup σ)))
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Open.fusionZStar P = center P := by
  have eP := subgroupOfEquivOfLe h.2.1
  have hq : IsQuasisimple P := (LocalAnalysis.ComponentInitial.isQuasisimple_congr eP).1 hcomp.1
  refine CatLeaf.fusionZStar_eq_center_of_quasisimple hq ?_
  intro hO
  have hc := pPrimeCore_coprime_card (p := 2) (G := P)
  rw [hO, Subgroup.card_top] at hc
  exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl
    ((show 2 ∣ 20160 by norm_num).trans (dvd_card_of_isL34Type htype)) hc

theorem rank_le_one_of_suz
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .Suz) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    pRank 2 ↥(Open.fusionZStar P) ≤ 1 := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Suz hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  have hZP := fusionZStar_eq_center_of_comp h hcomp htype
  have hZS : center S = ⊥ := center_eq_bot_of_simple hna
  have hZ2 : IsPGroup 2 (center S) := by rw [hZS]; exact IsPGroup.of_bot
  let eS : S ⧸ center S ≃* NativeSporadic.Suz :=
    ((QuotientGroup.quotientMulEquivOfEq hZS).trans QuotientGroup.quotientBot).trans e
  have hfix : CatFactsL4U4.OutInv.fixSub σ = fixedSubgroup σ := Subgroup.ext fun _ => Iff.rfl
  have eP := subgroupOfEquivOfLe h.2.1
  let f : ↥(P.subgroupOf (fixedSubgroup σ)) ⧸ center ↥(P.subgroupOf (fixedSubgroup σ)) ≃*
      ↥P ⧸ center ↥P := QuotientGroup.congr _ _ eP (Subgroup.map_center_eq eP)
  have hM : LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 :=
    LieType.CurtisTits.lieModel_of_mulEquiv (eZ.trans f) htype
  have hc := GSThmB.cf24CenterGe S (isQuasisimple_of_simple hna) hZ2 ⟨eS⟩ σ
    (MulEquiv.ext fun y => h.1 y) P (hfix ▸ h.2.1) (by rw [hfix]; exact hcomp) hM
  rw [hZS, le_bot_iff, map_eq_bot_iff_of_injective _ P.subtype_injective] at hc
  rw [hZP, hc, pRank_two_eq_zero_of_eq_bot rfl]
  exact Nat.zero_le 1

end CFSG.ComponentClassification.GrSLit.L34PF
