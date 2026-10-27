module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFON
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCatHS
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporX
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23ONOutK3Main
public import CFSG.LocalAnalysis.SteinbergBSONInvolutionLocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34RSporHS

public section

namespace CFSG.ComponentClassification.GrSLit.HeldBalSpor

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor
open CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_mul_ne_mul_of_four_dvd {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (h4 : 4 ∣ Nat.card S) : ∃ a b : S, a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hc
  have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
    by_contra hab
    exact hc ⟨a, b, hab⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (dvd_trans (by norm_num) h4)
  have hN : (Subgroup.zpowers x).Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_inv_cancel_right]; exact hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h | h
  · have hx1 : x = 1 := by
      have hx' : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
      rwa [h, Subgroup.mem_bot] at hx'
    rw [hx1, orderOf_one] at hx
    omega
  · have hcard : Nat.card S = 2 := by
      rw [← Subgroup.card_top (G := S), ← h, Nat.card_zpowers, hx]
    rw [hcard] at h4
    omega

theorem exists_mul_ne_mul_of_isL34Type {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] {P : Subgroup S} (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    ∃ a b : S, a * b ≠ b * a :=
  exists_mul_ne_mul_of_four_dvd ((show 4 ∣ 20160 by norm_num).trans
    ((L34PF.dvd_card_of_isL34Type htype).trans (Subgroup.card_subgroup_dvd_card P)))

theorem card_center_eq_one_of_suz
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier .Suz) {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : Nat.card (center ↥P) = 1 := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Suz hna e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
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
  have hc := GSThmB.cf24CenterGe S (L34PF.isQuasisimple_of_simple hna) hZ2 ⟨eS⟩ σ
    (MulEquiv.ext fun y => h.1 y) P (hfix ▸ h.2.1) (by rw [hfix]; exact hcomp) hM
  rw [hZS, le_bot_iff, map_eq_bot_iff_of_injective _ P.subtype_injective] at hc
  rw [hc, Subgroup.card_bot]

theorem card_center_eq_four_of_ON_inner
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (e : S ≃* NativeSporadic.Carrier .ONan) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hcomp : IsComponent (P.subgroupOf (fixedSubgroup σ)))
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) {t : S} (ht : σ = MulAut.conj t)
    (ht2 : orderOf t = 2) : Nat.card (center ↥P) = 4 := by
  have hZP := L34PF.fusionZStar_eq_center_of_comp h hcomp htype
  have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
    rw [ht]
    ext x
    rw [mem_centralizer_singleton_iff]
    change t * x * t⁻¹ = x ↔ x * t = t * x
    rw [mul_inv_eq_iff_eq_mul]
    exact eq_comm
  set C := centralizer ({t} : Set S) with hCdef
  have hPC : P ≤ C := hfix ▸ h.2.1
  have hB : IsComponent (P.subgroupOf C) := by rw [← hfix]; exact hcomp
  obtain ⟨φ, hinj, hCmap⟩ := L34PF.exists_centralizer_map_eq_onM e ht2
  let ψ : ↥C ≃* ↥ONSchreier.onM :=
    (C.equivMapOfInjective φ hinj).trans (MulEquiv.subgroupCongr hCmap)
  have hB' : IsComponent ((P.subgroupOf C).map ψ.toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv ψ hB
  obtain ⟨hLM, hcardL, -, -, -, -⟩ := ONSchreier.at_on_perfect_derived_subgroup
  obtain ⟨hLq, -⟩ := LocalAnalysis.SteinbergBS.onL_isQuasisimple
  have hLq' : IsQuasisimple (ONSchreier.onL.subgroupOf ONSchreier.onM) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe ONSchreier.onL_le_M).symm hLq
  have hcomm : commutator ONSchreier.onM ≤ ONSchreier.onL.subgroupOf ONSchreier.onM := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, hLM, ← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map_of_mem _ hx
  have hBL := LocalAnalysis.SteinbergBS.component_eq_of_commutator_le hLq' hcomm hB'
  have hcardP : Nat.card P = 80640 := by
    calc Nat.card P = Nat.card (P.subgroupOf C) :=
          (Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv).symm
      _ = Nat.card ((P.subgroupOf C).map ψ.toMonoidHom) :=
          (Subgroup.card_map_of_injective ψ.injective).symm
      _ = Nat.card (ONSchreier.onL.subgroupOf ONSchreier.onM) := by rw [hBL]
      _ = Nat.card ONSchreier.onL :=
          Nat.card_congr (subgroupOfEquivOfLe ONSchreier.onL_le_M).toEquiv
      _ = 80640 := hcardL
  have h1 : Nat.card P = Nat.card (P ⧸ Open.fusionZStar P) * Nat.card (Open.fusionZStar P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [card_of_isL34Type htype, hZP, hcardP] at h1
  omega

theorem card_center_eq_four_of_ON
    (hONO : SolMax.ONOuterComponentsInput) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* NativeSporadic.Carrier .ONan) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (htype : IsL34Type (P ⧸ Open.fusionZStar P)) :
    Nat.card (center ↥P) = 4 := by
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by
    rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one
  have hcore := oddCore_fixedSubgroup_eq_bot_of_mulAut hna
    (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree Sporadic.ONOddCore.sporadicOddCoreFree_ONan hna
      e) hσ2
  obtain ⟨hcomp, ⟨eZ⟩⟩ := h.isComponent_of_oddCore hcore
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout'
  · obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    exact card_center_eq_four_of_ON_inner e h hcomp htype ht ht2
  · exfalso
    have hfix : fixedSubgroup σ = Sporadic.Schreier.fixSub σ := by
      ext x
      exact Iff.rfl
    set L := P.subgroupOf (fixedSubgroup σ) with hLdef
    set φ := MulEquiv.subgroupCongr hfix
    have hB : IsComponent (L.map φ.toMonoidHom) :=
      ⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (L.equivMapOfInjective φ.toMonoidHom φ.injective)).1 hcomp.1,
        Subgroup.IsSubnormal.map (f := φ.toMonoidHom) φ.surjective hcomp.2⟩
    have hcB := hONO S ⟨e⟩ σ (MulEquiv.ext fun y => h.1 y) hout' _ hB
    have eL := L.equivMapOfInjective φ.toMonoidHom φ.injective
    have hq : Nat.card (↥(L.map φ.toMonoidHom) ⧸ center ↥(L.map φ.toMonoidHom)) =
        Nat.card (↥P ⧸ Open.fusionZStar ↥P) := by
      rw [Nat.card_congr eZ.toEquiv]
      exact Nat.card_congr (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).symm.toEquiv
    rw [hq, card_of_isL34Type htype] at hcB
    omega

section Main

theorem sporadicL34ComponentsInput_holds :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → Blueprint.NativeSporadic.SporadicRep S →
      ∀ (σ : MulAut S) (P : Subgroup S), CatLeaf.ProperFixedComponent σ P →
        IsL34Type (P ⧸ Open.fusionZStar P) →
        (Nonempty (S ≃* Blueprint.NativeSporadic.Suz) ∧ Nat.card (center ↥P) = 1) ∨
          (Nonempty (S ≃* Blueprint.NativeSporadic.ON) ∧ Nat.card (center ↥P) = 4) ∨
          Nonempty (S ≃* Blueprint.NativeSporadic.He) := by
  intro S _ _ hs hsp σ P h htype
  have : IsSimpleGroup S := hs
  have hna := exists_mul_ne_mul_of_isL34Type htype
  obtain ⟨s, ⟨e⟩⟩ := hsp
  have hONO : SolMax.ONOuterComponentsInput :=
    SolMax.onOuterComponentsInput_of_local SolMax.ONOut.onOuterLocalInput_holds
  have key : ∀ {s : TauCeti.SporadicName}, HarrisLit.SporCompData s →
      (S ≃* NativeSporadic.Carrier s) → False :=
    fun hd e => L34PF.not_isL34Type_of_sporCompData hd hna e h htype
  cases s
  case J1 => exact (L34PF.false_of_J1 e htype).elim
  case J3 => exact (L34PF.false_of_J3 e htype).elim
  case M12 => exact (L34R.not_isL34Type_M12 e P htype).elim
  case J2 => exact (L34R.not_isL34Type_J2 e h htype).elim
  case HS => exact (L34Sec5S.false_of_hs_fixed e h htype).elim
  case He => exact Or.inr (Or.inr ⟨(e : S ≃* NativeSporadic.He)⟩)
  case Suz =>
    exact Or.inl ⟨⟨(e : S ≃* NativeSporadic.Suz)⟩, card_center_eq_one_of_suz hna e h htype⟩
  case ONan =>
    exact Or.inr (Or.inl ⟨⟨(e : S ≃* NativeSporadic.ON)⟩,
      card_center_eq_four_of_ON hONO hna e h htype⟩)
  case M11 => exact (key HarrisLit.sporCompData_M11 e).elim
  case M22 => exact (key HarrisLit.sporCompData_M22 e).elim
  case M23 => exact (key HarrisLit.sporCompData_M23 e).elim
  case M24 => exact (key HarrisLit.sporCompData_M24 e).elim
  case J4 => exact (key HarrisLit.sporCompData_J4 e).elim
  case McL => exact (key HarrisLit.sporCompData_McL e).elim
  case Ru => exact (key HarrisLit.sporCompData_Ru e).elim
  case Co1 => exact (key HarrisLit.sporCompData_Co1 e).elim
  case Co2 => exact (key HarrisLit.sporCompData_Co2 e).elim
  case Co3 => exact (key HarrisLit.sporCompData_Co3 e).elim
  case Fi22 => exact (key HarrisLit.sporCompData_Fi22 e).elim
  case Fi23 => exact (key HarrisLit.sporCompData_Fi23 e).elim
  case Fi24Prime => exact (key HarrisLit.sporCompData_Fi24Prime e).elim
  case HN => exact (key HarrisLit.sporCompData_HN e).elim
  case Ly => exact (key HarrisLit.sporCompData_Ly e).elim
  case Th => exact (key HarrisLit.sporCompData_Th e).elim
  case B => exact (key HarrisLit.sporCompData_B e).elim
  case M => exact (key HarrisLit.sporCompData_M e).elim

end Main

end CFSG.ComponentClassification.GrSLit.HeldBalSpor
