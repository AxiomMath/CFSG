module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34He
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineL34HS
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineJTwo
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoONLocal
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataA
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporDataB
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporX
public import CFSG.LocalAnalysis.OddStandard.AltStdSmallSylow
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupNum
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt

public section

namespace CFSG.SeitzReduction.SporadicRefine

open CFSG Subgroup CFSG.Blueprint
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)

section Alt

theorem card_alt_seven {Y : Type} [Group Y] (e : Y ≃* alternatingGroup (Fin 7)) :
    Nat.card Y = 2520 := by
  rw [OddStandard.AltStdSec.card_eq_of_equiv_alt (by norm_num) e]
  decide

theorem card_quotient_center_alt_seven {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 7)) : Nat.card (Y ⧸ center Y) = 2520 := by
  have hz : center Y = ⊥ := OddStandard.AltStdSec.center_eq_bot_of_alt (by norm_num) e
  rw [Nat.card_congr
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).toEquiv]
  exact card_alt_seven e

theorem smallCentralQuotient_of_alt_seven {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin 7)) :
    ComponentClassification.RestrictedStd.SmallCentralQuotient Y := by
  have hz : center Y = ⊥ := OddStandard.AltStdSec.center_eq_bot_of_alt (by norm_num) e
  exact Or.inr (Or.inl
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e⟩)

theorem card_centralizer_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    Nat.card (centralizer ({x} : Set X)) = Nat.card (centralizer ({e x} : Set Y)) := by
  have hmap : (centralizer ({x} : Set X)).map e.toMonoidHom = centralizer ({e x} : Set Y) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hz
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul e z x, hz, map_mul]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [mem_centralizer_singleton_iff] at hy
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

theorem card_centralizer_alt_seven {c : alternatingGroup (Fin 7)} (hc2 : c * c = 1)
    (hc1 : c ≠ 1) : Nat.card (centralizer ({c} : Set (alternatingGroup (Fin 7)))) = 24 := by
  classical
  set c' : Equiv.Perm (Fin 7) := (c : Equiv.Perm (Fin 7)) with hc'
  have hc2' : c' * c' = 1 := congrArg Subtype.val hc2
  have hc1' : c' ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hcA : c' ∈ alternatingGroup (Fin 7) := c.2
  have hs := OddStandard.AltStdSec.card_support_eq_two_mul_card_cycleType hc2'
  have hsl : c'.support.card ≤ 7 := by
    have := Finset.card_le_univ c'.support
    rwa [Fintype.card_fin] at this
  have hk0 : Multiset.card c'.cycleType ≠ 0 := by
    intro h0
    rw [h0, mul_zero, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hs
    exact hc1' hs
  have hkeven : Even (Multiset.card c'.cycleType) := by
    have hsg := OddStandard.AltStdSmall.sign_eq_neg_one_pow_of_mul_self hc2'
    rw [Equiv.Perm.mem_alternatingGroup] at hcA
    rw [hcA] at hsg
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    rw [hodd.neg_one_pow] at hsg
    exact absurd hsg (by decide)
  have hk : Multiset.card c'.cycleType = 2 := by
    obtain ⟨j, hj⟩ := hkeven
    omega
  have hS := OddStandard.AltStdSec.nat_card_centralizer_of_mul_self hc2'
  rw [hk, Fintype.card_fin] at hS
  have h2 := OddStandard.AltStdSmall.two_mul_card_centralizer_inf_alternating hc2' hc1'
  rw [hS] at h2
  have hmap : (centralizer ({c} : Set (alternatingGroup (Fin 7)))).map
      (alternatingGroup (Fin 7)).subtype =
      alternatingGroup (Fin 7) ⊓ centralizer ({c'} : Set (Equiv.Perm (Fin 7))) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
      show (y : Equiv.Perm (Fin 7)) ∈ centralizer ({c'} : Set (Equiv.Perm (Fin 7)))
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hy
    · intro hx
      obtain ⟨hxA, hxc⟩ := Subgroup.mem_inf.1 hx
      refine ⟨⟨x, hxA⟩, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff] at hxc
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact Subtype.ext hxc
  have h3 : Nat.card (centralizer ({c} : Set (alternatingGroup (Fin 7)))) =
      Nat.card ↥(alternatingGroup (Fin 7) ⊓ centralizer ({c'} : Set (Equiv.Perm (Fin 7)))) := by
    rw [← hmap, Subgroup.card_map_of_injective (alternatingGroup (Fin 7)).subtype_injective]
  have h48 : (7 - 2 * 2).factorial * 2 ^ 2 * (2 : ℕ).factorial = 48 := by decide
  rw [h48] at h2
  omega

end Alt


theorem false_of_compData_alt_seven {s : TauCeti.SporadicName}
    (hd : ComponentClassification.HarrisLit.SporCompData s) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier s)
    {σ : MulAut S} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) {B : Subgroup (fixedSubgroup σ)}
    (hB : IsComponent B) (eB : B ≃* alternatingGroup (Fin 7)) : False := by
  rcases ComponentClassification.CatLeaf.exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  · obtain ⟨B', hB', ⟨φ⟩⟩ := OddStandard.AltStdSec.isComponent_map_fixedSubgroup_conj ht hB
    exact hd.inner S inferInstance hna ⟨e⟩ t
      (OddStandard.AltStdSec.lookup_orderOf_eq_two_of_conj hna hσ2 hσ1 ht) B' hB'
      (smallCentralQuotient_of_alt_seven (φ.trans eB))
  · have hfix : fixedSubgroup σ = fixSub σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix
    exact hd.outer S inferInstance hna ⟨e⟩ σ hσ2 hout (B.map φ.toMonoidHom)
      (LocalCores.isComponent_map_mulEquiv φ hB)
      (smallCentralQuotient_of_alt_seven
        ((B.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eB))

theorem on_outer_false_of_alt_seven
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.ON)
    {τ : MulAut S} (hτ : orderOf τ = 2) (hout : τ ∉ (MulAut.conj : S →* MulAut S).range)
    {D : Subgroup (fixedSubgroup τ)} (hN : D.Normal) (eD : D ≃* alternatingGroup (Fin 7))
    (hcard : Nat.card (fixedSubgroup τ) ∣ 10080) : False := by
  classical
  have := hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDcard : Nat.card D = 2520 := card_alt_seven eD
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 (by rw [hDcard]; norm_num)
  set t : S := ((d : fixedSubgroup τ) : S) with htdef
  have ht : orderOf t = 2 := by rw [htdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hd]
  have hτt : τ t = t := (d : fixedSubgroup τ).2
  have hdvd := RankOne.on_outer_card_dvd e hτ hout ht hτt
  set H : Subgroup (fixedSubgroup τ) :=
    centralizer ({(d : fixedSubgroup τ)} : Set (fixedSubgroup τ)) with hH
  have hmap : H.map (fixedSubgroup τ).subtype = fixedSubgroup τ ⊓ centralizer ({t} : Set S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hy
      show (y : S) ∈ centralizer ({t} : Set S)
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hy
    · intro hx
      obtain ⟨hxC, hxt⟩ := Subgroup.mem_inf.1 hx
      refine ⟨⟨x, hxC⟩, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff] at hxt
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact Subtype.ext hxt
  have hNH : Nat.card ↥(fixedSubgroup τ ⊓ centralizer ({t} : Set S)) = Nat.card H := by
    rw [← hmap, Subgroup.card_map_of_injective (fixedSubgroup τ).subtype_injective]
  rw [hNH] at hdvd
  have hHD : H.subgroupOf D = centralizer ({d} : Set D) := by
    ext x
    rw [mem_subgroupOf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hd2 : d * d = 1 := by rw [← pow_two, ← hd, pow_orderOf_eq_one]
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hd
    omega
  have h24 : Nat.card (H.subgroupOf D) = 24 := by
    rw [hHD, card_centralizer_congr eD d]
    refine card_centralizer_alt_seven ?_ ?_
    · rw [← map_mul, hd2, map_one]
    · exact fun h1 => hd1 (eD.injective (h1.trans (map_one eD).symm))
  have hHDmap : Nat.card ↥(H ⊓ D) = 24 := by
    rw [← subgroupOf_map_subtype, Subgroup.card_map_of_injective D.subtype_injective, h24]
  have h24H : 24 ∣ Nat.card H := by
    rw [← hHDmap]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hidx : H.relIndex D = 105 := by
    have h := (H.subgroupOf D).card_mul_index
    rw [h24, hDcard] at h
    show (H.subgroupOf D).index = 105
    omega
  have hle : H.relIndex D ≤ H.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := H) (le_top : D ≤ ⊤)
      (by rw [relIndex_top_right]; exact index_ne_zero_of_finite)
    rwa [relIndex_top_right] at h
  have hCH := H.card_mul_index
  have hCle : Nat.card (fixedSubgroup τ) ≤ 10080 := Nat.le_of_dvd (by norm_num) hcard
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have h105 : Nat.card H * 105 ≤ Nat.card (fixedSubgroup τ) := by
    rw [← hCH]
    exact Nat.mul_le_mul_left _ (by rw [← hidx]; exact hle)
  rcases hdvd with ⟨k, hk⟩ | ⟨k, hk⟩ | ⟨k, hk⟩
  · omega
  · obtain ⟨j, hj⟩ := h24H
    omega
  ·
    have h72 : Nat.card H = 72 := by
      obtain ⟨j, hj⟩ := h24H
      omega
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 2)
      (by rw [h72]; norm_num)
    have hQ : Nat.card (fixedSubgroup τ ⧸ D) ∣ 4 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup D
      rw [hDcard] at h
      have h' : Nat.card (fixedSubgroup τ ⧸ D) * 2520 ∣ 4 * 2520 := by
        rw [← h, show (4 * 2520 : ℕ) = 10080 by norm_num]
        exact hcard
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h'
    have hPD : ∀ p ∈ P, ((p : H) : fixedSubgroup τ) ∈ D := by
      intro p hp
      have h9 : orderOf p ∣ 9 := by
        have := Subgroup.orderOf_dvd_natCard P hp
        rwa [hP] at this
      set x : fixedSubgroup τ := ((p : H) : fixedSubgroup τ) with hx
      have hq1 : orderOf (QuotientGroup.mk' D x) ∣ 9 :=
        (orderOf_map_dvd (QuotientGroup.mk' D) x).trans ((orderOf_map_dvd H.subtype p).trans h9)
      have hq2 : orderOf (QuotientGroup.mk' D x) ∣ 4 := (_root_.orderOf_dvd_natCard _).trans hQ
      have hq := Nat.dvd_gcd hq1 hq2
      rw [show Nat.gcd 9 4 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hq
      exact hq
    have hle' : P.map H.subtype ≤ H ⊓ D := by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨p.2, hPD p hp⟩
    have h9 := Subgroup.card_dvd_of_le hle'
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP, hHDmap] at h9
    norm_num at h9


theorem false_of_sporadic_alt_seven {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hsp : NativeSporadic.SporadicRep S) {τ : MulAut S}
    (hτ : orderOf τ = 2) {D : Subgroup (fixedSubgroup τ)} (hD : IsComponent D)
    (eD : D ≃* alternatingGroup (Fin 7)) (hcard : Nat.card (fixedSubgroup τ) ∣ 10080)
    (hsmall : FixedCentralizerTwoSmall τ D) : False := by
  have := hS
  have hτ2 : τ * τ = 1 := by rw [← sq, ← hτ, pow_orderOf_eq_one]
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    omega
  have hDcard : Nat.card D = 2520 := card_alt_seven eD
  have hdvdC : 2520 ∣ Nat.card (fixedSubgroup τ) := hDcard ▸ card_subgroup_dvd_card D
  have hdvdS : 2520 ∣ Nat.card S := hdvdC.trans (card_subgroup_dvd_card _)
  obtain ⟨s, ⟨e⟩⟩ := hsp
  cases s
  case M12 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.card_M12] at hdvdS
    norm_num at hdvdS
  case J1 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J1.card_J1] at hdvdS
    norm_num at hdvdS
  case J3 =>
    rw [(Nat.card_congr e.toEquiv).trans Sporadic.J3.card_J3] at hdvdS
    norm_num at hdvdS
  case J2 =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      have hu := orderOf_eq_two_of_conj_of_simple hS hna hτ
      rw [Nat.card_congr (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizerOf u)).toEquiv]
        at hdvdC
      rcases j2_card_centralizer e hu with h | h <;> rw [h] at hdvdC <;> norm_num at hdvdC
    · rw [j2_card_fixedSubgroup_outer e hτ hin] at hdvdC
      norm_num at hdvdC
  case HS =>
    obtain ⟨r, hr, ⟨φ⟩⟩ := hs_fixedSubgroup_rows e hτ
    obtain ⟨-, -, -, hrows, -, -, -, -⟩ := hs_involution_centralizers
    have hcardC := (hrows r hr).2.2.2.2.1
    rw [Nat.card_congr φ.toEquiv, hcardC] at hdvdC hcard
    rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h | ⟨-, -, h, -⟩ | ⟨-, h⟩ | h <;>
      rw [h] at hdvdC hcard <;> revert hdvdC hcard <;> decide
  case He =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      exact he_inner_not_twoSmall e (orderOf_eq_two_of_conj_of_simple hS hna hτ) hD hsmall
    · rw [he_outer_card_fixedSubgroup e hτ hin] at hcard
      norm_num at hcard
  case Suz =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      obtain ⟨B', hB', ⟨φ⟩⟩ := OddStandard.AltStdSec.isComponent_map_fixedSubgroup_conj rfl hD
      have h := Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e u
        (orderOf_eq_two_of_conj_of_simple hS hna hτ) B' hB'
      rw [card_quotient_center_alt_seven (φ.trans eD)] at h
      norm_num at h
    · rcases suz_outer_card_fixedSubgroup e hτ hin with h | h <;> rw [h] at hdvdC hcard <;>
        revert hdvdC hcard <;> decide
  case ONan =>
    by_cases hin : τ ∈ (MulAut.conj : S →* MulAut S).range
    · obtain ⟨u, rfl⟩ := hin
      obtain ⟨B', hB', ⟨φ⟩⟩ := OddStandard.AltStdSec.isComponent_map_fixedSubgroup_conj rfl hD
      have h :=
        Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
          ⟨e⟩ u (orderOf_eq_two_of_conj_of_simple hS hna hτ) B' hB'
      rw [card_quotient_center_alt_seven (φ.trans eD)] at h
      norm_num at h
    · exact on_outer_false_of_alt_seven e hτ hin
        (RankOne.normal_of_isComponent_of_twoSmall hD hsmall) eD hcard
  case M11 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M11 hna e
      hτ2 hτ1 hD eD
  case M22 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M22 hna e
      hτ2 hτ1 hD eD
  case M23 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M23 hna e
      hτ2 hτ1 hD eD
  case M24 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M24 hna e
      hτ2 hτ1 hD eD
  case J4 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_J4 hna e
      hτ2 hτ1 hD eD
  case McL =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_McL hna e
      hτ2 hτ1 hD eD
  case Ru =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Ru hna e
      hτ2 hτ1 hD eD
  case Co1 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Co1 hna e
      hτ2 hτ1 hD eD
  case Co2 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Co2 hna e
      hτ2 hτ1 hD eD
  case Co3 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Co3 hna e
      hτ2 hτ1 hD eD
  case Fi22 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Fi22 hna e
      hτ2 hτ1 hD eD
  case Fi23 =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Fi23 hna e
      hτ2 hτ1 hD eD
  case Fi24Prime =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Fi24Prime
      hna e hτ2 hτ1 hD eD
  case HN =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_HN hna e
      hτ2 hτ1 hD eD
  case Ly =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Ly hna e
      hτ2 hτ1 hD eD
  case Th =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_Th hna e
      hτ2 hτ1 hD eD
  case B =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_B hna e
      hτ2 hτ1 hD eD
  case M =>
    exact false_of_compData_alt_seven ComponentClassification.HarrisLit.sporCompData_M hna e
      hτ2 hτ1 hD eD

end CFSG.SeitzReduction.SporadicRefine
