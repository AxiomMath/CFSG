module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitInnerFour
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitONanFixedLayerInv
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Core
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceTypes

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Blueprint.NativeSporadic (IsSporadic)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem oddIn_comm_of_inner_four_on
    {P : Subgroup G} (hperf : ⁅P, P⁆ = P) (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan)
    {x : G} (hxP : x ∈ P) (hx : orderOf x = 2)
    (hB : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ = ⊥) :
    ∀ u ∈ oddIn P, ∀ l ∈ P, u * l = l * u := by
  obtain ⟨y, hygs, hy2, hyx⟩ := exists_involution_gsFixedLayer_on hON hxP hx
  have hyinf := gsFixedLayer_le_inf P x hygs
  have hyP : y ∈ P := (Subgroup.mem_inf.mp hyinf).1
  have hyx_comm : y * x = x * y :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyinf).2
  let U : Subgroup ↥P := pPrimeCore 2 ↥P
  haveI : U.Normal := CFSG.pPrimeCore_normal
  let x' : ↥P := ⟨x, hxP⟩
  let y' : ↥P := ⟨y, hyP⟩
  have hx' : orderOf x' = 2 := (Subgroup.orderOf_mk x hxP).trans hx
  have hy' : orderOf y' = 2 := (Subgroup.orderOf_mk y hyP).trans hy2
  have hxy' : x' * y' = y' * x' := by
    apply Subtype.ext
    change x * y = y * x
    exact hyx_comm.symm
  have hne' : x' ≠ y' := by
    intro h
    exact hyx (congrArg Subtype.val h).symm
  have hfix : ∀ u ∈ U, x' * u = u * x' → y' * u = u * y' := by
    intro u hu hux
    have huOdd : (u : G) ∈ oddIn P := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have huC : (u : G) ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (congrArg Subtype.val hux).symm
    have hmem : ⁅(u : G), y⁆ ∈
        ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mpr ⟨huOdd, huC⟩) hygs
    rw [hB] at hmem
    have hcomm : (u : G) * y = y * (u : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
    apply Subtype.ext
    change y * (u : G) = (u : G) * y
    exact hcomm.symm
  have htop : commutator ↥P = ⊤ := by
    have hperf' : Group.IsPerfect ↥P := (Subgroup.isPerfect_iff (H := P)).mpr hperf
    exact Group.isPerfect_def.mp hperf'
  have hsimp : IsSimpleGroup (↥P ⧸ pPrimeCore 2 ↥P) := by
    obtain ⟨e⟩ := hON
    exact (MulEquiv.isSimpleGroup_congr e).mpr CFSG.Sporadic.ON.isSimpleGroup_ON
  have hconj : ∀ a b : (↥P) ⧸ pPrimeCore 2 ↥P,
      orderOf a = 2 → orderOf b = 2 → IsConj a b :=
    fun a b ha hb => CFSG.EvenSporadicStandard.Solomon78.on_forall_isConj hON a b ha hb
  have hcenter : U ≤ Subgroup.center ↥P :=
    le_center_of_four_fixed (P := ↥P) (U := U)
      (Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥P)))
      htop hsimp hconj hx' hy' hxy' hne' hfix
  intro u hu l hl
  obtain ⟨u', hu'U, hu'eq⟩ := Subgroup.mem_map.mp hu
  have hcommH : (⟨l, hl⟩ : ↥P) * u' = u' * (⟨l, hl⟩ : ↥P) :=
    Subgroup.mem_center_iff.mp (hcenter hu'U) ⟨l, hl⟩
  have hval : l * (u' : G) = (u' : G) * l := congrArg Subtype.val hcommH
  have hu'val : (u' : G) = u := hu'eq
  rw [hu'val] at hval
  exact hval.symm

theorem commutator_inner_ne_bot_le_wGroup_of_on
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hK : Assembly.KProper Blueprint.Catalog G) {t x : G} {P : Subgroup G} (ht : orderOf t = 2)
    (hPt : P ≤ centralizer ({t} : Set G))
    (hP : IsPComponent 2 (P.subgroupOf (centralizer ({t} : Set G))))
    (hON : IsSporadic (↥P ⧸ pPrimeCore 2 ↥P) .ONan)
    (hbad : ¬ ∀ u ∈ oddIn P, ∀ l ∈ P, u * l = l * u) (hxP : x ∈ P) (hx : orderOf x = 2)
    (hx1 : centralizer ({x} : Set G) ≠ ⊤) (hxt1 : centralizer ({x * t} : Set G) ≠ ⊤) :
    ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≠ ⊥ ∧
      ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
        ⁅oddIn P, P⁆ ⊓ wGroup (zpowers x ⊔ zpowers t) := by
  have hperf : ⁅P, P⁆ = P := by
    haveI : Group.IsPerfect ↥(P.subgroupOf (centralizer ({t} : Set G))) :=
      ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hP
    have h2 : Group.IsPerfect ↥P :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPt).toMonoidHom)
        (subgroupOfEquivOfLe hPt).surjective
    exact (Subgroup.isPerfect_iff (H := P)).mp h2
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hPt hxP)
  have htx : t * x = x * t := hxt.symm
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [pow_two] using h
  have hxt_ne : x ≠ t := by
    intro hxt_eq
    let x' : ↥P := ⟨x, hxP⟩
    have hx'ord : orderOf x' = 2 := (Subgroup.orderOf_mk x hxP).trans hx
    have hcentral : ∀ p : ↥P, p * x' = x' * p := by
      intro p
      apply Subtype.ext
      have hp : (p : G) * t = t * (p : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp (hPt p.2)
      change (p : G) * x = x * (p : G)
      rw [hxt_eq]
      exact hp
    have hx'center : QuotientGroup.mk' (pPrimeCore 2 ↥P) x' ∈
        Subgroup.center (↥P ⧸ pPrimeCore 2 ↥P) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥P) q
      rw [← map_mul, ← map_mul, hcentral p]
    have hcenter : Subgroup.center (↥P ⧸ pPrimeCore 2 ↥P) = ⊥ :=
      CFSG.EvenSporadicStandard.Solomon78.center_eq_bot_of_isSporadic_on hON
    rw [hcenter, Subgroup.mem_bot] at hx'center
    have hx'mem : x' ∈ pPrimeCore 2 ↥P := (QuotientGroup.eq_one_iff x').mp hx'center
    have hdvd : orderOf x' ∣ Nat.card (pPrimeCore 2 ↥P) :=
      Subgroup.orderOf_dvd_natCard _ hx'mem
    rw [hx'ord] at hdvd
    exact (Nat.coprime_two_left.mp
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥P))).not_two_dvd_nat hdvd
  have hxHcomm : ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hxt j).eq
  have zpowers_pair : ∀ {u : G}, u * u = 1 → ∀ y : G,
      y ∈ Subgroup.zpowers u ↔ y = 1 ∨ y = u := by
    intro u hu2 y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
      · left
        have h2 : u ^ (2 : ℤ) = 1 := by simpa [zpow_natCast, pow_two] using hu2
        rw [hm, _root_.zpow_mul, h2, _root_.one_zpow]
      · right
        have h2 : u ^ (2 : ℤ) = 1 := by simpa [zpow_natCast, pow_two] using hu2
        have h2m : u ^ ((2 : ℤ) * m) = 1 := by
          rw [_root_.zpow_mul, h2, _root_.one_zpow]
        rw [hm, _root_.zpow_add_one, h2m]
        simp
    · rintro (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
  have hxn : x ∉ Subgroup.zpowers t := by
    intro hmem
    rcases (zpowers_pair ht2 x).mp hmem with h1 | h1
    · have hxne1 : x ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at hx
        norm_num at hx
      exact hxne1 h1
    · exact hxt_ne h1
  obtain ⟨hEelem, hEcard⟩ := GrS5.elemTwo_zpowers_sup hx2 (isElemTwo_zpowers ht2) hxHcomm hxn
  have hE4 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers t) = 4 := by
    rw [hEcard, Nat.card_zpowers, ht]
  have hE2 : ∀ e ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers t, e * e = 1 := hEelem.2
  have hBx : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      (pPrimeCore 2 (centralizer ({x} : Set G))).map
        (centralizer ({x} : Set G)).subtype := by
    have h := GrS5.commutator_oddCore_pLayer_le (hS := hS) (hU := hU) (hheld := hheld)
      (hK := hK) (b := t) (e := x) (L := P) ht hPt hP htx hx1
    simpa only [oddIn, gsFixedLayer] using h
  have hPinfC : P ⊓ centralizer ({x} : Set G) = P ⊓ centralizer ({x * t} : Set G) := by
    ext y
    constructor
    · rintro ⟨hyP, hyC⟩
      refine ⟨hyP, ?_⟩
      change y ∈ Subgroup.centralizer ({x} : Set G) at hyC
      change y ∈ Subgroup.centralizer ({x * t} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hPt hyP)
      calc y * (x * t) = (y * x) * t := by group
        _ = (x * y) * t := by rw [hyC]
        _ = x * (y * t) := by group
        _ = x * (t * y) := by rw [hyt]
        _ = (x * t) * y := by group
    · rintro ⟨hyP, hyC⟩
      refine ⟨hyP, ?_⟩
      change y ∈ Subgroup.centralizer ({x * t} : Set G) at hyC
      change y ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff] at hyC ⊢
      have hyt : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp (hPt hyP)
      have h1 : (x * t) * t = x := by rw [mul_assoc, ht2, mul_one]
      calc y * x = y * ((x * t) * t) := by rw [h1]
        _ = (y * (x * t)) * t := by group
        _ = ((x * t) * y) * t := by rw [hyC]
        _ = (x * t) * (y * t) := by group
        _ = (x * t) * (t * y) := by rw [hyt]
        _ = ((x * t) * t) * y := by group
        _ = x * y := by rw [h1]
  have hOx : oddIn P ⊓ centralizer ({x} : Set G) =
      oddIn P ⊓ centralizer ({x * t} : Set G) := by
    have hOle : oddIn P ≤ P := Subgroup.map_subtype_le _
    calc oddIn P ⊓ centralizer ({x} : Set G)
        = (oddIn P ⊓ P) ⊓ centralizer ({x} : Set G) := by rw [inf_eq_left.mpr hOle]
      _ = oddIn P ⊓ (P ⊓ centralizer ({x} : Set G)) := by rw [inf_assoc]
      _ = oddIn P ⊓ (P ⊓ centralizer ({x * t} : Set G)) := by rw [hPinfC]
      _ = (oddIn P ⊓ P) ⊓ centralizer ({x * t} : Set G) := by rw [inf_assoc]
      _ = oddIn P ⊓ centralizer ({x * t} : Set G) := by rw [inf_eq_left.mpr hOle]
  have hgs : gsFixedLayer P x = gsFixedLayer P (x * t) := by
    rw [gsFixedLayer, gsFixedLayer, hPinfC]
  have hBxt : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      (pPrimeCore 2 (centralizer ({x * t} : Set G))).map
        (centralizer ({x * t} : Set G)).subtype := by
    have h := GrS5.commutator_oddCore_pLayer_le (hS := hS) (hU := hU) (hheld := hheld)
      (hK := hK) (b := t) (e := x * t) (L := P) ht hPt hP ?_ hxt1
    · change ⁅oddIn P ⊓ centralizer ({x * t} : Set G), gsFixedLayer P (x * t)⁆ ≤
        (pPrimeCore 2 (centralizer ({x * t} : Set G))).map
          (centralizer ({x * t} : Set G)).subtype at h
      rw [← hOx, ← hgs] at h
      exact h
    · calc t * (x * t) = (t * x) * t := by group
        _ = (x * t) * t := by rw [htx]
  have hOdd : oddIn P ≤ oddIn (centralizer ({t} : Set G)) := by
    rw [oddIn, oddIn, ← CFSG.pPrimeCore_map_subgroupOf (p := 2) P
      (centralizer ({t} : Set G)) hPt]
    exact Subgroup.map_mono (Walter.map_pPrimeCore_le_of_isSubnormal hP.choose_spec.2.1)
  have hcomm_le_Ct : ⁅oddIn P, P⁆ ≤ oddIn (centralizer ({t} : Set G)) := by
    have hcomm := Subgroup.commutator_le_map_commutator
      (f := (centralizer ({t} : Set G)).subtype)
      (H₁ := pPrimeCore 2 (centralizer ({t} : Set G))) (H₂ := ⊤)
      (K₁ := oddIn P) (K₂ := P) hOdd ?_
    · haveI : (pPrimeCore 2 (centralizer ({t} : Set G))).Normal := CFSG.pPrimeCore_normal
      refine hcomm.trans ?_
      exact Subgroup.map_mono (Subgroup.commutator_le_left
        (H₁ := pPrimeCore 2 (centralizer ({t} : Set G))) (H₂ := ⊤))
    · rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hPt
  have hBt : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      (pPrimeCore 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype := by
    have h := (Subgroup.commutator_mono
      (inf_le_left : oddIn P ⊓ centralizer ({x} : Set G) ≤ oddIn P)
      ((gsFixedLayer_le_inf P x).trans
        (inf_le_left : P ⊓ centralizer ({x} : Set G) ≤ P))).trans hcomm_le_Ct
    simpa only [oddIn] using h
  have hWle : ⁅oddIn P ⊓ centralizer ({x} : Set G), gsFixedLayer P x⁆ ≤
      wGroup (Subgroup.zpowers x ⊔ Subgroup.zpowers t) := by
    rw [wGroup_eq_iInf_of_four hE4 hE2]
    refine le_iInf fun e => le_iInf fun he => le_iInf fun he1 => ?_
    have hefour : e = 1 ∨ e = x ∨ e = t ∨ e = x * t := by
      obtain ⟨i, h, hh, rfl⟩ :=
        GrS5.mem_zpowers_sup (z := x) (H := Subgroup.zpowers t) hxHcomm he
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      have hxi : x ^ i = 1 ∨ x ^ i = x :=
        (zpowers_pair hx2 (x ^ i)).mp (Subgroup.zpow_mem_zpowers x i)
      have htj : t ^ j = 1 ∨ t ^ j = t :=
        (zpowers_pair ht2 (t ^ j)).mp (Subgroup.zpow_mem_zpowers t j)
      rcases hxi with hxi | hxi <;> rcases htj with htj | htj
      · exact Or.inl (by rw [hxi, htj]; simp)
      · exact Or.inr (Or.inr (Or.inl (by rw [hxi, htj]; simp)))
      · exact Or.inr (Or.inl (by rw [hxi, htj]; simp))
      · exact Or.inr (Or.inr (Or.inr (by rw [hxi, htj])))
    rcases hefour with rfl | rfl | rfl | rfl
    · exact absurd rfl he1
    · exact hBx
    · exact hBt
    · exact hBxt
  refine ⟨?_, ?_⟩
  · intro hbot
    exact hbad (oddIn_comm_of_inner_four_on hperf hON hxP hx hbot)
  · exact le_inf (Subgroup.commutator_mono
      (inf_le_left : oddIn P ⊓ centralizer ({x} : Set G) ≤ oddIn P)
      ((gsFixedLayer_le_inf P x).trans
        (inf_le_left : P ⊓ centralizer ({x} : Set G) ≤ P))) hWle

end CFSG.ComponentClassification.GrSLit.L34Sec5S
