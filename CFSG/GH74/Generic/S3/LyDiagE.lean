module

public import CFSG.GH74.Generic.S3.LyMain
public import CFSG.GH74.Generic.S3.LyDiagB
public import CFSG.GH74.Generic.S3.LyDiagC
public import CFSG.GH74.Generic.S3.LyDiagD
public import CFSG.GH74.Generic.S3.LyTrans
public import CFSG.GH74.Generic.Lifting
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.Rank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups commutatorElement

section

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.isPCompIn_barSub (hnd : NbrData G t p f x y Iw Iv) :
    CFSG.GH74.GLS.IsPCompIn 2
      (centralizer ({barMk ↥(centralizer ({y} : Set G)) ⟨x, hnd.x_mem_centralizer_y⟩} :
        Set (barQ ↥(centralizer ({y} : Set G))))) (S45.barSub y Iv) := by
  have hso := orderOf_mk_centralizer hnd.x_mem_centralizer_y hnd.x_inv
  have hB := hnd.isPCompIn_Iv
  have hΛC := le_centralizer_mk hB.1 hnd.x_mem_centralizer_y
  have hΛ := isTwoComponent_centralizer_mk hB hnd.x_mem_centralizer_y
  have hIC : S45.barSub y Iv ≤
      centralizer ({barMk ↥(centralizer ({y} : Set G)) ⟨x, hnd.x_mem_centralizer_y⟩} :
        Set (barQ ↥(centralizer ({y} : Set G)))) :=
    (Subgroup.map_mono hΛC).trans (map_centralizer_barMk hso).le
  exact isPCompIn_two_iff.mpr ⟨hIC, isTwoComponent_map_barMk hso hΛC hΛ⟩

end

theorem lyNotDiag_proved (hF : GenericKnownFacts) : LyNotDiag := by
  intro G _ _ x K hset _hmax _hnt honly t p f y Iw Iv hnd himg L hL hne hAB hdiag
  have hxY := hnd.x_mem_centralizer_y
  set Y : Type := ↥(centralizer ({y} : Set G)) with hYdef
  set s : barQ Y := barMk _ ⟨x, hxY⟩ with hs
  have hso := orderOf_mk_centralizer hxY hnd.x_inv
  have hsH : orderOf s = 2 := orderOf_barMk hso
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hsH, pow_two] at this
  have hgen : Gen4 (barQ Y) := (gen4Cen_barQ hset.gen4 hnd.y_inv).gen4
  have hIsub : ((S45.barSub y Iv).subgroupOf (centralizer ({s} : Set (barQ Y)))).IsSubnormal :=
    CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
      (isPCompIn_two_iff.mp hnd.isPCompIn_barSub).2.1 Subgroup.IsSubnormal.top
  have hΔ : S45.barSub y Iv = (swapDiag hAB).range :=
    eq_range_swapDiag_of_subnormal hsH hL.1 hAB hnd.barSub_isQuasisimple hIsub hdiag
  obtain ⟨F, hFf, hFfin, hFc, ⟨eSL⟩⟩ := hnd.Iv_iso
  obtain ⟨φ, -⟩ := hnd.barSub_equiv
  let eΔ : ↥(swapDiag hAB).range ≃* StatedSL 2 F :=
    ((MulEquiv.subgroupCongr hΔ.symm).trans (φ.symm.trans eSL.symm)).trans
      (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F).symm
  have hKP : GLS.IsKProperSimple G := ⟨hset.simple, hset.nonab, CFSG.GH74.kProper_of_kgh hset.kgh⟩
  have hcal := GLS.inCalK2_of_isComponent hKP hnd.y_inv hL
  have hZ2 : IsPGroup 2 ↥(center ↥L) := by
    have := pCore_isPGroup (p := 2) (G := ↥L)
    rw [← hcal.2.1] at this
    exact this
  have he : xbar y ∈ (swapDiag hAB).range := hΔ ▸ hnd.xbar_mem_barSub
  have hc : ∀ d ∈ (swapDiag hAB).range, d * xbar y = xbar y * d := fun d _ =>
    Subgroup.mem_center_iff.1 (xbar_mem_center y) d
  obtain ⟨a, haC, haa, hae⟩ := exists_central_involution_diag hF hL.1 hZ2 hAB hnd.prime.1 hnd.prime.2.1
    hnd.prime.2.2 hFc eΔ he hnd.xbar_ne_one hc
  obtain ⟨u, hu, huu, hbarOf⟩ := exists_involution_lift y (ub := (a : CentralizerBar y)) haa
  let xY : Y := ⟨x, hxY⟩
  let yY : Y := ⟨y, NbrData.y_mem_centralizer_y y⟩
  let zY : Y := ⟨u, hu⟩
  have hxY2 : xY * xY = 1 := Subtype.ext hnd.x_sq
  have hyY2 : yY * yY = 1 := Subtype.ext hnd.y_sq
  have hzY2 : zY * zY = 1 := Subtype.ext huu
  have hyc : ∀ g : Y, g * yY = yY * g := fun g =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 g.2)
  have hsq : (barMk Y (xY * zY)) ^ 2 = xbar y := by
    have h1 : barMk Y (xY * zY) = s * (a : barQ Y) := by
      rw [map_mul]
      exact congrArg (fun w => s * w) hbarOf
    rw [h1, pow_two, sq_eq_swapDiag hAB hs2 a, hae]
  have hmem : (xY * zY) ^ 2 * yY⁻¹ ∈ pPrimeCore 2 Y := by
    rw [← QuotientGroup.eq_one_iff]
    change barMk Y ((xY * zY) ^ 2 * yY⁻¹) = 1
    rw [map_mul, map_pow, map_inv, hsq]
    exact mul_inv_cancel _
  have hN : Odd (Nat.card (pPrimeCore 2 Y)) :=
    Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have : (pPrimeCore 2 Y).Normal := pPrimeCore_normal
  obtain ⟨g, hg⟩ := exists_conj_of_dihedral hN hyY2 hyc hxY2 hzY2 hmem
  have hxy : IsConj x (y * x) := by
    rw [isConj_iff]
    refine ⟨(g : G)⁻¹, ?_⟩
    have h1 : (g : G)⁻¹ * x * (g : G) = y * x := congrArg Subtype.val hg
    rw [inv_inv]
    exact h1
  have hLc : center ↥L ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at haC
    apply hnd.xbar_ne_one
    rw [← hae, haC]
    exact map_one _
  have hcomp : ∀ J : Subgroup (CentralizerBar y), CFSG.IsComponent J → center ↥J ≠ ⊥ := by
    intro J hJ
    rcases eq_or_eq_conj_of_gen4 hgen hL hne hJ with h | h
    · rw [h]
      exact hLc
    · rw [h]
      intro hbot
      have eLs : ↥L ≃* ↥(conjSub s⁻¹ L) := L.equivMapOfInjective _ (MulAut.conj s⁻¹).injective
      exact hLc (center_eq_bot_of_mulEquiv' eLs.symm hbot)
  obtain ⟨p', f', -, -, -, hmK⟩ := hset.shape.1
  have hKc : center ↥K = ⊥ := center_eq_bot_of_quasisimple_lieModel_L3 hset.comp.1 hmK
  have hnc : ¬ IsConj y x := not_isConj_of_centerless_component y x K hset.comp hKc hcomp
  obtain ⟨hx, hxc⟩ := hnd.x_mem_commutator hset.simple hset.nonab honly himg hxy hnc
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  refine not_mem_commutator_of_swapped (barMk Y) (L := L) (L' := conjSub s⁻¹ L)
    CFSG.IsComponent (fun J g hJ => isComponent_conjSub hJ g) hL hne
    (fun J hJ => eq_or_eq_conj_of_gen4 hgen hL hne hJ) (g₀ := xY) ?_ hxc
  change conjSub s L = conjSub s⁻¹ L
  rw [hs']

end CFSG.GH74.Generic.S3
