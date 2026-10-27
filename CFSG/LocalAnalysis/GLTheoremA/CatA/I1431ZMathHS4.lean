module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431Z

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open Subgroup CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzA
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

theorem noU42Comp_of_centralizer_equiv {Q : Type} [Group Q] [Finite Q] {k : Q} {T : Type}
    [Group T] (e : ↥(Subgroup.centralizer ({k} : Set Q)) ≃* T) (hq : CFSG.Open.IsQuasisimple T)
    (hZ : IsPGroup 3 ↥(Subgroup.center T)) (hp : 3 ∣ Nat.card T)
    (hc : Nat.card (T ⧸ Subgroup.center T) ≠ 25920) : NoU42Comp 3 k := by
  set C := Subgroup.centralizer ({k} : Set Q) with hC
  have hq' : CFSG.Open.IsQuasisimple ↥C :=
    CFSG.HardMathSupport.Timmesfeld.Proving.isQuasisimple_of_mulEquiv' e.symm hq
  have ec : ↥(Subgroup.center ↥C) ≃* ↥(Subgroup.center T) :=
    ((Subgroup.center ↥C).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_center_eq e))
  have hZ' : IsPGroup 3 ↥(Subgroup.center ↥C) := hZ.of_equiv ec.symm
  have hp' : 3 ∣ Nat.card ↥C := by
    rw [Nat.card_congr e.toEquiv]
    exact hp
  have eq : (↥C ⧸ Subgroup.center ↥C) ≃* (T ⧸ Subgroup.center T) :=
    QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center T) e (Subgroup.map_center_eq e)
  have hLn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (C : Set Q)) :=
    isPGroup_inf_centralizer_self C hZ'
  have hcore : GLAPPrimeCore 3 ↥C = ⊥ :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three le_rfl hLn hq' hp' hcent
  intro I hI hcI
  rw [eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three le_rfl hLn hq' hcore hcent hI]
    at hcI
  apply hc
  rw [← Nat.card_congr eq.toEquiv, ← Nat.card_congr (pSimpleEquivCenterQuot C hcore).toEquiv]
  exact hcI

theorem centralizer_sub_eq {G : Type} [Group G] (P : Subgroup G) {a b : ↥P}
    (h : Subgroup.centralizer ({(a : G)} : Set G) = Subgroup.centralizer ({(b : G)} : Set G)) :
    Subgroup.centralizer ({a} : Set ↥P) = Subgroup.centralizer ({b} : Set ↥P) := by
  apply Subgroup.map_injective P.subtype_injective
  rw [map_centralizer_subtype', map_centralizer_subtype', h]

theorem noU42Comp_of_centralizer_eq {Q : Type} [Group Q] {a b : Q}
    (h : Subgroup.centralizer ({a} : Set Q) = Subgroup.centralizer ({b} : Set Q))
    (hb : NoU42Comp 3 b) : NoU42Comp 3 a := by
  unfold NoU42Comp
  rw [h]
  exact hb


theorem noU42Comp_xA : NoU42Comp 3 (⟨fuseXA, fuseXA_mem⟩ : ↥suzM) := by
  obtain ⟨hq, hcen, ⟨eT⟩⟩ := aSub_quasisimple
  set k : ↥suzM := ⟨fuseXA, fuseXA_mem⟩ with hk
  have hmap : (Subgroup.centralizer ({k} : Set ↥suzM)).map suzM.subtype = aSub := by
    rw [map_centralizer_subtype' suzM k]
    exact aSub_eq.symm
  let e : ↥(Subgroup.centralizer ({k} : Set ↥suzM)) ≃* ↥aSub :=
    ((Subgroup.centralizer ({k} : Set ↥suzM)).equivMapOfInjective suzM.subtype
      suzM.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have hz3 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
  have hz1 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ≠ 1 := fun h => fuseXA_ne_one (congrArg Subtype.val h)
  have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := orderOf_eq_prime hz3 hz1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine noU42Comp_of_centralizer_equiv e hq ?_ (by rw [card_aSub]; norm_num) ?_
  · have h3 : IsPGroup 3 ↥(Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    exact h3.of_equiv (MulEquiv.subgroupCongr hcen.symm)
  · rw [Nat.card_congr eT.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀]
    norm_num

theorem noU42Comp_suzM (k : ↥suzM) (hk : orderOf k = 3) : NoU42Comp 3 k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 1782)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := suz_exists_conj_classes k.2 hs3
  let H : ↥suzM := ⟨h, hh⟩
  let y : ↥suzM := H⁻¹ * k * H
  have hy : (y : Equiv.Perm (Fin 1782)) = c ^ e := by
    show h⁻¹ * (k : Equiv.Perm (Fin 1782)) * h = c ^ e
    rw [← hcon]
    group
  have hY : NoU42Comp 3 y := by
    rcases hc with rfl | rfl | rfl
    · refine noU42Comp_of_centralizer_eq (b := ⟨fuseXA, fuseXA_mem⟩)
        (centralizer_sub_eq suzM ?_) noU42Comp_xA
      rw [hy]
      exact CFSG.Quasithin.Kleidman.centralizer_pow_eq fuseXA_pow he
    · obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
      refine noU42Comp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective suzM.subtype suzM.subtype_injective ?_
      rw [map_centralizer_subtype', hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := fuseXB) xBPerm_pow he]
      show CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
        (centralizer {xBPerm} ⊓ suzM)
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨hC, hCcard⟩ := Cy_eq
      refine noU42Comp_of_not_dvd ?_
      rw [card_centralizer_sub, hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq yPerm_pow he, ← hC,
        hCcard]
      norm_num
  have h' := noU42Comp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem row_suz (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) : I1431SporRow .Suz := by
  have e : NativeSporadic.Carrier .Suz ≃* ↥suzM := suzEquivM
  have hc : Nat.card ↥suzM = 448345497600 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  haveI : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  exact row_of_model (s := .Suz) (Q := ↥suzM) hOut (e.symm.trans (hbr .Suz).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    noU42Comp_suzM

end CFSG.LocalAnalysis.GLTheoremA.I1431Z
