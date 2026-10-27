module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS4
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Final
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZCo1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZMathHS1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZSpor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14ChevFacts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporHe7
public import Certificates.Data.TabCo1ThreeE

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K14Spor

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt)
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open CFSG.LocalAnalysis.GLTheoremA.H1431c (NoCardComp noCardComp_of_mulEquiv noCardComp_conj
  noCardComp_of_shapeRkAt noCardComp_of_pConstrained)

theorem noCardComp_of_centralizer_equiv {Q : Type} [Group Q] [Finite Q] {k : Q} {T : Type}
    [Group T] {n : ℕ} (e : ↥(Subgroup.centralizer ({k} : Set Q)) ≃* T)
    (hq : CFSG.Open.IsQuasisimple T) (hZ : IsPGroup 3 ↥(Subgroup.center T))
    (hp : 3 ∣ Nat.card T) (hc : Nat.card (T ⧸ Subgroup.center T) ≠ n) : NoCardComp n k := by
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
    CFSG.HardMathSupport.Dickson.I271.isPGroup_inf_centralizer_self C hZ'
  have hcore : GLAPPrimeCore 3 ↥C = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three
      le_rfl hLn hq' hp' hcent
  intro I hI hcI
  rw [CFSG.HardMathSupport.Dickson.I271.eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three
    le_rfl hLn hq' hcore hcent hI] at hcI
  apply hc
  rw [← Nat.card_congr eq.toEquiv,
    ← Nat.card_congr (CFSG.HardMathSupport.Dickson.I271.pSimpleEquivCenterQuot C hcore).toEquiv]
  exact hcI

theorem noCardComp_of_centralizer_eq {Q : Type} [Group Q] {a b : Q} {n : ℕ}
    (h : Subgroup.centralizer ({a} : Set Q) = Subgroup.centralizer ({b} : Set Q))
    (hb : NoCardComp n b) : NoCardComp n a := by
  unfold NoCardComp
  rw [h]
  exact hb


section Suz

open Subgroup CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzA
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)

theorem noCardComp_suzM
    {n : ℕ} (hn : n = 13685760 ∨ n = 1451520) (k : ↥suzM)
    (hk : orderOf k = 3) : NoCardComp n k := by
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
  have hY : NoCardComp n y := by
    rcases hc with rfl | rfl | rfl
    · refine noCardComp_of_centralizer_eq (b := ⟨fuseXA, fuseXA_mem⟩)
        (I1431Z.centralizer_sub_eq suzM ?_) ?_
      · rw [hy]
        exact CFSG.Quasithin.Kleidman.centralizer_pow_eq fuseXA_pow he
      · obtain ⟨hq, hcen, ⟨eT⟩⟩ := aSub_quasisimple
        set k' : ↥suzM := ⟨fuseXA, fuseXA_mem⟩ with hk'
        have hmap : (Subgroup.centralizer ({k'} : Set ↥suzM)).map suzM.subtype = aSub := by
          rw [map_centralizer_subtype' suzM k']
          exact aSub_eq.symm
        let e' : ↥(Subgroup.centralizer ({k'} : Set ↥suzM)) ≃* ↥aSub :=
          ((Subgroup.centralizer ({k'} : Set ↥suzM)).equivMapOfInjective suzM.subtype
            suzM.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
        have hz3 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ^ 3 = 1 := Subtype.ext (by simpa using fuseXA_pow)
        have hz1 : (⟨fuseXA, aX_mem⟩ : ↥aSub) ≠ 1 :=
          fun h => fuseXA_ne_one (congrArg Subtype.val h)
        have hord : orderOf (⟨fuseXA, aX_mem⟩ : ↥aSub) = 3 := orderOf_eq_prime hz3 hz1
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        refine noCardComp_of_centralizer_equiv e' hq ?_ (by rw [card_aSub]; norm_num) ?_
        · have h3 : IsPGroup 3 ↥(Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub)) :=
            IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
          exact h3.of_equiv (MulEquiv.subgroupCongr hcen.symm)
        · rw [Nat.card_congr eT.toEquiv, CFSG.LieType.Multipliers.U43.card_X₀]
          rcases hn with rfl | rfl <;> norm_num
    · obtain ⟨hcard, -, hle, hnorm, hcent⟩ := TabSuzB.caseB_spec
      refine noCardComp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective suzM.subtype suzM.subtype_injective ?_
      rw [map_centralizer_subtype', hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq (c := fuseXB) xBPerm_pow he]
      show CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape 3
        (centralizer {xBPerm} ⊓ suzM)
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 6) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨hC, hCcard⟩ := Cy_eq
      refine noCardComp_of_not_dvd ?_
      rw [I1431Z.card_centralizer_sub, hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq yPerm_pow he, ← hC, hCcard]
      rcases hn with rfl | rfl <;> norm_num
  have h' := noCardComp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem cardRow_suz
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (hn : n = 13685760 ∨ n = 1451520) : CardRow n .Suz := by
  have e : NativeSporadic.Carrier .Suz ≃* ↥suzM := suzEquivM
  have hc : Nat.card ↥suzM = 448345497600 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Suz.card_Suz
  haveI : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  exact cardRow_of_model (s := .Suz) (Q := ↥suzM) hOut (e.symm.trans (hbr .Suz).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noCardComp_suzM hn)

end Suz

section Co3

open Subgroup CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.Co3Cent
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T CFSG.Sporadic.Schreier.Co3

theorem noCardComp_co3P
    {n : ℕ} (hn : n = 13685760 ∨ n = 1451520) (k : ↥co3P)
    (hk : orderOf k = 3) : NoCardComp n k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 276)) = 3 := by
    rw [← Subgroup.orderOf_coe] at hk
    exact hk
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := exists_conj_classes k.2 hs3
  let H : ↥co3P := ⟨h, hh⟩
  let y : ↥co3P := H⁻¹ * k * H
  have hy : (y : Equiv.Perm (Fin 276)) = c ^ e := by
    show h⁻¹ * (k : Equiv.Perm (Fin 276)) * h = c ^ e
    rw [← hcon]
    group
  have hY : NoCardComp n y := by
    rcases hc with rfl | rfl | rfl
    · obtain ⟨hX3, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
      refine noCardComp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
      rw [map_centralizer_subtype', hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq hX3 he]
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨hX3, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
      refine noCardComp_of_pConstrained ?_
      refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
      rw [map_centralizer_subtype', hy, CFSG.Quasithin.Kleidman.centralizer_pow_eq hX3 he]
      exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
        (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent
    · obtain ⟨⟨hC, hCcard⟩, -⟩ := caseC_spec
      refine noCardComp_of_not_dvd ?_
      rw [I1431Z.card_centralizer_sub, hy,
        CFSG.Quasithin.Kleidman.centralizer_pow_eq yPerm_pow he, ← hC, hCcard]
      rcases hn with rfl | rfl <;> norm_num
  have h' := noCardComp_conj hY H
  have hk' : H * y * H⁻¹ = k := by
    simp only [y]
    group
  rwa [hk'] at h'

theorem cardRow_co3
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {n : ℕ}
    (hn : n = 13685760 ∨ n = 1451520) : CardRow n .Co3 := by
  have e : NativeSporadic.Carrier .Co3 ≃* ↥co3P := co3PermEquiv
  have hc : Nat.card ↥co3P = 495766656000 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Co3.card_Co3
  haveI : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  exact cardRow_of_model (s := .Co3) (Q := ↥co3P) hOut (e.symm.trans (hbr .Co3).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    (noCardComp_co3P hn)

end Co3

section HN

open CFSG.Sporadic.HNSchreier CFSG.HardMathSupport.Dickson.I271
open scoped commutatorElement

set_option maxRecDepth 4000 in
theorem noCardComp_s1'
    {n : ℕ} (hn : n ≠ 181440) : NoCardComp n (sJ 0) := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  obtain ⟨-, -, hcomm⟩ := CJ_s1_structure
  have hder := commutator_CJ_s1
  haveI hsimple : IsSimpleGroup ↥L1J := by
    have := alt3_simple
    exact MulEquiv.isSimpleGroup (alt3.equivMapOfInjective iotaA iotaA_injective).symm
  have hcard : Nat.card ↥L1J = 181440 := by
    rw [show (L1J : Subgroup JH) = alt3.map iotaA from rfl,
      Subgroup.card_map_of_injective iotaA_injective, card_alt3]
  have hLC : L1J ≤ Subgroup.centralizer ({sJ 0} : Set ↥JH) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx)
  have hnp : ¬ (Nat.card ↥L1J).Prime := by
    rw [hcard]
    norm_num
  have hnab : ∃ a b : ↥L1J, a * b ≠ b * a := exists_noncomm_of_simple_card (G := ↥L1J) hnp
  have h3 : 3 ∣ Nat.card ↥L1J := by
    rw [hcard]
    norm_num
  have hk : Nat.card ↥(Subgroup.centralizer ({sJ 0} : Set ↥JH)) = Nat.card ↥L1J * 3 ^ 1 := by
    rw [show Subgroup.centralizer ({sJ 0} : Set ↥JH) = CJ (sJ 0) from rfl, card_CJ_s1, hcard]
    norm_num
  refine noCardComp_of_shapeRkAt (Rk := fun _ _ => True) ?_
  refine shapeRkAt_of_data (Good := fun T _ => Nat.card T ≠ n) (Rk := fun _ _ => True)
    Nat.prime_three (fun T T' _ _ e h hc => h ((Nat.card_congr e.toEquiv).trans hc))
    (fun _ _ _ _ _ h => h) (sJ 0) L1J hLC ?_ hsimple hnab h3 hk (by rw [hcard]; exact hn.symm)
    trivial
  intro g hg l hl
  have h1 : ⁅g, l⁆ ∈ ⁅CJ (sJ 0), CJ (sJ 0)⁆ := Subgroup.commutator_mem_commutator hg (hLC hl)
  rw [hder] at h1
  have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
    rw [commutatorElement_def]; group
  rw [h3]
  exact L1J.mul_mem h1 hl

theorem noCardComp_JH'
    {n : ℕ} (hn : n ≠ 181440) (k : ↥JH) (hk : orderOf k = 3) :
    NoCardComp n k := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  rcases (order_three_classes k).1 hk with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg]
    exact noCardComp_conj (noCardComp_s1' hn) g
  · obtain ⟨g, hg⟩ := isConj_iff.1 h
    rw [← hg]
    exact noCardComp_conj
      (noCardComp_of_pConstrained (pConstrainedShape_of_hn3bRChecks hn3bR_checks)) g

set_option maxRecDepth 100000 in
theorem cardRow_hn
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    {n : ℕ} (hn : n ≠ 181440) : CardRow n .HN := by
  haveI : Finite ↥JH := Nat.finite_of_card_ne_zero (by rw [card_JH]; norm_num)
  haveI hHN : IsSimpleGroup NativeSporadic.HN := CFSG.Sporadic.HN.isSimpleGroup_HN
  haveI : IsSimpleGroup ↥JH := @MulEquiv.isSimpleGroup _ _ _ _ hHN hnEquivJ.symm
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  have hp : ¬ (Nat.card ↥JH).Prime := by rw [card_JH]; norm_num
  have hnc : ∃ x y : ↥JH, x * y ≠ y * x :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (S := ↥JH) hp
  have hb : ↥JH ≃* (TauCeti.CFSGIndex.sporadic .HN).Group := hnEquivJ.symm.trans e
  refine cardRow_of_model (s := .HN) (Q := ↥JH) hOut ?_ ?_ ?_
  · exact hb
  · exact hnc
  · exact noCardComp_JH' hn

end HN

theorem k14_names_of_dvd
    (s : TauCeti.SporadicName)
    (h : 13685760 ∣ sporOrd s ∨ 1451520 ∣ sporOrd s) :
    s = .Suz ∨ s = .Co3 ∨ s = .Co2 ∨ s = .Co1 ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi23 ∨
      s = .Fi24Prime ∨ s = .HN ∨ s = .Th ∨ s = .B ∨ s = .M := by
  revert h
  cases s <;> decide +kernel

theorem k14_card_dvd
    {S : Type} [Group S] [Finite S] {J : Subgroup S}
    (hT : catalogIs (PSimple 3 J) S9.isU5two ∨ catalogIs (PSimple 3 J) S9.isSp6two) :
    13685760 ∣ Nat.card S ∨ 1451520 ∣ Nat.card S := by
  have hd : Nat.card (PSimple 3 J) ∣ Nat.card S := by
    have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
    have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    exact h2.trans (h3.trans (Subgroup.card_subgroup_dvd_card J))
  rcases hT with hT | hT
  · left
    rw [← card_u5two hT]
    exact hd
  · right
    rw [← card_sp6two hT]
    exact hd

theorem k14SporU_of_BM
    (hB : K14Row .B) (hM : K14Row .M) : K14SporU := by
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  have hrow : ∀ n, n = 13685760 ∨ n = 1451520 → ∀ s, s ≠ .B → s ≠ .M → s ≠ .Co2 →
      (13685760 ∣ sporOrd s ∨ 1451520 ∣ sporOrd s) → CardRow n s := by
    intro n hn s hsB hsM hsC hd
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := cardRow_shape hOut hbr n hn
    rcases k14_names_of_dvd s hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact cardRow_suz hOut hbr hn
    · exact cardRow_co3 hOut hbr hn
    · exact absurd rfl hsC
    · exact h5
    · exact h6
    · exact h1
    · exact h3
    · exact h4
    · exact cardRow_hn hOut (by rcases hn with rfl | rfl <;> norm_num)
    · exact h2
    · exact absurd rfl hsB
    · exact absurd rfl hsM
  intro S _ _ s e β hβ3 hβ1 J hJ hJT
  by_contra hne
  obtain ⟨e'⟩ := e
  have hcard : Nat.card S = sporOrd s := (Nat.card_congr e'.toEquiv).trans (hOrd s)
  have hd : 13685760 ∣ sporOrd s ∨ 1451520 ∣ sporOrd s := hcard ▸ k14_card_dvd hJT
  by_cases hsB : s = .B
  · subst hsB
    exact hB S ⟨e'⟩ β hβ3 hβ1 J hJ hJT
  by_cases hsM : s = .M
  · subst hsM
    exact hM S ⟨e'⟩ β hβ3 hβ1 J hJ hJT
  exact k14Row_of_card (hrow _ (Or.inl rfl) s hsB hsM hne hd)
    (hrow _ (Or.inr rfl) s hsB hsM hne hd) S ⟨e'⟩ β hβ3 hβ1 J hJ hJT

end CFSG.LocalAnalysis.GLTheoremA.K14Spor

end
