module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRowsA
public import CFSG.Sporadic.Co2Smith.GlC0JankoA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Co3Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Shape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi22Shape

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem stypeOK_U42
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    (e : T ≃* ↥CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45.originalSubgroup) :
    STypeOK 3 T := by
  have hT : Nat.card T = 25920 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Co2Smith.card_QP45
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  exact stypeOK_of_card hb hT (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)

theorem stypeOK_L28
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    (e : T ≃* ↥CFSG.GH74.KGroups.L28.QP.originalSubgroup) : STypeOK 3 T := by
  obtain ⟨e1⟩ := CFSG.GH74.KGroups.L28.equiv_psl_P
  have hT : Nat.card T = 504 :=
    (Nat.card_congr (e.trans e1.symm).toEquiv).trans CFSG.GH74.KGroups.L28.card_psl_GF8
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  exact stypeOK_of_card hb hT (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows

namespace CFSG.HardMathSupport.Dickson.I271.SporAltCo3

open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
  CFSG.Monster.B.Fischer CFSG.Sporadic.Schreier.Co3
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T
  CFSG.HardMathSupport.Dickson.I271.Co3Cent CFSG.HardMathSupport.Solomon.Coordinator.Co3Pump
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.I271
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
open scoped commutatorElement


theorem shape_XB' {XBm : XB ∈ co3P} :
    ShapeRkAt 3 STypeThree (fun _ _ => True) (⟨XB, XBm⟩ : ↥co3P) := by
  left
  refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseB_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem shape_XA' {XAm : XA ∈ co3P} :
    ShapeRkAt 3 STypeThree (fun _ _ => True) (⟨XA, XAm⟩ : ↥co3P) := by
  left
  refine pConstrainedShape_of_map_injective co3P.subtype co3P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := caseA_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem shape_y' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {yPm : yPerm ∈ co3P} :
    ShapeRkAt 3 STypeThree (fun _ _ => True) (⟨yPerm, yPm⟩ : ↥co3P) := by
  obtain ⟨⟨hC, hCcard⟩, hLC, hder, hLcard, hrels⟩ := caseC_spec
  obtain ⟨e⟩ := nonempty_mulEquiv_L
  refine shapeRkAt_of_subgroup_data (P := co3P) (L := closure (permsA 276 (lGens ())))
    Nat.prime_three stypeThree_of_equiv (fun _ _ _ _ _ h => h)
    ⟨yPerm, yPm⟩ (hC ▸ hLC) ?_ (isSimpleGroup_of_equiv_P9 e) (nonabelian_of_equiv_P9 e) ?_
    (k := 2) ?_ ?_ trivial
  · intro g hg l hl
    rw [← hC] at hg
    have h1 : ⁅g, l⁆ ∈ ⁅closure (permsA 276 (cGens ())), closure (permsA 276 (cGens ()))⁆ :=
      Subgroup.commutator_mem_commutator hg (hLC hl)
    have h2 := hder h1
    have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
      rw [commutatorElement_def]; group
    rw [h3]
    exact (closure (permsA 276 (lGens ()))).mul_mem h2 hl
  · rw [hLcard]; norm_num
  · rw [← hC, hCcard, hLcard]; norm_num
  · exact stypeOK_L28 hb e

theorem co3_centShapeRk_level (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CentShapeRk 3 STypeThree (fun _ _ => True) ↥co3P := by
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hXA3, -, hXAm, -⟩ := caseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := caseB_spec
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 276)) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : (k : Equiv.Perm (Fin 276)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 276)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥co3P, (c' : Equiv.Perm (Fin 276)) = c ∧ c' ^ 3 = 1 ∧
      ShapeRkAt 3 STypeThree (fun _ _ => True) c' := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨⟨XA, hXAm⟩, rfl, Subtype.ext (by simpa using hXA3), shape_XA' (XAm := hXAm)⟩
    · exact ⟨⟨XB, hXBm⟩, rfl, Subtype.ext (by simpa using hXB3), shape_XB' (XBm := hXBm)⟩
    · exact ⟨⟨yPerm, yPerm_mem⟩, rfl, Subtype.ext (by simpa using yPerm_pow),
        shape_y' hb (yPm := yPerm_mem)⟩
  obtain ⟨c', hc'val, hc'3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 STypeThree (fun _ _ => True) (c' ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc'3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three stypeThree_of_equiv hRk
    (MulAut.conj (⟨h, hh⟩ : ↥co3P)) hshape'
  have hk : (MulAut.conj (⟨h, hh⟩ : ↥co3P)) (c' ^ e) = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp [MulAut.conj_apply]
  rw [hk] at hconj
  exact hconj

theorem srow_Co3_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .Co3 3 := by
  have e : CFSG.Blueprint.NativeSporadic.Co3 ≃* ↥co3P := co3PermEquiv
  haveI : IsSimpleGroup ↥co3P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co3.isSimpleGroup_Co3 e.symm
  have hc : Nat.card ↥co3P = 495766656000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co3.card_Co3
  have b : ↥co3P ≃* (TauCeti.CFSGIndex.sporadic .Co3).Group := e.symm.trans (hbr .Co3).some
  exact srow_of_centShape hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) (CentShape.of_centShapeRk (co3_centShapeRk_level hb))
    fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.SporAltCo3

namespace CFSG.HardMathSupport.Dickson.I271.SporAltCo2

open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open Subgroup CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co2Cert
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271.Co2Cent CFSG.HardMathSupport.Dickson.I271.U42Presentation
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremA.I1416Rows
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor


theorem co2Shape_XA' {XAm : co2XA ∈ co2P} :
    ShapeRkAt 3 STypeThree (fun _ _ => True) (⟨co2XA, XAm⟩ : ↥co2P) := by
  left
  refine pConstrainedShape_of_map_injective co2P.subtype co2P.subtype_injective ?_
  rw [map_centralizer_subtype']
  obtain ⟨-, -, -, hcard, hle, hnorm, hcent⟩ := co2CaseA_spec
  exact pConstrainedShape_of_normal_pgroup hle (normal_subgroupOf_of_forall_conj hnorm)
    (IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num)) hcent

theorem co2Shape_XB' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {XBm : co2XB ∈ co2P} :
    ShapeRkAt 3 STypeThree (fun _ _ => True) (⟨co2XB, XBm⟩ : ↥co2P) := by
  obtain ⟨-, -, -, hcard, hLC, hLn, hcent, hrels⟩ := co2CaseB_spec
  obtain ⟨e⟩ := nonempty_mulEquiv_QP45_of_rels uvGen hrels hcard
  exact shapeRkAt_of_subgroup_data_nq Nat.prime_three stypeThree_of_equiv (fun _ _ _ _ _ h => h)
    co2P ⟨co2XB, XBm⟩ Lsub hLC hLn
    (isSimpleGroup_of_equiv_QP45 e) (nonabelian_of_equiv_QP45 e)
    (three_dvd_card_of_equiv_QP45 e) hcent
    (stypeOK_U42 hb e) trivial

theorem co2_centShapeRk_level (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : CentShapeRk 3 STypeThree (fun _ _ => True) ↥co2P := by
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  obtain ⟨hXA3, -, hXAm, -⟩ := co2CaseA_spec
  obtain ⟨hXB3, -, hXBm, -⟩ := co2CaseB_spec
  intro k hk1 hkp
  have hs3 : orderOf (k : Equiv.Perm (Fin 2300)) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h1 : (k : Equiv.Perm (Fin 2300)) ^ 3 = 1 := by
      have := congrArg Subtype.val hkp
      simpa using this
    have h2 : (k : Equiv.Perm (Fin 2300)) ≠ 1 := fun h => hk1 (Subtype.ext h)
    exact orderOf_eq_prime h1 h2
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := co2_exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥co2P, (c' : Equiv.Perm (Fin 2300)) = c ∧ c' ^ 3 = 1 ∧
      ShapeRkAt 3 STypeThree (fun _ _ => True) c' := by
    rcases hc with rfl | rfl
    · exact ⟨⟨co2XA, hXAm⟩, rfl, Subtype.ext (by simpa using hXA3), co2Shape_XA' (XAm := hXAm)⟩
    · exact ⟨⟨co2XB, hXBm⟩, rfl, Subtype.ext (by simpa using hXB3), co2Shape_XB' hb (XBm := hXBm)⟩
  obtain ⟨c', hc'val, hc'3, hshape⟩ := hrep
  have hshape' : ShapeRkAt 3 STypeThree (fun _ _ => True) (c' ^ e) :=
    ShapeRkAt.of_centralizer_eq (CFSG.Quasithin.Kleidman.centralizer_pow_eq hc'3 he).symm hshape
  have hconj := ShapeRkAt.of_equiv Nat.prime_three stypeThree_of_equiv hRk
    (MulAut.conj (⟨h, hh⟩ : ↥co2P)) hshape'
  have hk : (MulAut.conj (⟨h, hh⟩ : ↥co2P)) (c' ^ e) = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp [MulAut.conj_apply]
  rw [hk] at hconj
  exact hconj

theorem srow_Co2_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .Co2 3 := by
  have e : CFSG.Blueprint.NativeSporadic.Co2 ≃* ↥co2P := co2PermEquiv
  haveI : IsSimpleGroup ↥co2P :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Co2.isSimpleGroup_Co2 e.symm
  have hc : Nat.card ↥co2P = 42305421312000 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Co2.card_Co2
  have b : ↥co2P ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group := e.symm.trans (hbr .Co2).some
  exact srow_of_centShape hOut b
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) (CentShape.of_centShapeRk (co2_centShapeRk_level hb))
    fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.SporAltCo2

namespace CFSG.HardMathSupport.Dickson.I271.SporAltFi22

open CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Certificates CFSG.Monster.B.Fischer
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent CFSG.HardMathSupport.Dickson.I271
  CFSG.LocalAnalysis.GLTheoremA.I1416Rows
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor

section ClassA


theorem shapeRkAt_xP' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥) :
    ShapeRkAt 3 STypeThree (fun _ _ => True) xP := by
  refine shapeRkAt_of_subgroup_data_solvable Nat.prime_three
    stypeThree_of_equiv (fun _ _ _ _ _ h => h) fi22P xP lSub ?_
    lSub_normalized_cent isSimpleGroup_lSub nonabelian_lSub ?_ hcore (m := 6) ?_ (by norm_num)
    (stypeOK_of_card hb (N := 3265920) (by rw [card_lSub] <;> norm_num) (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide)) trivial
  · intro l hl
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (lSub_comm_x l hl),
      ((mem_lev2_iff _).1 (lSub_le_lev2 hl)).1⟩
  · rw [card_lSub]; norm_num
  · refine card_cent_eq.trans ?_
    rw [card_lSub]

end ClassA

section ClassAJ

open CFSG.Sporadic.Fi22 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
  CFSG.HardMathSupport.Solomon.Coordinator.YS08
  CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump
  CFSG.HardMathSupport.Dickson.I271.TabFi22Small


theorem shapeRkAt_xRep_three' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : ShapeRkAt 3 STypeThree (fun _ _ => True) (xRep 3) := by
  haveI := finite_J_tab
  have hOP : OPrimeCoreTrivialAt 3 ↥fi22P :=
    @OPrimeCoreTrivialAt.of_mulEquiv 3 ↥fi22P _ ↥CFSG.Sporadic.Fi22.J inferInstance eJP.symm oPrimeCoreTrivialAt_Fi22J
  have hcore : GLAPPrimeCore 3 ↥(Subgroup.centralizer ({xP} : Set ↥fi22P)) = ⊥ :=
    (glaPPrimeCoreOf_eq_bot_iff_glaPPrimeCore 3 _).1 (hOP xP orderOf_xP)
  have hshape := shapeRkAt_xP' hb hcore
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  have hJ := @ShapeRkAt.of_equiv ↥fi22P ↥CFSG.Sporadic.Fi22.J _ _ inferInstance 3 Nat.prime_three STypeThree
    (fun _ _ => True) stypeThree_of_equiv hRk finite_J_tab eJP.symm xP hshape
  set t : CFSG.Sporadic.Fi22.J := eJP.symm xP with ht
  have hord : orderOf t = 3 := by rw [MulEquiv.orderOf_eq]; exact orderOf_xP
  have hiota : Fi22Copy.iotaJ t = xPerm := by
    have h1 := eJP_apply t
    rw [ht, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  obtain ⟨k, hk4, hconj⟩ := fi22_classify t hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hfix : fixCard (Fi22Copy.iotaJ (xRep k)) = 126 := by
    rw [← hc, map_mul, map_mul, map_inv, hiota, fixCard_conj]
    exact fixCard_xPerm
  have hk3 : k = 3 := by
    have hf := Fi22Copy.fixN_xRep
    simp only [fixN_eq_card] at hf
    interval_cases k <;> omega
  subst hk3
  have h2 := @ShapeRkAt.of_equiv ↥CFSG.Sporadic.Fi22.J ↥CFSG.Sporadic.Fi22.J _ finite_J_tab inferInstance 3 Nat.prime_three
    STypeThree (fun _ _ => True) stypeThree_of_equiv hRk finite_J_tab (MulAut.conj c) t hJ
  rw [MulAut.conj_apply, hc] at h2
  exact h2

theorem shapeRkAt_xRep' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {k : ℕ} (hk : k < 4) :
    ShapeRkAt 3 STypeThree (fun _ _ => True) (xRep k) := by
  by_cases h3 : k = 3
  · subst h3
    exact shapeRkAt_xRep_three' hb
  · exact Or.inl (tabFi22_pConstrained_xRep (by omega))

theorem centShapeRk_J_level (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CentShapeRk 3 STypeThree (fun _ _ => True) CFSG.Sporadic.Fi22.J := by
  haveI := finite_J_tab
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨j, hj4, hconj⟩ := fi22_classify k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := @ShapeRkAt.of_equiv ↥CFSG.Sporadic.Fi22.J ↥CFSG.Sporadic.Fi22.J _ finite_J_tab inferInstance 3 Nat.prime_three
    STypeThree (fun _ _ => True) stypeThree_of_equiv hRk finite_J_tab (MulAut.conj c⁻¹) (xRep j)
    (shapeRkAt_xRep' hb hj4)
  have hk : (MulAut.conj c⁻¹) (xRep j) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

set_option maxRecDepth 100000 in
theorem srow_Fi22_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .Fi22 3 := by
  have hfin : Finite CFSG.Sporadic.Fi22.J := finite_J_tab
  have e : CFSG.Blueprint.NativeSporadic.Fi22 ≃* CFSG.Sporadic.Fi22.J := fi22EquivJ
  have hs : IsSimpleGroup CFSG.Sporadic.Fi22.J :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e.symm
  have hc : Nat.card CFSG.Sporadic.Fi22.J = 64561751654400 := CFSG.Sporadic.Fi22.card_J
  have hpr : ¬ (Nat.card CFSG.Sporadic.Fi22.J).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : CFSG.Sporadic.Fi22.J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple CFSG.Sporadic.Fi22.J _ hfin hs hpr
  have b : CFSG.Sporadic.Fi22.J ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group := e.symm.trans (hbr .Fi22).some
  exact @srow_of_centShape .Fi22 3 CFSG.Sporadic.Fi22.J _ hfin hs hOut b hnc Nat.prime_three (by norm_num)
    STypeThree (@CentShape.of_centShapeRk 3 STypeThree (fun _ _ => True) CFSG.Sporadic.Fi22.J _ (centShapeRk_J_level hb))
    fun _ _ h => h

end ClassAJ

end CFSG.HardMathSupport.Dickson.I271.SporAltFi22
