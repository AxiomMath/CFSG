module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.I1416Suz

open CFSG.HardMathSupport.Dickson.I271
open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.I1416Rows

section Quasi

variable {Q : Type} [Group Q] [Finite Q]

theorem compOK_of_centralizer_equiv {k : Q} {T : Type} [Group T]
    (e : ↥(Subgroup.centralizer ({k} : Set Q)) ≃* T) (hq : CFSG.Open.IsQuasisimple T)
    (hZ : IsPGroup 3 ↥(Subgroup.center T)) (hp : 3 ∣ Nat.card T)
    (hT : TypeOK 3 (T ⧸ Subgroup.center T)) : CompOK 3 k := by
  set C := Subgroup.centralizer ({k} : Set Q) with hC
  have hq' : CFSG.Open.IsQuasisimple ↥C := isQuasisimple_of_mulEquiv' e.symm hq
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
  refine compOK_of_shapeRkAt (Good := TypeThree) (Rk := fun _ _ => True) Nat.prime_three
    (Or.inr ⟨C, glaPComponent_of_normal_quasisimple le_rfl hLn hq' hcore,
      fun I hI => eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three le_rfl hLn hq' hcore
        hcent hI, ?_, trivial⟩) fun _ _ h => h
  exact TypeOK.of_mulEquiv ((pSimpleEquivCenterQuot C hcore).trans eq).symm hT

end Quasi

open CFSG.LieType.Multipliers.U43 in
theorem typeOK_U43 (hb : LieOrderBridge) {T : Type} [Group T] (e : T ≃* X₀) : TypeOK 3 T := by
  have hc : Nat.card T = 3265920 := by rw [Nat.card_congr e.toEquiv]; exact card_X₀
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  exact typeOK_of_not_chev (not_isChevSimple_two_of_card hb (a := 7) (m := 25515)
    (by rw [hc]; norm_num) (by decide) (by norm_num) (by norm_num))

section Entries

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Dickson.I271.TabSuzA
  CFSG.LieType.Multipliers.U43 CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.AGLEmbeddingD2.Wilson.Census228Spor CFSG.CosetTable
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM)
open scoped commutatorElement


theorem compOK_xA (hb : LieOrderBridge) : CompOK 3 (⟨fuseXA, fuseXA_mem⟩ : ↥suzM) := by
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
  refine compOK_of_centralizer_equiv e hq ?_ ?_ (typeOK_U43 hb eT)
  · have h3 : IsPGroup 3 ↥(Subgroup.zpowers (⟨fuseXA, aX_mem⟩ : ↥aSub)) := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
    exact h3.of_equiv (MulEquiv.subgroupCongr hcen.symm)
  · exact ⟨3265920, by rw [card_aSub]⟩

open TabSuzC in
theorem compOK_y : CompOK 3 (⟨yPerm, yPerm_mem⟩ : ↥suzM) := by
  obtain ⟨hCeq, hCcard⟩ := Cy_eq
  obtain ⟨hder, hEcard⟩ := Esub_derived
  obtain ⟨eE⟩ := nonempty_mulEquiv_Esub_alt6
  have hEC : Esub ≤ Subgroup.closure (permsA 1782 (cGens (levels ()))) := hCeq ▸ Esub_le_C
  haveI hs : IsSimpleGroup ↥Esub :=
    @MulEquiv.isSimpleGroup _ _ _ _ (alternatingGroup.isSimpleGroup (by simp)) eE
  haveI : Finite ↥Esub := Nat.finite_of_card_ne_zero (by rw [hEcard]; norm_num)
  have hnab : ∃ a b : ↥Esub, a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hEcard]; norm_num)
  have hsh : ShapeRkAt 3 TypeThree (fun _ _ => True) (⟨yPerm, yPerm_mem⟩ : ↥suzM) := by
    refine shapeRkAt_of_subgroup_data Nat.prime_three typeThree_of_equiv
      (fun _ _ _ _ _ h => h) suzM ⟨yPerm, yPerm_mem⟩ Esub Esub_le_C ?_ hs hnab
      (by rw [hEcard]; norm_num) (k := 2) ?_ (typeOK_A6 eE) trivial
    · intro g hg l hl
      rw [← hCeq] at hg
      have h1 : ⁅g, l⁆ ∈ ⁅Subgroup.closure (permsA 1782 (cGens (levels ()))),
          Subgroup.closure (permsA 1782 (cGens (levels ())))⁆ :=
        Subgroup.commutator_mem_commutator hg (hEC hl)
      have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
        rw [commutatorElement_def]
        group
      rw [h3]
      exact Esub.mul_mem (hder h1) hl
    · show Nat.card ↥(Subgroup.centralizer {yPerm} ⊓ suzM) = Nat.card ↥Esub * 3 ^ 2
      rw [← hCeq, hCcard, hEcard]
      norm_num
  exact compOK_of_shapeRkAt Nat.prime_three hsh fun _ _ h => h

theorem compOK_suzM (hb : LieOrderBridge) (k : ↥suzM) (hk : orderOf k = 3) : CompOK 3 k := by
  have hs3 : orderOf (k : Equiv.Perm (Fin 1782)) = 3 := by
    rw [Subgroup.orderOf_coe, hk]
  obtain ⟨h, hh, c, hc, e, he, hcon⟩ := suz_exists_conj_classes k.2 hs3
  have hrep : ∃ c' : ↥suzM, (c' : Equiv.Perm (Fin 1782)) = c ∧ c' ^ 3 = 1 ∧ CompOK 3 c' := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨⟨fuseXA, fuseXA_mem⟩, rfl, Subtype.ext (by simpa using fuseXA_pow), compOK_xA hb⟩
    · exact ⟨⟨fuseXB, fuseXB_mem⟩, rfl, Subtype.ext (by simpa using fuseXB_pow),
        compOK_of_pConstrained Nat.prime_three KDLevelSuz.pConstrained_xB⟩
    · exact ⟨⟨yPerm, yPerm_mem⟩, rfl, Subtype.ext (by simpa using yPerm_pow), compOK_y⟩
  obtain ⟨c', hc'val, hc'3, hok⟩ := hrep
  have hok' : CompOK 3 (c' ^ e) := by
    intro I hI
    rw [CFSG.Quasithin.Kleidman.centralizer_pow_eq hc'3 he] at hI
    exact hok I hI
  have hconj := CompOK.of_mulEquiv Nat.prime_three (MulAut.conj (⟨h, hh⟩ : ↥suzM)) hok'
  have hk' : (MulAut.conj (⟨h, hh⟩ : ↥suzM)) (c' ^ e) = k := by
    apply Subtype.ext
    rw [← hcon, ← hc'val]
    simp [MulAut.conj_apply]
  rw [hk'] at hconj
  exact hconj


set_option maxRecDepth 100000 in
theorem row_Suz_three (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) (hb : LieOrderBridge) :
    I1416SporRow .Suz 3 := by
  have e : CFSG.Blueprint.NativeSporadic.Suz ≃* ↥suzM := suzEquivM
  have hfin : Finite ↥suzM := inferInstance
  have hs : IsSimpleGroup ↥suzM :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Suz.isSimpleGroup_Suz e.symm
  have hc : Nat.card ↥suzM = 448345497600 :=
    (Nat.card_congr e.toEquiv).symm.trans CFSG.Sporadic.Suz.card_Suz
  have hpr : ¬ (Nat.card ↥suzM).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : ↥suzM, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥suzM _ hfin hs hpr
  have b : ↥suzM ≃* (TauCeti.CFSGIndex.sporadic .Suz).Group := e.symm.trans (hbr .Suz).some
  exact @row_of_model .Suz 3 ↥suzM _ hfin hs hOut b hnc (compOK_suzM hb)

end Entries

end CFSG.HardMathSupport.Dickson.I271.I1416Suz
