module

public import CFSG.HardMathSupport.Dickson.BMRows.M13Inf
public import CFSG.HardMathSupport.Dickson.BMRows.M13L33
public import CFSG.HardMathSupport.Dickson.BMRows.M13Shape
public import CFSG.HardMathSupport.Dickson.BMRows.M13Types
public import CFSG.HardMathSupport.Dickson.BMRows.M13AOrder

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open Subgroup CFSG.Blueprint CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Existence
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenB
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
  CFSG.HardMathSupport.Dickson.Sec6.I1431
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Dickson.I271 (ShapeRkAt)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge lieOrderBridge_holds)

section Gmat


theorem shapeRkAt_xE (φ : Gmat ≃* MGriess) :
    ShapeRkAt 13 M13L33.GoodL33 M13L33.TrivRk (gw thirteenX) := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨Q, hQC, ⟨e⟩⟩ := M13L33.exists_l33_xE
  exact M13Shape.shapeRkAt_of_l33 orderOf_xE hQC e (card_centralizer_xE_le φ)
    fun u hu2 hu1 hux => card_cent_inf_xE_le φ hu2 hu1 hux

theorem shapeRkAt_conj_xE (φ : Gmat ≃* MGriess) {s m : Gmat} {k : ℕ} (hk : k % 13 ≠ 0)
    (h : m * s * m⁻¹ = gw thirteenX ^ k) :
    ShapeRkAt 13 M13L33.GoodL33 M13L33.TrivRk s := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hk1 : gw thirteenX ^ k ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_xE] at this
    exact hk (Nat.mod_eq_zero_of_dvd this)
  have h1 : ShapeRkAt 13 M13L33.GoodL33 M13L33.TrivRk (gw thirteenX ^ k) :=
    CFSG.HardMathSupport.Dickson.I271.ShapeRkAt.of_centralizer_eq
      (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime orderOf_xE
        hk1).symm (shapeRkAt_xE φ)
  have h2 := CFSG.HardMathSupport.Dickson.I271.ShapeRkAt.of_equiv (by norm_num)
    (fun _ _ _ _ f hg => M13L33.GoodL33.of_equiv f hg) (fun _ _ _ _ _ _ => trivial)
    (MulAut.conj m⁻¹) h1
  have hs : (MulAut.conj m⁻¹) (gw thirteenX ^ k) = s := by
    rw [← h]
    simp [MulAut.conj_apply, mul_assoc]
  rwa [hs] at h2

theorem levelOK_gmat_thirteen (φ : Gmat ≃* MGriess) {s : Gmat} (hs : orderOf s = 13) :
    KDSpor.LevelOK 13 s := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
  · exact levelOK_conj_c13 hk h
  · exact KDSpor.levelOK_of_shapeRkAt (by norm_num) (shapeRkAt_conj_xE φ hk h)
      M13Types.kLevel_goodL33

theorem compOK_gmat_thirteen (φ : Gmat ≃* MGriess) {s : Gmat} (hs : orderOf s = 13) :
    I1416Rows.CompOK 13 s := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
  · exact compOK_conj_c13 hk h
  · exact I1416Rows.compOK_of_shapeRkAt (by norm_num) (shapeRkAt_conj_xE φ hk h)
      M13Types.typeOK_goodL33

theorem qcompOK_gmat_thirteen (φ : Gmat ≃* MGriess) {s : Gmat} (hs : orderOf s = 13) :
    I1416QRows.QCompOK 13 s := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
  · exact qcompOK_conj_c13 hk h
  · exact I1416QRows.qcompOK_of_shapeRkAt (by norm_num) (shapeRkAt_conj_xE φ hk h)
      M13Types.qtypeOK_goodL33

theorem ccompOK_gmat_thirteen (hb : LieOrderBridge) (φ : Gmat ≃* MGriess) {s : Gmat}
    (hs : orderOf s = 13) : Chev2Rows.CCompOK 13 s := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  obtain ⟨m, k, hk, h | h⟩ := census_thirteen s hs
  · exact Chev2Rows.ccompOK_of_no_comp (noComp_conj_c13 hk h)
  · exact Chev2Rows.ccompOK_of_shapeRkAt (by norm_num) (shapeRkAt_conj_xE φ hk h)
      (M13Types.ctypeOK_goodL33 hb)

end Gmat

section MRows


theorem exists_M_equivs : Nonempty ((Gmat ≃* MGriess) × (Gmat ≃* Carrier .M)) := by
  obtain ⟨e₀⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_griess_y443Derived
  let e : CFSG.Monster.Existence.MGriess ≃* Carrier .M := e₀
  have φ := CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth
  exact ⟨(φ.symm, φ.symm.trans e)⟩

theorem levelOK_M_thirteen : ∀ k : Carrier .M, orderOf k = 13 → KDSpor.LevelOK 13 k := by
  obtain ⟨⟨ψ, eG⟩⟩ := exists_M_equivs
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  intro k hk
  have hs : orderOf (eG.symm k) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hk
  have h := KDSpor.LevelOK.of_mulEquiv (by norm_num : Nat.Prime 13) eG
    (levelOK_gmat_thirteen ψ hs)
  rwa [MulEquiv.apply_symm_apply] at h

theorem compOK_M_thirteen : ∀ k : Carrier .M, orderOf k = 13 → I1416Rows.CompOK 13 k := by
  obtain ⟨⟨ψ, eG⟩⟩ := exists_M_equivs
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  intro k hk
  have hs : orderOf (eG.symm k) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hk
  have h := I1416Rows.CompOK.of_mulEquiv (by norm_num : Nat.Prime 13) eG
    (compOK_gmat_thirteen ψ hs)
  rwa [MulEquiv.apply_symm_apply] at h

theorem qcompOK_M_thirteen : ∀ k : Carrier .M, orderOf k = 13 → I1416QRows.QCompOK 13 k := by
  obtain ⟨⟨ψ, eG⟩⟩ := exists_M_equivs
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  intro k hk
  have hs : orderOf (eG.symm k) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hk
  have h := I1416QRows.QCompOK.of_mulEquiv (by norm_num : Nat.Prime 13) eG
    (qcompOK_gmat_thirteen ψ hs)
  rwa [MulEquiv.apply_symm_apply] at h

theorem ccompOK_M_thirteen (hb : LieOrderBridge) :
    ∀ k : Carrier .M, orderOf k = 13 → Chev2Rows.CCompOK 13 k := by
  obtain ⟨⟨ψ, eG⟩⟩ := exists_M_equivs
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  haveI : Finite (Carrier .M) := Finite.of_equiv Gmat eG.toEquiv
  intro k hk
  have hs : orderOf (eG.symm k) = 13 := by
    rw [MulEquiv.orderOf_eq]
    exact hk
  have h := Chev2Rows.CCompOK.of_mulEquiv (by norm_num : Nat.Prime 13) eG
    (ccompOK_gmat_thirteen hb ψ hs)
  rwa [MulEquiv.apply_symm_apply] at h

theorem kdSporRow_M_thirteen : KDSporRow .M 13 := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact KDSpor.kdSporRow_of_levelOK sporadicOuterLeTwo_holds b hnc (by norm_num) (by norm_num)
    levelOK_M_thirteen

theorem row_M_thirteen : I1416Rows.I1416SporRow .M 13 := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact I1416Rows.row_of_model sporadicOuterLeTwo_holds b hnc compOK_M_thirteen

theorem qrow_M_thirteen : I1416QRows.I1416QRow .M 13 := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact I1416QRows.qrow_of_model sporadicOuterLeTwo_holds b hnc qcompOK_M_thirteen

end MRows

section CRow


theorem crow_M_thirteen : Chev2Rows.CRow .M 13 := by
  obtain ⟨_, _, ⟨b⟩, hnc⟩ := model_M
  exact Chev2Rows.crow_of_model sporadicOuterLeTwo_holds b hnc
    (ccompOK_M_thirteen lieOrderBridge_holds)

end CRow

end CFSG.HardMathSupport.Dickson.BMRows
