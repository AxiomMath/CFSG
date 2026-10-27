module

public import CFSG.HardMathSupport.Dickson.BMRows.M11Shape
public import CFSG.Sporadic.Bridge.MonsterModelsGriess

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows

open CFSG.Monster CFSG.Monster.Generated CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven CFSG.Open
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Dickson.BMRows.M11 (CentElevenBound)
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge lieOrderBridge_holds)

section MRows


theorem levelOK_gmat_eleven (h : CentElevenBound) {s : Gmat} (hs : orderOf s = 11) :
    KDSpor.LevelOK 11 s :=
  KDSpor.levelOK_of_shapeRkAt (by norm_num) (M11.shapeRkAt_gmat_eleven h hs) M11.kLevel_goodM12

theorem compOK_gmat_eleven (h : CentElevenBound) {s : Gmat} (hs : orderOf s = 11) :
    I1416Rows.CompOK 11 s :=
  I1416Rows.compOK_of_shapeRkAt (by norm_num) (M11.shapeRkAt_gmat_eleven h hs)
    (M11.typeOK_goodM12 sporadicOuterLeTwo_holds)

theorem qcompOK_gmat_eleven (h : CentElevenBound) {s : Gmat} (hs : orderOf s = 11) :
    I1416QRows.QCompOK 11 s :=
  I1416QRows.qcompOK_of_shapeRkAt (by norm_num) (M11.shapeRkAt_gmat_eleven h hs)
    (M11.qtypeOK_goodM12 sporadicOuterLeTwo_holds)

theorem kdSporRow_M_eleven (h : CentElevenBound) : KDSporRow .M 11 := by
  haveI : IsSimpleGroup Gmat := generated_rational_group_finite_simple.2.1
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact KDSpor.kdSporRow_of_levelOK sporadicOuterLeTwo_holds b ⟨_, _, w0_e0_ne⟩ (by norm_num)
    (by norm_num) fun k hk => levelOK_gmat_eleven h hk

theorem row_M_eleven (h : CentElevenBound) : I1416Rows.I1416SporRow .M 11 := by
  haveI : IsSimpleGroup Gmat := generated_rational_group_finite_simple.2.1
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact I1416Rows.row_of_model sporadicOuterLeTwo_holds b ⟨_, _, w0_e0_ne⟩
    fun k hk => compOK_gmat_eleven h hk

theorem qrow_M_eleven (h : CentElevenBound) : I1416QRows.I1416QRow .M 11 := by
  haveI : IsSimpleGroup Gmat := generated_rational_group_finite_simple.2.1
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact I1416QRows.qrow_of_model sporadicOuterLeTwo_holds b ⟨_, _, w0_e0_ne⟩
    fun k hk => qcompOK_gmat_eleven h hk

end MRows

section CRow


theorem ccompOK_gmat_eleven (hb : LieOrderBridge) (h : CentElevenBound) {s : Gmat}
    (hs : orderOf s = 11) : Chev2Rows.CCompOK 11 s :=
  Chev2Rows.ccompOK_of_shapeRkAt (by norm_num) (M11.shapeRkAt_gmat_eleven h hs)
    (M11.ctypeOK_goodM12 hb)

theorem crow_M_eleven (h : CentElevenBound) : Chev2Rows.CRow .M 11 := by
  haveI : IsSimpleGroup Gmat := generated_rational_group_finite_simple.2.1
  obtain ⟨b⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  exact Chev2Rows.crow_of_model sporadicOuterLeTwo_holds b ⟨_, _, w0_e0_ne⟩
    fun k hk => ccompOK_gmat_eleven lieOrderBridge_holds h hk

end CRow

end CFSG.HardMathSupport.Dickson.BMRows
