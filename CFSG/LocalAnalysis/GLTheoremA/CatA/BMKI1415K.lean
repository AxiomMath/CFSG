module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKSporDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKI1415Other
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteAll
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteB
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteM
public import CFSG.HardMathSupport.Dickson.BMRows.M11Row
public import CFSG.HardMathSupport.Dickson.BMRows.M13AOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.BMRows

section BMKI1415K

theorem i1415Row_of_K
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (s : TauCeti.SporadicName) (p : ℕ)
    (hB : s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B))
    (hM : s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) :
    I1415Rows.I1415Row s p := by
  by_cases hsB : s = .B
  · subst hsB
    exact arows_B_all (arow_B_three_of_kGroup (hB rfl)) (arow_B_five_of_kGroup (hB rfl))
      arow_B_seven p
  by_cases hsM : s = .M
  · subst hsM
    exact arows_M_all (arow_M_three_of_kGroup (hM rfl)) (arow_M_five_of_kGroup (hM rfl))
      arow_M_seven i1415Row_M_eleven i1415Row_M_thirteen p
  exact I1415Rows.i1415Row_of_ne_BM hOut hbr hOrd hb hsB hsM p

theorem i1415SporSK_holds
    : I1415SporSK := by
  intro S _ _ s he hB hM p hp hp2 β hβ hβ1 J hJ m hm hA
  exact (i1415Row_of_K CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds s p hB hM) S he hp hp2 β hβ hβ1 J hJ m hm hA

end BMKI1415K

end CFSG.LocalAnalysis.GLTheoremA
