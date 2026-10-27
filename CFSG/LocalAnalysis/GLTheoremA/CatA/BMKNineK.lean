module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKSporDefs
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteB
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.BMRows

section BMKNineK

theorem nineRow_of_K
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (s : TauCeti.SporadicName)
    (hB : s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B))
    (hM : s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M))
    (hHN : s ≠ .HN) (hCo : s ≠ .Co1) : SporAltRows.NineRow s := by
  by_cases hsB : s = .B
  · subst hsB
    exact SporAltRows.nineRow_of_srow (srow_B_three_of_kGroup (hB rfl))
  by_cases hsM : s = .M
  · subst hsM
    exact SporAltRows.nineRow_of_srow (srow_M_three_of_kGroup (hM rfl))
  by_cases hsHe : s = .He
  · subst hsHe
    exact SporAltRows.nineRow_of_grow (fun T _ hT => SporAltRows.not_equiv_alt_of_card (by norm_num)
      (fun h => absurd (h ▸ hT) (by decide))) (SporAltRows.grow_He_three hOut hbr)
  exact SporAltRows.nineRow_of_srow (SporAltRows.srow_three hOut hbr hOrd hb hsB hsM hsHe hHN hCo)

theorem i1415NineSporSK_holds
    : I1415NineSporSK := by
  intro S _ _ s he hB hM β hβ hβ1 J hJ hA
  by_cases hHN : s = .HN
  · exact Or.inl hHN
  by_cases hCo : s = .Co1
  · exact Or.inr hCo
  exact ((nineRow_of_K CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds s hB hM hHN hCo) S he β hβ hβ1 J hJ hA).elim

end BMKNineK

end CFSG.LocalAnalysis.GLTheoremA
