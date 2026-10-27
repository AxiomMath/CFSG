module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKSporDefs
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteB
public import CFSG.HardMathSupport.Dickson.BMRows.ConcreteM
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporHeSeven

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Dickson.BMRows

section BMKAltK

theorem altRow7_of_K
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (s : TauCeti.SporadicName)
    (hB : s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B))
    (hM : s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) : SporAltRows.AltRow 7 s := by
  by_cases hsB : s = .B
  · subst hsB
    exact SporAltRows.altRow_of_srow (by norm_num) (srow_B_three_of_kGroup (hB rfl))
  by_cases hsM : s = .M
  · subst hsM
    exact SporAltRows.altRow_of_srow (by norm_num) (srow_M_three_of_kGroup (hM rfl))
  by_cases hsHe : s = .He
  · subst hsHe
    exact SporAltRows.altRow_He_seven hOut hbr
  by_cases hsHN : s = .HN
  · exact hsHN ▸ (SporAltRows.altRow_HN_Co1 hOut hbr (Or.inl rfl)).1
  by_cases hsCo : s = .Co1
  · exact hsCo ▸ (SporAltRows.altRow_HN_Co1 hOut hbr (Or.inl rfl)).2
  exact SporAltRows.altRow_of_srow (by norm_num)
    (SporAltRows.srow_three hOut hbr hOrd hb hsB hsM hsHe hsHN hsCo)

theorem altRow8_of_K
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (s : TauCeti.SporadicName)
    (hB : s = .B → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .B))
    (hM : s = .M → CFSG.Open.IsKGroup (CFSG.Blueprint.NativeSporadic.Carrier .M)) : SporAltRows.AltRow 8 s := by
  by_cases hsB : s = .B
  · subst hsB
    exact SporAltRows.altRow_of_srow (by norm_num) (srow_B_three_of_kGroup (hB rfl))
  by_cases hsM : s = .M
  · subst hsM
    exact SporAltRows.altRow_of_srow (by norm_num) (srow_M_three_of_kGroup (hM rfl))
  by_cases hsHe : s = .He
  · subst hsHe
    exact SporAltRows.altRow_of_grow (by norm_num) (fun T _ hT => SporAltRows.not_equiv_alt_of_card (by norm_num)
      (fun h => absurd (h ▸ hT) (by decide))) (SporAltRows.grow_He_three hOut hbr)
  by_cases hsHN : s = .HN
  · exact hsHN ▸ (SporAltRows.altRow_HN_Co1 hOut hbr (Or.inr rfl)).1
  by_cases hsCo : s = .Co1
  · exact hsCo ▸ (SporAltRows.altRow_HN_Co1 hOut hbr (Or.inr rfl)).2
  exact SporAltRows.altRow_of_srow (by norm_num)
    (SporAltRows.srow_three hOut hbr hOrd hb hsB hsM hsHe hsHN hsCo)

theorem i1415SevenSporSK_holds
    : I1415SevenSporSK := by
  intro S _ _ s he hB hM β hβ hβ1 J hJ hA
  exact (altRow7_of_K CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds s hB hM) S he β hβ hβ1 J hJ hA

theorem i1422SporSK_holds
    : I1422SporSK := by
  intro S _ _ s he hB hM β hβ hβ1 J hJ hA
  exact (altRow8_of_K CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds s hB hM) S he β hβ hβ1 J hJ hA

end BMKAltK

end CFSG.LocalAnalysis.GLTheoremA
