module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDL227SporRows
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi24LeafShape
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Assembly
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDL227Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem kdl227Row_of_carrier (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {s : TauCeti.SporadicName} (hfs : Finite (Carrier s) ∧ IsSimpleGroup (Carrier s))
    (hnp : ¬ (CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s).Prime)
    (h : NoL227At (Carrier s)) : KDL227SporRow s := by
  obtain ⟨hfin, hs⟩ := hfs
  have b : Carrier s ≃* (TauCeti.CFSGIndex.sporadic s).Group := (hbr s).some
  have hcard : Nat.card (Carrier s) = CFSG.HardMathSupport.Solomon.Coordinator.sporOrd s :=
    (Nat.card_congr b.toEquiv).trans (hOrd s)
  have hnc := CFSG.HardMathSupport.Dickson.Sec6.I1431.exists_not_comm_of_simple_not_prime
    (G := Carrier s) (by rw [hcard]; exact hnp)
  exact kdl227Row_of_model hOut b hnc h

theorem noL227At_of_centShapeRk {Q : Type} [Group Q] [Finite Q]
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShapeRk 3 Good Rk Q)
    (hnot : ∀ (T : Type) [Group T], Good T → ¬ catalogIs T (onLie (isL2 27))) : NoL227At Q := by
  intro k hk1 hk3 J hJ hL
  rcases h k hk1 hk3 with hc | ⟨J0, -, huniq, hg, -⟩
  · exact KDSpor.false_of_glaPComponent_of_pConstrained Nat.prime_three hc hJ
  · obtain rfl := huniq J hJ
    exact hnot _ hg hL

theorem not_catalogIs_L227_of_goodSpor_Suz
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    {T : Type} [Group T] (h : CFSG.HardMathSupport.Dickson.I271.GoodSpor 3 [.Suz] T) :
    ¬ catalogIs T (onLie (isL2 27)) := by
  intro hL
  rcases h with h | h | ⟨S, hS, ⟨f⟩⟩
  · exact not_catalogIs_L227_of_leafType h hL
  · exact not_catalogIs_L227_of_A6 h hL
  · rw [List.mem_singleton] at hS
    subst hS
    have hc := (Nat.card_congr f.toEquiv).trans (hOrd .Suz)
    rw [card_of_catalogIs_L227 hL] at hc
    simp only [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd] at hc
    norm_num at hc

section RowFi24


theorem kdl227Row_Fi24 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hfs : Finite (Carrier .Fi24Prime) ∧ IsSimpleGroup (Carrier .Fi24Prime)) :
    KDL227SporRow .Fi24Prime := by
  haveI := hfs.1
  exact kdl227Row_of_carrier hOut hbr hOrd hfs
    (by simp only [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderFi24Prime]; norm_num)
    (noL227At_of_centShape CFSG.HardMathSupport.Dickson.I271.leafShape_Fi24_three
      fun _ _ h => not_catalogIs_L227_of_leafType h)

end RowFi24

section RowCo1


theorem kdl227Row_Co1 (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hfs : Finite (Carrier .Co1) ∧ IsSimpleGroup (Carrier .Co1)) :
    KDL227SporRow .Co1 := by
  haveI := hfs.1
  exact kdl227Row_of_carrier hOut hbr hOrd hfs
    (by simp only [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd, CFSG.Open.orderCo1]; norm_num)
    (noL227At_of_centShapeRk (CFSG.HardMathSupport.Dickson.I271.TabCo1.centShapeRk_Co1_three hbr
      (CFSG.HardMathSupport.Dickson.I271.TabCo1.co1ThreeAShape_holds hOut hbr))
      fun _ _ h => not_catalogIs_L227_of_goodSpor_Suz hOrd h)

end RowCo1

section Closed


theorem kdl227Row_Co1_holds : KDL227SporRow .Co1 :=
  kdl227Row_Co1 CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    (CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M .Co1 (by decide))

theorem kdl227Row_Fi24_holds : KDL227SporRow .Fi24Prime :=
  kdl227Row_Fi24 CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    (CFSG.Sporadic.Bridge.carrier_finite_simple_of_ne_M .Fi24Prime (by decide))

end Closed

end CFSG.LocalAnalysis.GLTheoremA.KDL227Rows
