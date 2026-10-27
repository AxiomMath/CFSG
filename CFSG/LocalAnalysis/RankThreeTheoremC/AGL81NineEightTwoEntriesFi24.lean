module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra
import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Gen
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesThree
import CFSG.Sporadic.Schreier.Fi24Schreier
public import CFSG.Sporadic.Fi24.Setup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 CFSG.Sporadic.Fi24
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

theorem kFactNineThreeNoTwoAt_of_sevenModel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {i : TauCeti.CFSGIndex} {X : Type} [Group X] [Finite X] (hM : Nonempty (X ≃* i.Group))
    {Q : Subgroup X} {z : X} {«gens» : Set X} (D : SevenModel X p Q z «gens»)
    (hcen : Subgroup.center X = ⊥) (hout : Nat.card (Outer X) ≤ 2) {E : Subgroup X}
    (hE : IsElemAbelian p E) (hE2 : Nat.card E = p ^ 2) : KFactNineThreeNoTwoAt p i := by
  have hp : p.Prime := Fact.out
  refine kFactNineThreeNoTwoAt_of_model_coprime hp hp2 hM hE.isPGroup fun V hV hN => ?_
  exact D.noSig hp2 hcen hout (E.map (MulAut.conj : X →* MulAut X)) (hE.map _)
    (by rw [Subgroup.card_map_of_injective (conj_injective_of_center_bot_sg hcen), hE2]) V
    (hp.coprime_iff_not_dvd.2 hV) hN

theorem kFactNineThreeNoTwoAt_fi24 :
    KFactNineThreeNoTwoAt 7 (.sporadic .Fi24Prime) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcx : Commute Fi7.C7 Fi7.X7 := Fi7.fi7_cube.2.2.2.1
  have hc7 : Fi7.C7 ^ 7 = 1 := Fi7.C7_pow_seven
  have hx7 : Fi7.X7 ^ 7 = 1 := Fi7.fi7_cube.1
  have hxc : Fi7.X7 ∉ Subgroup.zpowers Fi7.C7 := by
    simpa [Fi7.cube7] using Fi7.cube7_not_mem_zpowers (t := 49) (by norm_num) (by norm_num)
  have hE : IsElemAbelian 7 (Subgroup.closure ({Fi7.C7, Fi7.X7} : Set J)) :=
    @IsElemAbelian.closure_of_commute J (Subgroup.toGroup _) 7 _
      (by rintro a (rfl | rfl) b (rfl | rfl); exacts [rfl, hcx, hcx.symm, rfl])
      (by rintro a (rfl | rfl); exacts [hc7, hx7])
  have hE49 : Nat.card (Subgroup.closure ({Fi7.C7, Fi7.X7} : Set J)) = 7 ^ 2 :=
    card_closure_pair_sq hcx hc7 hx7 Fi7.C7_ne_one hxc
  have hout : Nat.card (Outer J) ≤ 2 :=
    le_of_eq ((Nat.card_congr (@equivalence CFSG.Blueprint.NativeSporadic.Fi24prime J
      Units.instGroup (Subgroup.toGroup _) fi24EquivJ).toEquiv).symm.trans
      CFSG.Sporadic.Schreier.Fi24.card_outer_fi24prime)
  have D : SevenModel J 7 Fi7.Q7 Fi7.C7 Fi7.gens7 :=
    ⟨Fi7.sevenLine_c, Fi7.Q7_sylow, Fi7.fi7_gens_top, Fi7.fi7_gens_good,
      Fi7.fi7_rankOK Fi7.fi7_order_four⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  have hM : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) :=
    ⟨fi24EquivJ.symm.trans e⟩
  exact @kFactNineThreeNoTwoAt_of_sevenModel 7 _ (by norm_num) _ J (Subgroup.toGroup _)
    inferInstance hM _ _ _ D center_J hout _ hE hE49

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
