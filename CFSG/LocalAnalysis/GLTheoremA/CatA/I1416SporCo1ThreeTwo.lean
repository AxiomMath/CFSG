module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAll3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.LieOrderGrid

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

set_option maxRecDepth 100000 in
theorem lieOrderFormula_ne_suz {d : TauCeti.LieTypeIndex} (hd : d.Valid) :
    CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d ≠ 448345497600 :=
  LieGrid.lieOrderFormula_ne_of_grid [2, 3, 5, 7, 11, 13] 448345497600 (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) hd

theorem not_isChevSimple_two_of_card_suz
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type} [Group T]
    (hc : Nat.card T = 448345497600) : ¬ IsChevSimple 2 T := by
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d => exact lieOrderFormula_ne_suz d.2 ((hb d T ⟨e⟩).symm.trans hc)
    | _ => exact hi.elim
  · cases i with
    | lie d => exact lieOrderFormula_ne_suz d.2 ((hb d T ⟨e⟩).symm.trans hc)
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hc] at hcn
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num [Nat.factorial] at hcn
    | _ => exact hi.elim

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.Multipliers.U43 CFSG.LocalAnalysis.GLTheoremA.I1416Rows

theorem row_Co1_three (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : I1416SporRow .Co1 3 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  have hC := tabCo1_centShapeRk_three_good (Good := fun T _ => TypeOK 3 T)
    (fun _ _ _ _ e h => TypeOK.of_mulEquiv e h)
    (fun T _ e => by
      have hc : Nat.card T = 3265920 := (Nat.card_congr e.toEquiv).trans card_X₀
      haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
      exact typeOK_of_not_chev (not_isChevSimple_two_of_card hb (a := 7) (m := 25515)
        (by rw [hc]; norm_num) (by decide) (by norm_num) (by norm_num)))
    (by
      haveI : Finite ↥(alternatingGroup (Fin 9)) := inferInstance
      exact typeOK_of_not_chev (not_isChevSimple_two_of_card_181440 hb card_alt_nine))
    (fun _ _ hc _ => typeOK_of_not_chev (not_isChevSimple_two_of_card_suz hb hc)) (hbr .Suz)
  exact @row_of_model .Co1 3 ↥GA _ hfin hs hOut b hnc fun x hx =>
    CFSG.LocalAnalysis.GLTheoremA.I1416Rows.compOK_of_centShape Nat.prime_three
      (CentShape.of_centShapeRk hC) (fun _ _ h => h) hx

end CFSG.HardMathSupport.Dickson.I271.TabCo1

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

@[expose] def I1416SporResidual5 : Prop :=
  (∀ p, I1416SporRow .B p) ∧ (∀ p, I1416SporRow .M p) ∧ I1416SporRow .Fi24Prime 5

theorem i1416TwoSporS_of_residual5
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (hres : I1416SporResidual5) : I1416TwoSporS := by
  obtain ⟨hB, hM, hF5⟩ := hres
  exact i1416TwoSporS_of_residual4 hOut hbr hOrd hb
    ⟨hB, hM, CFSG.HardMathSupport.Dickson.I271.TabCo1.row_Co1_three hOut hbr hb, hF5⟩

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows
