module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Three
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1415ASporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRowsA

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.Multipliers.U43


theorem card_alt_nine : Nat.card ↥(alternatingGroup (Fin 9)) = 181440 :=
  (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt 9 (by norm_num)).trans (by decide)

theorem arow_Co1_three (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CFSG.LocalAnalysis.GLTheoremA.I1415Rows.I1415Row .Co1 3 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  have hC := tabCo1_centShapeRk_three_good
    (Good := CFSG.LocalAnalysis.GLTheoremA.I1415Rows.ATypeThree)
    CFSG.LocalAnalysis.GLTheoremA.I1415Rows.atypeThree_of_equiv
    (fun _ _ e => CFSG.LocalAnalysis.GLTheoremA.I1415Rows.atypeOK_of_card_eq
      ((Nat.card_congr e.toEquiv).trans card_X₀))
    (CFSG.LocalAnalysis.GLTheoremA.I1415Rows.atypeOK_of_card_eq card_alt_nine)
    (fun _ _ hc _ => CFSG.LocalAnalysis.GLTheoremA.I1415Rows.atypeOK_of_card_eq hc) (hbr .Suz)
  exact @CFSG.LocalAnalysis.GLTheoremA.I1415Rows.arow_of_centShape .Co1 3 ↥GA _ hfin hs hOut b hnc
    Nat.prime_three (by norm_num) _ (CentShape.of_centShapeRk hC) fun _ _ h => h

theorem qrow_Co1_three (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .Co1 3 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  have hQ : ∀ (T : Type) [Group T] {N : ℕ}, Nat.card T = N → 0 < N → N < 2 ^ 200 →
      (∀ q ∈ N.primeFactorsList, q ≠ 2 → q ≠ 3 → ∀ k < 200, q ^ k ∣ N → q ^ (3 * k) ≤ N) →
      CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeThree T := fun T _ N hT hN0 hNlt hN => by
    haveI : Finite T := Nat.finite_of_card_ne_zero (by omega)
    exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeOK_of_card hb hT hN0 hNlt hN
      (fun h => absurd rfl h) (fun _ => by
        intro h5
        subst h5
        exact absurd hN (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel))
  have hC := tabCo1_centShapeRk_three_good
    (Good := CFSG.LocalAnalysis.GLTheoremA.I1416QRows.QTypeThree)
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qtypeThree_of_equiv
    (fun T _ e => hQ T ((Nat.card_congr e.toEquiv).trans card_X₀) (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel))
    (hQ _ card_alt_nine (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel))
    (fun T _ hc _ => hQ T hc (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel)) (hbr .Suz)
  exact @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_centShape .Co1 3 ↥GA _ hfin hs hOut b hnc
    Nat.prime_three (by norm_num) _ (CentShape.of_centShapeRk hC) fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.TabCo1
