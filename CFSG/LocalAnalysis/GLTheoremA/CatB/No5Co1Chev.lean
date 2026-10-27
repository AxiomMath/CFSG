module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.No5Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatB.List93IdNot2b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA.No5

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator

section Co1Chev


theorem card_co1 : Nat.card (TauCeti.CFSGIndex.sporadic .Co1).Group = CFSG.Open.orderCo1 :=
  sporadicOrdersTable_holds .Co1

theorem co1_not_chev2 {S : Type} [Group S] (e : S ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) :
    ¬ IsChevSimple 2 S :=
  CFSG.LocalAnalysis.GLTheoremA.List93.not_chev2_spor (s := .Co1) (a := 21)
    (m := 1982582476875) ⟨991291238437, by norm_num⟩ (by norm_num)
    (by norm_num [sporOrd, CFSG.Open.orderCo1]) (by norm_num) (by decide +kernel) e

theorem co1_not_chev_of_odd {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) : ¬ IsChevSimple q S := by
  have hT : Nat.card S = CFSG.Open.orderCo1 := (Nat.card_congr e.toEquiv).trans card_co1
  by_cases hdvd : q ∣ CFSG.Open.orderCo1
  · rcases prime_dvd_co1 hq hdvd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hq2
    · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 9)
        (m := 2 ^ 21 * 5 ^ 4 * 7 ^ 2 * 11 * 13 * 23) hq hq2
        (by rw [hT]; norm_num [CFSG.Open.orderCo1]) (by norm_num) (by norm_num)
        (fun _ => by norm_num [CFSG.Open.orderCo1]) (fun h => absurd h (by norm_num))
    · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 4)
        (m := 2 ^ 21 * 3 ^ 9 * 7 ^ 2 * 11 * 13 * 23) hq hq2
        (by rw [hT]; norm_num [CFSG.Open.orderCo1]) (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) (fun _ => by norm_num [CFSG.Open.orderCo1])
    · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 2)
        (m := 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 11 * 13 * 23) hq hq2
        (by rw [hT]; norm_num [CFSG.Open.orderCo1]) (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 1)
        (m := 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 13 * 23) hq hq2
        (by rw [hT]; norm_num [CFSG.Open.orderCo1]) (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 1)
        (m := 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 23) hq hq2
        (by rw [hT]; norm_num [CFSG.Open.orderCo1]) (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
    · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
        CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 1)
        (m := 2 ^ 21 * 3 ^ 9 * 5 ^ 4 * 7 ^ 2 * 11 * 13) hq hq2
        (by rw [hT]; norm_num [CFSG.Open.orderCo1]) (by norm_num) (by norm_num)
        (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
  · exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds (a := 0)
      (m := CFSG.Open.orderCo1) hq hq2 (by rw [hT]; simp) hdvd
      (by norm_num [CFSG.Open.orderCo1])
      (fun h => absurd (by rw [h]; norm_num [CFSG.Open.orderCo1]) hdvd)
      (fun h => absurd (by rw [h]; norm_num [CFSG.Open.orderCo1]) hdvd)

theorem co1_not_chev_of_prime {q : ℕ} (hq : q.Prime) {S : Type} [Group S] [Finite S]
    (e : S ≃* (TauCeti.CFSGIndex.sporadic .Co1).Group) : ¬ IsChevSimple q S := by
  by_cases h2 : q = 2
  · subst h2
    exact co1_not_chev2 e
  · exact co1_not_chev_of_odd hq h2 e

end Co1Chev

end CFSG.LocalAnalysis.GLTheoremA.No5
