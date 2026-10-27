module

public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XNArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4XN

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem not_weakExc_of_isD4two (hb : CatDistinct.OrderBridge)
    (hM22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520)
    {S : Type} [Group S] [Finite S] (h4 : catalogIs S S9.isD4two) :
    ¬ catalogIs S weakExcIndex := by
  intro hw
  have hN : Nat.card S = 174182400 := CatDistinct.card_isD4two hb h4
  obtain ⟨i, hi, ⟨e⟩⟩ := hw
  cases i with
  | cyclic p hp => simp [weakExcIndex, excIndex] at hi
  | alternating n hn =>
    have h6 : n = 6 ∨ n = 7 := by simpa [weakExcIndex, excIndex] using hi
    have hc := CatDistinct.card_alternating_of_iso hn e
    rw [hN] at hc
    rcases h6 with rfl | rfl
    · norm_num [Nat.factorial] at hc
    · norm_num [Nat.factorial] at hc
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M22 := by simpa [weakExcIndex, excIndex] using hi
    subst hs
    have hc : Nat.card S = 443520 := by rw [Nat.card_congr e.toEquiv]; exact hM22
    rw [hN] at hc
    norm_num at hc
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    have hord : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d1 :=
      hb ⟨d1, hv⟩ S ⟨e⟩
    rw [hN] at hord
    cases d1 with
    | A r q =>
      rcases r with _ | _ | _ | r
      · simp [weakExcIndex, excIndex] at hi
      · obtain ⟨hp2, -, hexp⟩ : q.p = 2 ∧ Odd q.exponent ∧ 1 < q.exponent := by
          simpa [weakExcIndex, excIndex] using hi
        have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
        have hn2 : q.card % 2 = 0 := by
          rw [hcard]
          exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
        exact A1_ne q.card hn2 (CatDistinct.two_le_card q) hord.symm
      · have h9 : q.card % 9 = 4 ∨ q.card % 9 = 7 := by
          simpa [weakExcIndex, excIndex] using hi
        exact A2_ne q.card h9 hord.symm
      · simp [weakExcIndex, excIndex] at hi
    | twistedA r q =>
      rcases r with _ | _ | r
      · simp [weakExcIndex, excIndex] at hi
      · simp [weakExcIndex, excIndex] at hi
      · rcases r with _ | r
        · have h9 : q.card % 9 = 2 ∨ q.card % 9 = 5 := by
            simpa [weakExcIndex, excIndex] using hi
          exact TA2_ne q.card h9 hord.symm
        · simp [weakExcIndex, excIndex] at hi
    | B _ _ => simp [weakExcIndex, excIndex] at hi
    | C _ _ => simp [weakExcIndex, excIndex] at hi
    | D _ _ => simp [weakExcIndex, excIndex] at hi
    | twistedD _ _ => simp [weakExcIndex, excIndex] at hi
    | E6 _ => simp [weakExcIndex, excIndex] at hi
    | E7 _ => simp [weakExcIndex, excIndex] at hi
    | E8 _ => simp [weakExcIndex, excIndex] at hi
    | F4 _ => simp [weakExcIndex, excIndex] at hi
    | G2 _ => simp [weakExcIndex, excIndex] at hi
    | twistedE6 _ => simp [weakExcIndex, excIndex] at hi
    | trialityD4 _ => simp [weakExcIndex, excIndex] at hi
    | suzuki _ => simp [weakExcIndex, excIndex] at hi
    | reeG2 _ => simp [weakExcIndex, excIndex] at hi
    | reeF4 _ => simp [weakExcIndex, excIndex] at hi
    | tits => simp [weakExcIndex, excIndex] at hi

end CFSG.LocalAnalysis.GLTheoremA.D4XN
