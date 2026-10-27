module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YDArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YCRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.D4T
open CFSG.LocalAnalysis.GLTheoremA

theorem not_weakExc_of_isD4big (hb : CatDistinct.OrderBridge)
    (hM22 : Nat.card (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group = 443520)
    {S : Type} [Group S] [Finite S] (h4 : catalogIs S isD4any) (hn : ¬ catalogIs S S9.isD4two) :
    ¬ catalogIs S weakExcIndex := by
  intro hw
  obtain ⟨i, hi, ⟨e⟩⟩ := h4
  have hi2 : ¬ S9.isD4two i := fun h => hn ⟨i, h, ⟨e⟩⟩
  obtain ⟨q, hv, hp2, hex, rfl⟩ := exists_D4_of_isD4any_not_two hi hi2
  have hN : Nat.card S = orderD 4 q.card := hb ⟨.D 4 q, hv⟩ S ⟨e⟩
  have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp2]
  rw [hcard] at hN
  have h27 : 27 ∣ Nat.card S := hN ▸ dvd_orderD q.exponent (by omega)
  obtain ⟨j, hj, ⟨e'⟩⟩ := hw
  cases j with
  | cyclic p hp => simp [weakExcIndex, excIndex] at hj
  | alternating n hn5 =>
    have h6 : n = 6 ∨ n = 7 := by simpa [weakExcIndex, excIndex] using hj
    have hc := CatDistinct.card_alternating_of_iso hn5 e'
    rw [hc] at h27
    rcases h6 with rfl | rfl <;> norm_num [Nat.factorial] at h27
  | sporadic s =>
    have hs : s = TauCeti.SporadicName.M22 := by simpa [weakExcIndex, excIndex] using hj
    subst hs
    have hc : Nat.card S = 443520 := by rw [Nat.card_congr e'.toEquiv]; exact hM22
    rw [hc] at h27
    norm_num at h27
  | lie d =>
    obtain ⟨d1, hv'⟩ := d
    have hord : Nat.card S = CFSG.HardMathSupport.Solomon.Coordinator.I1420.lieOrderFormula d1 :=
      hb ⟨d1, hv'⟩ S ⟨e'⟩
    cases d1 with
    | A r q' =>
      rcases r with _ | _ | _ | r
      · simp [weakExcIndex, excIndex] at hj
      · obtain ⟨hp2', hodd, -⟩ : q'.p = 2 ∧ Odd q'.exponent ∧ 1 < q'.exponent := by
          simpa [weakExcIndex, excIndex] using hj
        have hc' : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hp2']
        have hord' : Nat.card S = orderA 1 q'.card := hord
        refine orderA_one_ne_orderD (k := q'.exponent) (e := q.exponent) hodd (by omega) ?_
        rw [← hc', ← hord', hN]
      · have h9 : q'.card % 9 = 4 ∨ q'.card % 9 = 7 := by
          simpa [weakExcIndex, excIndex] using hj
        have hord' : Nat.card S = orderA 2 q'.card := hord
        apply not_dvd27_orderA2 q'.card h9
        rw [← hord']
        exact h27
      · simp [weakExcIndex, excIndex] at hj
    | twistedA r q' =>
      rcases r with _ | _ | r
      · simp [weakExcIndex, excIndex] at hj
      · simp [weakExcIndex, excIndex] at hj
      · rcases r with _ | r
        · have h9 : q'.card % 9 = 2 ∨ q'.card % 9 = 5 := by
            simpa [weakExcIndex, excIndex] using hj
          have hord' : Nat.card S = orderTwistedA 2 q'.card := hord
          apply not_dvd27_orderTA2 q'.card h9
          rw [← hord']
          exact h27
        · simp [weakExcIndex, excIndex] at hj
    | B _ _ => simp [weakExcIndex, excIndex] at hj
    | C _ _ => simp [weakExcIndex, excIndex] at hj
    | D _ _ => simp [weakExcIndex, excIndex] at hj
    | twistedD _ _ => simp [weakExcIndex, excIndex] at hj
    | E6 _ => simp [weakExcIndex, excIndex] at hj
    | E7 _ => simp [weakExcIndex, excIndex] at hj
    | E8 _ => simp [weakExcIndex, excIndex] at hj
    | F4 _ => simp [weakExcIndex, excIndex] at hj
    | G2 _ => simp [weakExcIndex, excIndex] at hj
    | twistedE6 _ => simp [weakExcIndex, excIndex] at hj
    | trialityD4 _ => simp [weakExcIndex, excIndex] at hj
    | suzuki _ => simp [weakExcIndex, excIndex] at hj
    | reeG2 _ => simp [weakExcIndex, excIndex] at hj
    | reeF4 _ => simp [weakExcIndex, excIndex] at hj
    | tits => simp [weakExcIndex, excIndex] at hj

end CFSG.LocalAnalysis.GLTheoremA.D4Y
