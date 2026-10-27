module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144ILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428NonInnHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428ExcHolds
public import CFSG.Timmesfeld.Orders.DistinctLinearD4

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.CatDistinct
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem not_d4_of_linUni_two (hc : Ctx) {S : Type} [Group S] [Finite S]
    (h : catalogIs S (onLie fun i => ∃ n q, q.p = 2 ∧ (i = .A n q ∨ i = .twistedA n q))) :
    ¬ catalogIs S isD4any ∧ ¬ catalogIs S (onLie fun | .trialityD4 _ => True | _ => False) := by
  obtain ⟨d, hv, hd, ⟨eS⟩⟩ := K144I.exists_lieIndex_of_catalogIs_onLie h
  obtain ⟨n, q, hq2, hcase⟩ := hd
  have hchev : IsChevSimple 2 S := by
    refine Or.inl ⟨TauCeti.CFSGIndex.lie ⟨d, hv⟩, ?_, ⟨eS⟩⟩
    rcases hcase with rfl | rfl
    · simpa [onLie, TauCeti.LieTypeIndex.characteristic_A] using hq2
    · simpa [onLie, TauCeti.LieTypeIndex.characteristic_twistedA] using hq2
  have hqexp : 1 ≤ q.exponent := q.exponent_pos
  constructor
  · rintro hD4
    obtain ⟨iD, hiD, ⟨eD⟩⟩ := hD4
    obtain ⟨qD, hvD, hqD2, rfl⟩ := T1428NonInn.t1428NonInn_exists_D4 hiD
    have hqDexp : 1 ≤ qD.exponent := qD.exponent_pos
    have hcardD : Nat.card S = ordD 4 (2 ^ qD.exponent) := by
      rw [hc.bridge ⟨.D 4 qD, hvD⟩ S ⟨eD⟩]
      simp [lieOrderFormula, TauCeti.PrimePower.card_def, hqD2]
      rfl
    rcases hcase with rfl | rfl
    · have hcardA : Nat.card S = ordA n (2 ^ q.exponent) := by
        rw [hc.bridge ⟨.A n q, hv⟩ S ⟨eS⟩]
        simp [lieOrderFormula, TauCeti.PrimePower.card_def, hq2]
        rfl
      have hn : 1 ≤ n := by
        have := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at this
        exact this.1.1
      exact ordA_ne_ordD_four hn hqexp hqDexp (hcardA.symm.trans hcardD)
    · have hcardU : Nat.card S = ordTwistedA n (2 ^ q.exponent) := by
        rw [hc.bridge ⟨.twistedA n q, hv⟩ S ⟨eS⟩]
        simp only [lieOrderFormula, TauCeti.PrimePower.card_def, hq2]
        rw [← T1428.ordTwistedA_eq_orderTwistedA]
        exact Nat.one_le_two_pow
      have hn : 2 ≤ n := by
        have := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at this
        exact this.1.1
      exact (ordD_ne_ordTwistedA (n := 4) (f := qD.exponent) (u := n) (g := q.exponent)
        (by norm_num) hqDexp hn hqexp) (hcardD.symm.trans hcardU)
  · intro hT
    obtain ⟨dT, hvT, hdT, ⟨eT⟩⟩ := K144I.exists_lieIndex_of_catalogIs_onLie hT
    obtain ⟨qT, rfl⟩ : ∃ qT, dT = .trialityD4 qT := by
      cases dT with
      | trialityD4 qT => exact ⟨qT, rfl⟩
      | _ => simp [onLie] at hdT
    have hqT2 : qT.p = 2 := CatDistinct.td4_chev2_even hc qT hvT eT hchev
    have hqTexp : 1 ≤ qT.exponent := qT.exponent_pos
    have hcardT : Nat.card S = ordTrialityD4 (2 ^ qT.exponent) := by
      rw [hc.bridge ⟨.trialityD4 qT, hvT⟩ S ⟨eT⟩]
      simp [lieOrderFormula, TauCeti.PrimePower.card_def, hqT2]
      rfl
    rcases hcase with rfl | rfl
    · have hcardA : Nat.card S = ordA n (2 ^ q.exponent) := by
        rw [hc.bridge ⟨.A n q, hv⟩ S ⟨eS⟩]
        simp [lieOrderFormula, TauCeti.PrimePower.card_def, hq2]
        rfl
      have hn : 1 ≤ n := by
        have := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at this
        exact this.1.1
      exact ordA_ne_ordTrialityD4 hn hqexp hqTexp (hcardA.symm.trans hcardT)
    · have hcardU : Nat.card S = ordTwistedA n (2 ^ q.exponent) := by
        rw [hc.bridge ⟨.twistedA n q, hv⟩ S ⟨eS⟩]
        simp only [lieOrderFormula, TauCeti.PrimePower.card_def, hq2]
        rw [← T1428.ordTwistedA_eq_orderTwistedA]
        exact Nat.one_le_two_pow
      have hn : 2 ≤ n := by
        have := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        rw [TauCeti.LieTypeIndex.inStandardRange_iff] at this
        exact this.1.1
      exact (ordTrialityD4_ne_ordTwistedA (f := qT.exponent) (u := n) (g := q.exponent)
        hqTexp hn hqexp) (hcardT.symm.trans hcardU)

end CFSG.LocalAnalysis.GLTheoremA

end
