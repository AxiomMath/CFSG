module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem card_dvd_of_u42Pumpup {S : Type} [Group S] [Finite S] {α : MulAut S}
    (h : U42Pumpup S α) : 25920 ∣ Nat.card S := by
  obtain ⟨-, -, J, -, hT⟩ := h
  have h1 : Nat.card (PSimple 3 J) = 25920 := I1431Z.card_eq_of_u4two hT
  have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
  have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
  have h4 : Nat.card J ∣ Nat.card S := Subgroup.card_subgroup_dvd_card J
  rw [← h1]
  exact h2.trans (h3.trans h4)

section Orders

theorem u42FieldTwoAt_nonClassical_of
    (hF4 : U42FieldTwoAt fun d => ∃ q, d = .F4 q)
    (hTw : U42FieldTwoAt fun d => ∃ q, d = .twistedE6 q)
    (hE : U42FieldTwoAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q) :
    U42FieldTwoAt U42NonClassical := by
  intro Y _ _ hY hcore hRk ⟨d, hv⟩ hd hc hf he α hα hP
  have hcard := CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨d, hv⟩
    (Y ⧸ Subgroup.center Y) he
  have hdvd := card_dvd_of_u42Pumpup hP
  have hs : d.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff d).1 hv).1
  cases d with
  | A n q => exact (hd trivial).elim
  | twistedA n q => exact (hd trivial).elim
  | B n q => exact (hd trivial).elim
  | C n q => exact (hd trivial).elim
  | D n q => exact (hd trivial).elim
  | twistedD n q => exact (hd trivial).elim
  | E6 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inl rfl⟩ hc hf he α hα hP
  | E7 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inr (Or.inl rfl)⟩ hc hf he α hα hP
  | E8 q => exact hE Y hY hcore hRk ⟨_, hv⟩ ⟨q, Or.inr (Or.inr rfl)⟩ hc hf he α hα hP
  | F4 q => exact hF4 Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he α hα hP
  | twistedE6 q => exact hTw Y hY hcore hRk ⟨_, hv⟩ ⟨q, rfl⟩ hc hf he α hα hP
  | G2 q =>
    simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    omega
  | trialityD4 q =>
    simp only [KD264Lie.fieldSize] at hf
    rw [hcard] at hdvd
    simp only [lieOrderFormula, CFSG.Open.orderTrialityD4, hf] at hdvd
    norm_num at hdvd
  | suzuki m =>
    simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | reeG2 m =>
    rw [TauCeti.LieTypeIndex.characteristic_reeG2] at hc
    omega
  | reeF4 m =>
    simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
    simp only [KD264Lie.fieldSize] at hf
    have : 2 ^ 3 ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  | tits =>
    rw [hcard] at hdvd
    simp only [lieOrderFormula, CFSG.Open.orderTits] at hdvd
    norm_num at hdvd

end Orders

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
