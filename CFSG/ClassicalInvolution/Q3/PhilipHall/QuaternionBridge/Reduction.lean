module

public import CFSG.ClassicalInvolution.Q3.TL3CentTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.HasLiftTwin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

theorem tightBelow_mono {m n : ℕ} (h : m ≤ n) (hn : TightBelow n) : TightBelow m :=
  fun Y _ _ hY R S t hd hc => hn Y (lt_of_lt_of_le hY h) R S t hd hc


theorem cit3Below_mono {m n : ℕ} (h : m ≤ n) (hn : CIT3Below n) : CIT3Below m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ

theorem tightCentTwinLift_of_q8TwinGood (h : Q8TwinGood) (n : ℕ) : TightCentTwinLift n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 hQ _ c hcZ hc1 hy _
  obtain ⟨y, hy⟩ := hy
  have B := q8Bridge_of_centTwin hd hc hE2 hQ hcZ hc1 hy
  have hle : Nat.card (Y ⧸ TA3.fstarCenter Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  exact good_of_twin hd B.central B.two B.not_mem
    (h _ B.simple B.nonab (cit3Below_mono hle hA) (tightBelow_mono hle hb) _ _ _ B.quot.datum
      B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty B.quot.twin)

theorem tightTwistAllTwin_of_q8TwinGood (h : Q8TwinGood) (n : ℕ) : TightTwistAllTwin n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 htw hall _ _
  have B := q8Bridge_of_twisted hd hc hE2 htw hall
  have hle : Nat.card (Y ⧸ genFittingFitting Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  exact good_of_twin hd B.central B.two B.not_mem
    (h _ B.simple B.nonab (cit3Below_mono hle hA) (tightBelow_mono hle hb) _ _ _ B.quot.datum
      B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty B.quot.twin)

theorem tightCentTwinLift_of_q8TwinLift (h : Q8TwinLift) (n : ℕ) : TightCentTwinLift n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 hQ _ c hcZ hc1 hy _
  obtain ⟨y, hy⟩ := hy
  have B := q8Bridge_of_centTwin hd hc hE2 hQ hcZ hc1 hy
  have hle : Nat.card (Y ⧸ TA3.fstarCenter Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  exact good_of_hasLift_twin hd B.central B.two B.not_mem
    (h _ B.simple B.nonab (cit3Below_mono hle hA) (tightBelow_mono hle hb) _ _ _ B.quot.datum
      B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty B.quot.twin)

theorem tightTwistAllTwin_of_q8TwinLift (h : Q8TwinLift) (n : ℕ) : TightTwistAllTwin n := by
  intro hA hb Y _ _ hn R S t hd hc hE2 htw hall _ _
  have B := q8Bridge_of_twisted hd hc hE2 htw hall
  have hle : Nat.card (Y ⧸ genFittingFitting Y) ≤ n := by rw [← hn]; exact B.quot.card_lt.le
  exact good_of_hasLift_twin hd B.central B.two B.not_mem
    (h _ B.simple B.nonab (cit3Below_mono hle hA) (tightBelow_mono hle hb) _ _ _ B.quot.datum
      B.quot.cls.1 B.quot.cls.2.1 B.quot.hyp B.aEmpty B.quot.twin)

theorem tightCentTwinLift_of_q8 (h7 : Q8Thm7) (hg : Q8SimpleGood) (n : ℕ) :
    TightCentTwinLift n :=
  tightCentTwinLift_of_q8TwinGood (q8TwinGood_of_parts h7 hg) n

theorem tightTwistAllTwin_of_q8 (h7 : Q8Thm7) (hg : Q8SimpleGood) (n : ℕ) :
    TightTwistAllTwin n :=
  tightTwistAllTwin_of_q8TwinGood (q8TwinGood_of_parts h7 hg) n

theorem tightCentTwinLift_of_q8_lift (h7 : Q8Thm7) (hl : Q8SimpleLift) (n : ℕ) :
    TightCentTwinLift n :=
  tightCentTwinLift_of_q8TwinLift (q8TwinLift_of_parts h7 hl) n

theorem tightTwistAllTwin_of_q8_lift (h7 : Q8Thm7) (hl : Q8SimpleLift) (n : ℕ) :
    TightTwistAllTwin n :=
  tightTwistAllTwin_of_q8TwinLift (q8TwinLift_of_parts h7 hl) n

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
