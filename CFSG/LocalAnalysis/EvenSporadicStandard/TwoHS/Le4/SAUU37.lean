module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUCheck

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

structure U37Facts : Prop where
  three : ∀ B ∈ q0List, B ^ 3 = 1 → B ≠ 1 →
    ∃ c : V4, B *ᵥ c = c ∧ c + c ≠ 0 ∧ c + c ≠ tVec
  seven : ∀ B ∈ q0List, B ^ 7 = 1 → B ≠ 1 →
    ∀ c : V4, c + c ∈ fVecs → B *ᵥ c = c → c = 0 ∨ c = tVec
  ex7 : ∃ B ∈ q0List, B ^ 7 = 1 ∧ B ≠ 1

@[expose] def rpow3 (a : R4) : R4 := rmul a (rmul a a)

@[expose] def rpow7 (a : R4) : R4 := rmul (rpow3 a) (rmul (rpow3 a) a)

theorem ofR4_rpow3 (a : R4) : ofR4 (rpow3 a) = ofR4 a ^ 3 := by
  simp only [rpow3, ofR4_rmul]
  rw [pow_succ, pow_two, mul_assoc]

theorem ofR4_rpow7 (a : R4) : ofR4 (rpow7 a) = ofR4 a ^ 7 := by
  simp only [rpow7, ofR4_rpow3, ofR4_rmul]
  have h : (7 : ℕ) = 3 + 3 + 1 := by decide
  rw [h, pow_add, pow_add, pow_one, mul_assoc]

@[expose] def u3Check : Bool :=
  q0R.all fun b => !(rpow3 b == R4.one) || b == R4.one ||
    allVR.any fun c => rmv b c == c && !(radd c c == zeroRV) && !(radd c c == tRV)

@[expose] def u7Check : Bool :=
  q0R.all fun b => !(rpow7 b == R4.one) || b == R4.one ||
    allVR.all fun c => !(inFR (radd c c)) || !(rmv b c == c) || c == zeroRV || c == tRV

@[expose] def u7ex : Bool := q0R.any fun b => rpow7 b == R4.one && !(b == R4.one)

theorem wf_rpow3 (a : R4) : (rpow3 a).wf := wf_rmul _ _

theorem wf_rpow7 (a : R4) : (rpow7 a).wf := wf_rmul _ _

theorem ofRV_tRV : ofRV tRV = tVec := by
  unfold tRV
  rw [ofRV_toRV]

theorem rpow3_eq_one {B : M4} (h : B ^ 3 = 1) : rpow3 (toR4 B) = R4.one := by
  apply ofR4_inj (wf_rpow3 _) wf_one
  rw [ofR4_rpow3, ofR4_toR4, ofR4_one]
  exact h

theorem rpow7_eq_one {B : M4} (h : B ^ 7 = 1) : rpow7 (toR4 B) = R4.one := by
  apply ofR4_inj (wf_rpow7 _) wf_one
  rw [ofR4_rpow7, ofR4_toR4, ofR4_one]
  exact h

theorem toR4_ne_one {B : M4} (h : B ≠ 1) : (toR4 B == R4.one) = false := by
  apply beq_eq_false_iff_ne.2
  intro h'
  apply h
  have := congrArg ofR4 h'
  rwa [ofR4_toR4, ofR4_one] at this

theorem u37Facts_of_check (h3 : u3Check = true) (h7 : u7Check = true) (hex : u7ex = true) :
    U37Facts where
  three := by
    intro B hB hB3 hB1
    have hb : toR4 B ∈ q0R := List.mem_map.2 ⟨B, hB, rfl⟩
    have h1 := (List.all_eq_true.1 h3) _ hb
    rw [rpow3_eq_one hB3, toR4_ne_one hB1] at h1
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_false,
      List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h1
    obtain ⟨c, hc, ⟨hfix, hz⟩, ht⟩ := h1
    refine ⟨ofRV c, ?_, ?_, ?_⟩
    · have := congrArg ofRV (beq_iff_eq.1 hfix)
      rw [ofRV_rmv, ofR4_toR4] at this
      exact this
    · intro h0
      have h1 : ofRV (radd c c) = ofRV zeroRV := by
        rw [ofRV_radd, ofRV_zeroRV]
        exact h0
      have := ofRV_inj (wf_radd c c) (by decide) h1
      rw [this] at hz
      simp at hz
    · intro h0
      have h1 : ofRV (radd c c) = ofRV tRV := by
        rw [ofRV_radd, ofRV_tRV]
        exact h0
      have := ofRV_inj (wf_radd c c) (by unfold tRV; exact wf_toRV _) h1
      rw [this] at ht
      simp at ht
  seven := by
    intro B hB hB7 hB1 c hcF hfix
    have hb : toR4 B ∈ q0R := List.mem_map.2 ⟨B, hB, rfl⟩
    have h1 := (List.all_eq_true.1 h7) _ hb
    rw [rpow7_eq_one hB7, toR4_ne_one hB1] at h1
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_false,
      List.all_eq_true] at h1
    have h2 := h1 (toRV c) (mem_allVR c)
    have hcc : inFR (radd (toRV c) (toRV c)) = true := by
      rw [inFR_iff (wf_radd _ _), ofRV_radd, ofRV_toRV]
      exact hcF
    have hfx : rmv (toR4 B) (toRV c) = toRV c := by
      apply ofRV_inj (wf_rmv _ _) (wf_toRV c)
      rw [ofRV_rmv, ofR4_toR4, ofRV_toRV]
      exact hfix
    rw [hcc, hfx] at h2
    simp only [Bool.not_true, Bool.false_or, beq_self_eq_true, Bool.not_true, Bool.or_eq_true,
      beq_iff_eq] at h2
    rcases h2 with h2 | h2
    · left
      have := congrArg ofRV h2
      rw [ofRV_toRV, ofRV_zeroRV] at this
      exact this
    · right
      have := congrArg ofRV h2
      rw [ofRV_toRV, ofRV_tRV] at this
      exact this
  ex7 := by
    obtain ⟨b, hb, hb2⟩ := List.any_eq_true.1 hex
    obtain ⟨B, hB, rfl⟩ := List.mem_map.1 hb
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hb2
    obtain ⟨hp, hne⟩ := hb2
    refine ⟨B, hB, ?_, ?_⟩
    · have := congrArg ofR4 hp
      rwa [ofR4_rpow7, ofR4_toR4, ofR4_one] at this
    · intro h
      rw [h] at hne
      have : toR4 (1 : M4) = R4.one := by
        apply ofR4_inj (wf_toR4 _) wf_one
        rw [ofR4_toR4, ofR4_one]
      simp [this] at hne

end CFSG.EvenSporadicStandard.TwoHS
