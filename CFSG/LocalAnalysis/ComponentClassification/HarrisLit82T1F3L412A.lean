module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Universal.Spin.Chevalley.Odd
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Frame

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem spinAction_comm_apply {x g : spinGroup Q} (h : x * g = g * x) (v : V) :
    spinAction Q x (spinAction Q g v) = spinAction Q g (spinAction Q x v) := by
  have h' := congrArg (fun y => spinAction Q y v) h
  simpa only [map_mul, LinearEquiv.mul_apply] using h'

variable {m : ℕ}

theorem exists_spinAction_vec_eq_smul (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)
    {x : spinGroup Q}
    (ha : x * F.longRoot hij true true (.ofAdd 1) = F.longRoot hij true true (.ofAdd 1) * x)
    (hb : x * F.longRoot hij true false (.ofAdd 1) = F.longRoot hij true false (.ofAdd 1) * x) :
    ∃ c : K, spinAction Q x (F.vec i true) = c • F.vec i true := by
  have e1 : spinAction Q (F.longRoot hij true true (.ofAdd 1)) (F.vec j false) =
      F.vec j false + (1 : K) • F.vec i true :=
    F.spinAction_longRoot_vec_not_right hij true true 1
  have e2 : spinAction Q (F.longRoot hij true false (.ofAdd 1)) (F.vec j true) =
      F.vec j true + (1 : K) • F.vec i true :=
    F.spinAction_longRoot_vec_not_right hij true false 1
  have h1 := spinAction_comm_apply ha (F.vec j false)
  rw [e1, one_smul, map_add, HypFrame.spinAction_longRoot, one_mul, one_mul] at h1
  have h2 := spinAction_comm_apply hb (F.vec j true)
  rw [e2, one_smul, map_add, HypFrame.spinAction_longRoot, one_mul, one_mul] at h2
  set A := spinAction Q x with hA
  have ea : A (F.vec i true) = polar Q (A (F.vec j false)) (F.vec j true) • F.vec i true -
      polar Q (A (F.vec j false)) (F.vec i true) • F.vec j true :=
    add_left_cancel (h1.trans (add_sub_assoc _ _ _))
  have eb : A (F.vec i true) = polar Q (A (F.vec j true)) (F.vec j false) • F.vec i true -
      polar Q (A (F.vec j true)) (F.vec i true) • F.vec j false :=
    add_left_cancel (h2.trans (add_sub_assoc _ _ _))
  have hp1 : polar Q (F.vec j true) (F.vec j false) = 1 := F.polar_vec_not j true
  have hp0 : polar Q (F.vec i true) (F.vec j false) = 0 := F.polar_vec_of_ne hij true false
  have hp2 : polar Q (F.vec j false) (F.vec j false) = 0 := F.polar_vec_self j false
  have pa := congrArg (fun w => polar Q w (F.vec j false)) ea
  have pb := congrArg (fun w => polar Q w (F.vec j false)) eb
  simp only [polar_sub_left, polar_smul_left, smul_eq_mul, hp1, hp0, hp2, mul_zero, mul_one,
    sub_zero, zero_sub] at pa pb
  have hq : polar Q (A (F.vec j false)) (F.vec i true) = 0 := neg_eq_zero.mp (pa.symm.trans pb)
  exact ⟨_, by rw [ea, hq, zero_smul, sub_zero]⟩

theorem spinAction_vec_eq_smul_of_commute (F : HypFrame Q m) {i j : Fin m} (hij : i ≠ j)
    {x : spinGroup Q} {c : K} (hi : spinAction Q x (F.vec i true) = c • F.vec i true)
    (hc : x * F.longRoot hij.symm false false (.ofAdd 1) =
      F.longRoot hij.symm false false (.ofAdd 1) * x)
    (hd : x * F.longRoot hij.symm true false (.ofAdd 1) =
      F.longRoot hij.symm true false (.ofAdd 1) * x) :
    spinAction Q x (F.vec j true) = c • F.vec j true ∧
      spinAction Q x (F.vec i false) = c • F.vec i false ∧
      spinAction Q x (F.vec j false) = c • F.vec j false := by
  have ed : spinAction Q (F.longRoot hij.symm true false (.ofAdd 1)) (F.vec i true) =
      F.vec i true + (1 : K) • F.vec j true :=
    F.spinAction_longRoot_vec_not_right hij.symm true false 1
  have ec1 : spinAction Q (F.longRoot hij.symm false false (.ofAdd 1)) (F.vec i true) =
      F.vec i true + (1 : K) • F.vec j false :=
    F.spinAction_longRoot_vec_not_right hij.symm false false 1
  have ec2 : spinAction Q (F.longRoot hij.symm false false (.ofAdd 1)) (F.vec j true) =
      F.vec j true - (1 : K) • F.vec i false :=
    F.spinAction_longRoot_vec_not_left hij.symm false false 1
  set A := spinAction Q x with hA
  have hj : A (F.vec j true) = c • F.vec j true := by
    have h := spinAction_comm_apply hd (F.vec i true)
    rw [ed, one_smul, map_add, hi, map_smul, ed, one_smul, smul_add] at h
    exact add_left_cancel h
  have hfj : A (F.vec j false) = c • F.vec j false := by
    have h := spinAction_comm_apply hc (F.vec i true)
    rw [ec1, one_smul, map_add, hi, map_smul, ec1, one_smul, smul_add] at h
    exact add_left_cancel h
  have hfi : A (F.vec i false) = c • F.vec i false := by
    have h := spinAction_comm_apply hc (F.vec j true)
    rw [ec2, one_smul, map_sub, hj, map_smul, ec2, one_smul, smul_sub] at h
    exact sub_right_inj.mp h
  exact ⟨hj, hfi, hfj⟩

theorem exists_spinAction_vec_eq_smul_of_commute_shortRoot (F : OddFrame Q m) (h2 : (2 : K) ≠ 0)
    (r : Fin m) (b : Bool) {x : spinGroup Q}
    (hx : x * F.shortRoot r b (.ofAdd 1) = F.shortRoot r b (.ofAdd 1) * x) :
    ∃ c : K, spinAction Q x (F.vec r b) = c • F.vec r b := by
  have hz := spinAction_comm_apply hx F.z
  rw [OddFrame.spinAction_shortRoot_z, map_sub, map_smul, OddFrame.spinAction_shortRoot] at hz
  have hE := spinAction_comm_apply hx (F.vec r b)
  rw [OddFrame.spinAction_shortRoot_vec_self, OddFrame.spinAction_shortRoot] at hE
  set A := spinAction Q x with hA
  set E := F.vec r b with hEdef
  have hEF : polar Q E (F.vec r (!b)) = 1 := F.polar_vec_not r b
  have hzF : polar Q F.z (F.vec r (!b)) = 0 := F.polar_z_vec r (!b)
  have hEz : polar Q E F.z = 0 := F.polar_vec_z r b
  have hzz : polar Q F.z F.z = 2 := F.polar_z_self
  have hE0 : (0 : V) = (1 * polar Q (A E) E) • F.z -
      (1 * polar Q (A E) F.z + 1 ^ 2 * polar Q (A E) E) • E :=
    add_left_cancel ((add_zero _).trans (hE.trans (add_sub_assoc _ _ _)))
  have p1 := congrArg (fun w => polar Q w (F.vec r (!b))) hE0
  have p2 := congrArg (fun w => polar Q w F.z) hE0
  simp only [polar_zero_left, polar_sub_left, polar_smul_left, smul_eq_mul, hEF, hzF, hEz, hzz,
    one_mul, one_pow, mul_zero, mul_one, zero_sub, sub_zero] at p1 p2
  have hAEE : polar Q (A E) E = 0 := by
    rcases mul_eq_zero.mp p2.symm with h | h
    · exact h
    · exact absurd h h2
  have hAEz : polar Q (A E) F.z = 0 := by linear_combination p1 - hAEE
  have p3 := congrArg (fun w => polar Q w F.z) hz
  simp only [polar_sub_left, polar_add_left, polar_smul_left, smul_eq_mul, hAEz, hEz, hzz,
    one_mul, one_pow, mul_zero, mul_one, sub_zero] at p3
  have hpz : polar Q (A F.z) E = 0 := by
    have : (2 : K) * polar Q (A F.z) E = 0 := by linear_combination -p3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact h
  simp only [hpz, mul_zero, zero_smul, add_zero, one_mul, one_pow, mul_one] at hz
  have h2E : (2 : K) • A E = polar Q (A F.z) F.z • E := sub_right_injective hz
  refine ⟨2⁻¹ * polar Q (A F.z) F.z, ?_⟩
  rw [mul_smul, ← h2E, smul_smul, inv_mul_cancel₀ h2, one_smul]

end Frame

section QuadOdd

variable {K : Type} [Field K] {n : ℕ}

theorem eq_of_polar_quadOdd (h2 : (2 : K) ≠ 0) {w w' : Fin n ⊕ Fin n ⊕ Unit → K}
    (hvec : ∀ k s, polar (quadOdd n K) w ((oddFrame n K).vec k s) =
      polar (quadOdd n K) w' ((oddFrame n K).vec k s))
    (hz : polar (quadOdd n K) w (oddFrame n K).z = polar (quadOdd n K) w' (oddFrame n K).z) :
    w = w' := by
  funext idx
  rcases idx with k | k | u
  · have h := hvec k false
    rwa [oddFrame_vec, oddVec_false, polar_quadOdd_single_inr_inl,
      polar_quadOdd_single_inr_inl] at h
  · have h := hvec k true
    rwa [oddFrame_vec, oddVec_true, polar_quadOdd_single_inl, polar_quadOdd_single_inl] at h
  · cases u
    rw [oddFrame_z, oddZ, polar_quadOdd_single_inr_inr, polar_quadOdd_single_inr_inr] at hz
    exact mul_left_cancel₀ h2 hz

theorem mul_self_eq_one_of_card_three [Finite K] (hK : Nat.card K = 3) {a : K} (ha : a ≠ 0) :
    a * a = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rw [Fintype.card_eq_nat_card, hK] at h
  rw [← pow_two]
  simpa using h

theorem hyperbolic_sq_three [Finite K] (hK : Nat.card K = 3) {a b c d : K} (hab : a * b = 0)
    (hcd : c * d = 0) (h : a * d + b * c = 1) :
    a * a + b * c = 1 ∧ a * b + b * d = 0 ∧ c * a + d * c = 0 ∧ c * b + d * d = 1 := by
  by_cases hb : b = 0
  · have had : a * d = 1 := by linear_combination h - c * hb
    have ha2 := mul_self_eq_one_of_card_three hK (left_ne_zero_of_mul_eq_one had)
    have hd2 := mul_self_eq_one_of_card_three hK (right_ne_zero_of_mul_eq_one had)
    have hc : c = 0 := (mul_eq_zero.mp hcd).resolve_right (right_ne_zero_of_mul_eq_one had)
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination ha2 + c * hb
    · linear_combination (a + d) * hb
    · linear_combination (a + d) * hc
    · linear_combination hd2 + c * hb
  · have ha : a = 0 := (mul_eq_zero.mp hab).resolve_right hb
    have hbc : b * c = 1 := by linear_combination h - d * ha
    have hd : d = 0 := (mul_eq_zero.mp hcd).resolve_left (right_ne_zero_of_mul_eq_one hbc)
    refine ⟨?_, ?_, ?_, ?_⟩
    · linear_combination h + (a - d) * ha
    · linear_combination b * ha + b * hd
    · linear_combination c * ha + c * hd
    · linear_combination h + d * hd - d * ha

end QuadOdd

end CFSG.ComponentClassification.HarrisLit.T1
