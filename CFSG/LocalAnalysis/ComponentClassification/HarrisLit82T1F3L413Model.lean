module

public import CFSG.LieType.HighestRoot.CentSpinBasic
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCenter
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.L413

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed
  CliffordAlgebra QuadraticMap Subgroup
open scoped MatrixGroups

theorem fin4_zero_ne_one : (0 : Fin 4) ≠ 1 := by decide
theorem fin4_one_ne_zero : (1 : Fin 4) ≠ 0 := by decide
theorem fin4_two_ne_three : (2 : Fin 4) ≠ 3 := by decide
theorem fin4_three_ne_two : (3 : Fin 4) ≠ 2 := by decide

variable {K : Type} [Field K]

theorem commute_ranges_of_unitriangular {S : Type*} [Group S] (ρ₁ ρ₂ : SL(2, K) →* S)
    (huu : ∀ a b, Commute (ρ₁ (upperSL2 a)) (ρ₂ (upperSL2 b)))
    (hul : ∀ a b, Commute (ρ₁ (upperSL2 a)) (ρ₂ (lowerSL2 b)))
    (hlu : ∀ a b, Commute (ρ₁ (lowerSL2 a)) (ρ₂ (upperSL2 b)))
    (hll : ∀ a b, Commute (ρ₁ (lowerSL2 a)) (ρ₂ (lowerSL2 b))) :
    ∀ x ∈ ρ₁.range, ∀ y ∈ ρ₂.range, x * y = y * x := by
  rintro _ ⟨M, rfl⟩ _ ⟨N, rfl⟩
  obtain ⟨a, b, c, d, rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 M
  obtain ⟨a', b', c', d', rfl⟩ := exists_eq_lowerSL2_mul_upperSL2_mul_lowerSL2_mul_upperSL2 N
  have key : ∀ g : S, Commute g (ρ₂ (lowerSL2 a')) → Commute g (ρ₂ (upperSL2 b')) →
      Commute g (ρ₂ (lowerSL2 c')) → Commute g (ρ₂ (upperSL2 d')) →
      Commute g (ρ₂ (lowerSL2 a') * ρ₂ (upperSL2 b') * ρ₂ (lowerSL2 c') * ρ₂ (upperSL2 d')) :=
    fun g h₁ h₂ h₃ h₄ => ((h₁.mul_right h₂).mul_right h₃).mul_right h₄
  simp only [map_mul]
  exact ((((key _ (hll a a') (hlu a b') (hll a c') (hlu a d')).mul_left
    (key _ (hul b a') (huu b b') (hul b c') (huu b d'))).mul_left
    (key _ (hll c a') (hlu c b') (hll c c') (hlu c d'))).mul_left
    (key _ (hul d a') (huu d b') (hul d c') (huu d d'))).eq

variable (K) in
noncomputable abbrev frame8 : HypFrame (quadPlus 4 K) 4 :=
  plusFrame 4 K (by norm_num)

variable (K) in
@[expose] noncomputable def rt : Fin 4 → (SL(2, K) →* spinGroup (quadPlus 4 K))
  | 0 => (frame8 K).longSL2 fin4_zero_ne_one true false
  | 1 => (frame8 K).longSL2 fin4_zero_ne_one true true
  | 2 => (frame8 K).longSL2 fin4_two_ne_three true false
  | 3 => (frame8 K).longSL2 fin4_two_ne_three true true

variable (K) in
@[expose] noncomputable def pl : Fin 4 → Frame (quadPlus 4 K)
  | 0 => (frame8 K).toFrame fin4_zero_ne_one true false
  | 1 => (frame8 K).toFrame fin4_zero_ne_one true true
  | 2 => (frame8 K).toFrame fin4_two_ne_three true false
  | 3 => (frame8 K).toFrame fin4_two_ne_three true true

variable (K) in
@[expose] noncomputable def inv4 (i : Fin 4) : spinGroup (quadPlus 4 K) := rt K i (-1)

theorem spinAction_rt (i : Fin 4) (M : SL(2, K)) :
    spinAction (quadPlus 4 K) (rt K i M) = (pl K i).La M := by
  fin_cases i
  · exact CFSG.LieType.HighestRoot.spinAction_longSL2 (frame8 K) _ _ _ M
  · exact CFSG.LieType.HighestRoot.spinAction_longSL2 (frame8 K) _ _ _ M
  · exact CFSG.LieType.HighestRoot.spinAction_longSL2 (frame8 K) _ _ _ M
  · exact CFSG.LieType.HighestRoot.spinAction_longSL2 (frame8 K) _ _ _ M

theorem rt_injective (i : Fin 4) : Function.Injective (rt K i) := by
  fin_cases i
  · exact CFSG.LieType.HighestRoot.longSL2_injective (frame8 K) _ _ _
  · exact CFSG.LieType.HighestRoot.longSL2_injective (frame8 K) _ _ _
  · exact CFSG.LieType.HighestRoot.longSL2_injective (frame8 K) _ _ _
  · exact CFSG.LieType.HighestRoot.longSL2_injective (frame8 K) _ _ _

theorem pl_zero_swap : (pl K 0).swap = pl K 1 :=
  (CFSG.LieType.HighestRoot.toFrame_not (frame8 K) fin4_zero_ne_one true false).symm

theorem pl_one_swap : (pl K 1).swap = pl K 0 :=
  (CFSG.LieType.HighestRoot.toFrame_not (frame8 K) fin4_zero_ne_one true true).symm

theorem pl_two_swap : (pl K 2).swap = pl K 3 :=
  (CFSG.LieType.HighestRoot.toFrame_not (frame8 K) fin4_two_ne_three true false).symm

theorem pl_three_swap : (pl K 3).swap = pl K 2 :=
  (CFSG.LieType.HighestRoot.toFrame_not (frame8 K) fin4_two_ne_three true true).symm

theorem commute_rt_zero_one : ∀ x ∈ (rt K 0).range, ∀ y ∈ (rt K 1).range, x * y = y * x := by
  refine commute_ranges_of_unitriangular _ _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_)
  · show Commute ((frame8 K).longSL2 fin4_zero_ne_one true false (upperSL2 a))
      ((frame8 K).longSL2 fin4_zero_ne_one true true (upperSL2 b))
    rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2]
    exact (frame8 K).commute_longRoot_longRoot_left fin4_zero_ne_one fin4_zero_ne_one true false
      true a b
  · show Commute ((frame8 K).longSL2 fin4_zero_ne_one true false (upperSL2 a))
      ((frame8 K).longSL2 fin4_zero_ne_one true true (lowerSL2 b))
    rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2]
    show Commute ((frame8 K).longRoot fin4_zero_ne_one true false (.ofAdd a))
      ((frame8 K).longRoot fin4_one_ne_zero false false (.ofAdd b))
    rw [(frame8 K).longRoot_swap fin4_one_ne_zero false false b]
    exact (frame8 K).commute_longRoot_longRoot_right fin4_zero_ne_one fin4_zero_ne_one true false
      false a (-b)
  · show Commute ((frame8 K).longSL2 fin4_zero_ne_one true false (lowerSL2 a))
      ((frame8 K).longSL2 fin4_zero_ne_one true true (upperSL2 b))
    rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_upperSL2]
    show Commute ((frame8 K).longRoot fin4_one_ne_zero true false (.ofAdd a))
      ((frame8 K).longRoot fin4_zero_ne_one true true (.ofAdd b))
    rw [(frame8 K).longRoot_swap fin4_zero_ne_one true true b]
    exact (frame8 K).commute_longRoot_longRoot_left fin4_one_ne_zero fin4_one_ne_zero true false
      true a (-b)
  · show Commute ((frame8 K).longSL2 fin4_zero_ne_one true false (lowerSL2 a))
      ((frame8 K).longSL2 fin4_zero_ne_one true true (lowerSL2 b))
    rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]
    exact (frame8 K).commute_longRoot_longRoot_right fin4_one_ne_zero fin4_one_ne_zero true false
      false a b

theorem commute_rt_two_three : ∀ x ∈ (rt K 2).range, ∀ y ∈ (rt K 3).range, x * y = y * x := by
  refine commute_ranges_of_unitriangular _ _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_)
  · show Commute ((frame8 K).longSL2 fin4_two_ne_three true false (upperSL2 a))
      ((frame8 K).longSL2 fin4_two_ne_three true true (upperSL2 b))
    rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2]
    exact (frame8 K).commute_longRoot_longRoot_left fin4_two_ne_three fin4_two_ne_three true false
      true a b
  · show Commute ((frame8 K).longSL2 fin4_two_ne_three true false (upperSL2 a))
      ((frame8 K).longSL2 fin4_two_ne_three true true (lowerSL2 b))
    rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2]
    show Commute ((frame8 K).longRoot fin4_two_ne_three true false (.ofAdd a))
      ((frame8 K).longRoot fin4_three_ne_two false false (.ofAdd b))
    rw [(frame8 K).longRoot_swap fin4_three_ne_two false false b]
    exact (frame8 K).commute_longRoot_longRoot_right fin4_two_ne_three fin4_two_ne_three true
      false false a (-b)
  · show Commute ((frame8 K).longSL2 fin4_two_ne_three true false (lowerSL2 a))
      ((frame8 K).longSL2 fin4_two_ne_three true true (upperSL2 b))
    rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_upperSL2]
    show Commute ((frame8 K).longRoot fin4_three_ne_two true false (.ofAdd a))
      ((frame8 K).longRoot fin4_two_ne_three true true (.ofAdd b))
    rw [(frame8 K).longRoot_swap fin4_two_ne_three true true b]
    exact (frame8 K).commute_longRoot_longRoot_left fin4_three_ne_two fin4_three_ne_two true
      false true a (-b)
  · show Commute ((frame8 K).longSL2 fin4_two_ne_three true false (lowerSL2 a))
      ((frame8 K).longSL2 fin4_two_ne_three true true (lowerSL2 b))
    rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]
    exact (frame8 K).commute_longRoot_longRoot_right fin4_three_ne_two fin4_three_ne_two true
      false false a b

theorem commute_longSL2_disjoint (s t u v : Bool) :
    ∀ x ∈ ((frame8 K).longSL2 fin4_zero_ne_one s t).range,
      ∀ y ∈ ((frame8 K).longSL2 fin4_two_ne_three u v).range, x * y = y * x := by
  refine commute_ranges_of_unitriangular _ _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    (fun a b => ?_)
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_upperSL2]
    exact (frame8 K).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2]
    exact (frame8 K).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_upperSL2]
    exact (frame8 K).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b
  · rw [HypFrame.longSL2_lowerSL2, HypFrame.longSL2_lowerSL2]
    exact (frame8 K).commute_longRoot_longRoot_of_disjoint (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) _ _ _ _ a b

theorem commute_rt {i k : Fin 4} (hik : i ≠ k) {x y : spinGroup (quadPlus 4 K)}
    (hx : x ∈ (rt K i).range) (hy : y ∈ (rt K k).range) : x * y = y * x := by
  fin_cases i <;> fin_cases k
  · exact absurd rfl hik
  · exact commute_rt_zero_one x hx y hy
  · exact commute_longSL2_disjoint true false true false x hx y hy
  · exact commute_longSL2_disjoint true false true true x hx y hy
  · exact (commute_rt_zero_one y hy x hx).symm
  · exact absurd rfl hik
  · exact commute_longSL2_disjoint true true true false x hx y hy
  · exact commute_longSL2_disjoint true true true true x hx y hy
  · exact (commute_longSL2_disjoint true false true false y hy x hx).symm
  · exact (commute_longSL2_disjoint true true true false y hy x hx).symm
  · exact absurd rfl hik
  · exact commute_rt_two_three x hx y hy
  · exact (commute_longSL2_disjoint true false true true y hy x hx).symm
  · exact (commute_longSL2_disjoint true true true true y hy x hx).symm
  · exact (commute_rt_two_three y hy x hx).symm
  · exact absurd rfl hik

theorem inv4_mem (i : Fin 4) : inv4 K i ∈ (rt K i).range := ⟨-1, rfl⟩

theorem inv4_mul_self (i : Fin 4) : inv4 K i * inv4 K i = 1 := by
  rw [inv4, ← map_mul, neg_one_mul, neg_neg, map_one]

theorem orderOf_inv4 (h2 : (2 : K) ≠ 0) (i : Fin 4) : orderOf (inv4 K i) = 2 := by
  rw [inv4, orderOf_injective _ (rt_injective i)]
  exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2

theorem commute_inv4 (i : Fin 4) {x : spinGroup (quadPlus 4 K)} (hx : x ∈ (rt K i).range) :
    x * inv4 K i = inv4 K i * x := by
  obtain ⟨M, rfl⟩ := hx
  rw [inv4, ← map_mul, ← map_mul, mul_neg_one, neg_one_mul]

theorem diagSL2_neg_one : diagSL2 (-1 : Kˣ) = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_diagSL2]

theorem inv4_one_eq_longTorus :
    inv4 K 1 = (frame8 K).longTorus fin4_zero_ne_one true true (-1) := by
  rw [HypFrame.longTorus_apply, diagSL2_neg_one]
  rfl

theorem inv4_three_eq_longTorus :
    inv4 K 3 = (frame8 K).longTorus fin4_two_ne_three true true (-1) := by
  rw [HypFrame.longTorus_apply, diagSL2_neg_one]
  rfl

theorem actsBy_inv4_one :
    ActsBy (frame8 K) (inv4 K 1) (fun m => if m = 0 ∨ m = 1 then -1 else 1) := by
  rw [inv4_one_eq_longTorus]
  exact actsBy_longTorus_neg_one (frame8 K) fin4_zero_ne_one

theorem actsBy_inv4_three :
    ActsBy (frame8 K) (inv4 K 3) (fun m => if m = 2 ∨ m = 3 then -1 else 1) := by
  rw [inv4_three_eq_longTorus]
  exact actsBy_longTorus_neg_one (frame8 K) fin4_two_ne_three

variable (K) in
@[expose] noncomputable def om : spinGroup (quadPlus 4 K) := inv4 K 1 * inv4 K 3

theorem actsBy_om : ActsBy (frame8 K) (om K) fun _ => -1 := by
  refine (actsBy_inv4_one.mul actsBy_inv4_three).congr (funext fun m => ?_)
  fin_cases m <;> simp

variable (K) in
noncomputable abbrev neg8 : spinGroup (quadPlus 4 K) := negOneS K (n := 4) (by norm_num)

theorem center_eq_scalarSpin :
    center (spinGroup (quadPlus 4 K)) = scalarSpin 4 K :=
  (spinToStatedProj_quadPlus (K := K) (by norm_num)).2.2.symm.trans
    (spinToStatedProj_quadPlus (K := K) (by norm_num)).2.1

theorem mem_center_iff_eq {c : spinGroup (quadPlus 4 K)} :
    c ∈ center (spinGroup (quadPlus 4 K)) ↔
      c = 1 ∨ c = neg8 K ∨ c = om K ∨ c = neg8 K * om K := by
  rw [center_eq_scalarSpin, ← SetLike.mem_coe,
    coe_scalarSpin_eq_of_actsBy_neg (n := 4) (by norm_num) actsBy_om]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem neg8_mem_center : neg8 K ∈ center (spinGroup (quadPlus 4 K)) :=
  mem_center_iff_eq.mpr (Or.inr (Or.inl rfl))

theorem om_mem_center : om K ∈ center (spinGroup (quadPlus 4 K)) :=
  mem_center_iff_eq.mpr (Or.inr (Or.inr (Or.inl rfl)))

theorem inv4_zero : inv4 K 0 = neg8 K * inv4 K 1 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul]
  exact CFSG.LieType.HighestRoot.coe_longSL2_not_neg_one (frame8 K) fin4_zero_ne_one true true

theorem inv4_two : inv4 K 2 = neg8 K * inv4 K 3 := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, spinGroup.coe_negOne, neg_one_mul]
  exact CFSG.LieType.HighestRoot.coe_longSL2_not_neg_one (frame8 K) fin4_two_ne_three true true

theorem exists_inv4_eq {c : spinGroup (quadPlus 4 K)}
    (hc : c ∈ center (spinGroup (quadPlus 4 K))) : ∃ i, inv4 K 1 * c = inv4 K i := by
  rcases mem_center_iff_eq.mp hc with rfl | rfl | rfl | rfl
  · exact ⟨1, mul_one _⟩
  · exact ⟨0, by rw [inv4_zero, (commute_negOneS (n := 4) (by norm_num) (inv4 K 1)).eq]⟩
  · exact ⟨3, by rw [om, ← mul_assoc, inv4_mul_self, one_mul]⟩
  · refine ⟨2, ?_⟩
    rw [inv4_two, om, ← mul_assoc, ← (commute_negOneS (n := 4) (by norm_num) (inv4 K 1)).eq,
      mul_assoc, ← mul_assoc (inv4 K 1), inv4_mul_self, one_mul]

theorem exists_mem_center_inv4_eq :
    ∀ i : Fin 4, ∃ c ∈ center (spinGroup (quadPlus 4 K)), inv4 K i = inv4 K 1 * c
  | 0 => ⟨neg8 K, neg8_mem_center, by
      rw [inv4_zero, (commute_negOneS (n := 4) (by norm_num) (inv4 K 1)).eq]⟩
  | 1 => ⟨1, one_mem _, (mul_one _).symm⟩
  | 2 => ⟨neg8 K * om K, mul_mem neg8_mem_center om_mem_center, by
      rw [inv4_two, om, ← mul_assoc, ← (commute_negOneS (n := 4) (by norm_num) (inv4 K 1)).eq,
        mul_assoc, ← mul_assoc (inv4 K 1), inv4_mul_self, one_mul]⟩
  | 3 => ⟨om K, om_mem_center, by rw [om, ← mul_assoc, inv4_mul_self, one_mul]⟩

theorem actsBy_neg8 : ActsBy (frame8 K) (neg8 K) fun _ => 1 :=
  actsBy_of_mem_ker (n := 4) (by norm_num) (negOne_mem_ker (n := 4) (by norm_num))

theorem spinAction_inv4_vec_zero : ∀ i : Fin 4,
    spinAction (quadPlus 4 K) (inv4 K i) ((frame8 K).vec 0 true) =
      (if i.val < 2 then -1 else 1 : K) • (frame8 K).vec 0 true
  | 0 => by
    rw [inv4_zero, (actsBy_neg8.mul actsBy_inv4_one) 0 true]
    simp
  | 1 => by
    rw [actsBy_inv4_one 0 true]
    simp
  | 2 => by
    rw [inv4_two, (actsBy_neg8.mul actsBy_inv4_three) 0 true]
    simp
  | 3 => by
    rw [actsBy_inv4_three 0 true]
    simp

theorem inv4_injective (h2 : (2 : K) ≠ 0) : Function.Injective (inv4 K) := by
  have hN : neg8 K ≠ 1 := negOneS_ne_one (n := 4) (by norm_num) h2
  have hv := CFSG.LieType.HighestRoot.hypFrame_vec_ne_zero (frame8 K) 0 true
  have hneg : ∀ i k : Fin 4, i.val < 2 → 2 ≤ k.val → inv4 K i ≠ inv4 K k := by
    intro i k hi hk h
    have e : spinAction (quadPlus 4 K) (inv4 K i) ((frame8 K).vec 0 true) =
        -(frame8 K).vec 0 true := by
      simpa [hi] using spinAction_inv4_vec_zero (K := K) i
    have e' : spinAction (quadPlus 4 K) (inv4 K k) ((frame8 K).vec 0 true) =
        (frame8 K).vec 0 true := by
      simpa [show ¬ k.val < 2 by omega] using spinAction_inv4_vec_zero (K := K) k
    rw [h, e'] at e
    have h0 : (2 : K) • (frame8 K).vec 0 true = 0 := by
      rw [two_smul]
      nth_rewrite 1 [e]
      rw [neg_add_cancel]
    exact hv ((smul_eq_zero.mp h0).resolve_left h2)
  have h01 : inv4 K 0 ≠ inv4 K 1 := fun h => hN (by
    rw [inv4_zero] at h
    simpa using h)
  have h23 : inv4 K 2 ≠ inv4 K 3 := fun h => hN (by
    rw [inv4_two] at h
    simpa using h)
  intro i k h
  fin_cases i <;> fin_cases k
  all_goals first
    | rfl
    | exact absurd h h01
    | exact absurd h.symm h01
    | exact absurd h h23
    | exact absurd h.symm h23
    | exact absurd h (hneg _ _ (by decide) (by decide))
    | exact absurd h.symm (hneg _ _ (by decide) (by decide))

theorem finrank_V8 : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem vec_mem_perp_toFrame {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (s t a : Bool) : (frame8 K).vec k a ∈ ((frame8 K).toFrame hij s t).perp := by
  rw [Frame.mem_perp_iff]
  show !![polar (quadPlus 4 K) ((frame8 K).vec k a) ((frame8 K).vec i (!s)),
      -polar (quadPlus 4 K) ((frame8 K).vec k a) ((frame8 K).vec j (!t));
      polar (quadPlus 4 K) ((frame8 K).vec k a) ((frame8 K).vec j t),
      polar (quadPlus 4 K) ((frame8 K).vec k a) ((frame8 K).vec i s)] = 0
  rw [(frame8 K).polar_vec_of_ne hki, (frame8 K).polar_vec_of_ne hki,
    (frame8 K).polar_vec_of_ne hkj, (frame8 K).polar_vec_of_ne hkj, neg_zero]
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem span_toFrame_le {k l : Fin 4} (hkl : k ≠ l) (u v : Bool)
    {P : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (h : ∀ a, (frame8 K).vec k a ∈ P ∧ (frame8 K).vec l a ∈ P) :
    ((frame8 K).toFrame hkl u v).span ≤ P := by
  rintro _ ⟨X, rfl⟩
  rw [Frame.incl_apply]
  exact add_mem (add_mem (add_mem (P.smul_mem _ (h u).1) (P.smul_mem _ (h (!u)).1))
    (P.smul_mem _ (h v).2)) (P.smul_mem _ (h (!v)).2)

theorem span_le_perp_two_zero (s t u v : Bool) :
    ((frame8 K).toFrame fin4_two_ne_three u v).span ≤
      ((frame8 K).toFrame fin4_zero_ne_one s t).perp :=
  span_toFrame_le _ u v fun a => ⟨vec_mem_perp_toFrame _ (by decide) (by decide) s t a,
    vec_mem_perp_toFrame _ (by decide) (by decide) s t a⟩

theorem span_le_perp_zero_two (s t u v : Bool) :
    ((frame8 K).toFrame fin4_zero_ne_one s t).span ≤
      ((frame8 K).toFrame fin4_two_ne_three u v).perp :=
  span_toFrame_le _ s t fun a => ⟨vec_mem_perp_toFrame _ (by decide) (by decide) u v a,
    vec_mem_perp_toFrame _ (by decide) (by decide) u v a⟩

theorem perp_le_span_of_span_le_perp {fr fr' : Frame (quadPlus 4 K)}
    (h : fr'.span ≤ fr.perp) : fr.perp ≤ fr'.span := by
  have h1 := finrank_perp_add_four fr
  rw [finrank_V8] at h1
  have h2 := Frame.finrank_span fr'
  exact (Submodule.eq_of_le_of_finrank_eq h (by omega)).symm.le

theorem perp_le_span_zero (s t : Bool) :
    ((frame8 K).toFrame fin4_zero_ne_one s t).perp ≤ (pl K 2).span :=
  perp_le_span_of_span_le_perp (span_le_perp_two_zero s t true false)

theorem perp_le_span_two (s t : Bool) :
    ((frame8 K).toFrame fin4_two_ne_three s t).perp ≤ (pl K 0).span :=
  perp_le_span_of_span_le_perp (span_le_perp_zero_two true false s t)

end CFSG.ComponentClassification.HarrisLit.T1.L413
