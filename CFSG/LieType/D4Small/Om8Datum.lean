module

public import CFSG.LieType.D4Small.Datum
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGTorus
public import CFSG.ClassicalGroups.Orthogonal.RootGroupGLEichler
public import CFSG.LieType.Steinberg.Classical.SpinFrame.Commutator
import Mathlib.Tactic.Ring
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard

public section

namespace CFSG.LieType.D4Small

open CFSG.StandardType CFSG.StandardType.Triality CFSG.StandardType.L613KG
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame QuadraticMap
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

theorem isLong_of_isD4Root {α : Fin 4 → ℤ} (h : IsD4Root α) : IsLong α := by
  obtain ⟨i, j, hij, hi, hj, hα⟩ := isD4Root_iff.1 h
  obtain ⟨s, hs⟩ := exists_boolSign_eq hi
  obtain ⟨t, ht⟩ := exists_boolSign_eq hj
  exact ⟨i, j, hij, s, t, by rw [hα, ← hs, ← ht]⟩

theorem isD4Root_of_isLong {e : Fin 4 → ℤ} (h : IsLong e) : IsD4Root e := by
  obtain ⟨i, j, hij, s, t, rfl⟩ := h
  exact isD4Root_single_add_single hij (boolSign_eq_one_or_eq_neg_one s)
    (boolSign_eq_one_or_eq_neg_one t)

theorem toStdD_fromStd_of_isD4Root {α : Fin 4 → ℤ} (h : IsD4Root α) :
    toStdD 4 (fromStd α) = α := by
  obtain ⟨i, j, hij, hi, hj, hα⟩ := isD4Root_iff.1 h
  obtain ⟨s, hs⟩ := exists_boolSign_eq hi
  obtain ⟨t, ht⟩ := exists_boolSign_eq hj
  rw [show α = lv i j s t by rw [hα, ← hs, ← ht]]
  exact (roots_check i j s t hij).1

theorem mem_rootsD4_fromStd_of_isD4Root {α : Fin 4 → ℤ} (h : IsD4Root α) :
    fromStd α ∈ rootsD4 :=
  mem_rootsD4_iff.2 (by rw [toStdD_fromStd_of_isD4Root h]; exact isLong_of_isD4Root h)

theorem exists_lv_of_isD4Root {α : Fin 4 → ℤ} (h : IsD4Root α) :
    ∃ (i j : Fin 4) (s t : Bool), i ≠ j ∧ α = lv i j s t ∧
      toStdD 4 (fromStd α) = lv i j s t := by
  obtain ⟨i, j, hij, hi, hj, hα⟩ := isD4Root_iff.1 h
  obtain ⟨s, hs⟩ := exists_boolSign_eq hi
  obtain ⟨t, ht⟩ := exists_boolSign_eq hj
  refine ⟨i, j, s, t, hij, ?_, ?_⟩
  · rw [hα, ← hs, ← ht]
  · rw [show α = lv i j s t by rw [hα, ← hs, ← ht]]
    exact (roots_check i j s t hij).1

theorem isD4Root_lv (i j : Fin 4) (s t : Bool) (hij : i ≠ j) : IsD4Root (lv i j s t) :=
  isD4Root_single_add_single hij (boolSign_eq_one_or_eq_neg_one s)
    (boolSign_eq_one_or_eq_neg_one t)

theorem toStdD_fromStd_lv (i j : Fin 4) (s t : Bool) (hij : i ≠ j) :
    toStdD 4 (fromStd (lv i j s t)) = lv i j s t :=
  roots_check i j s t hij |>.1

theorem lv_neg (i j : Fin 4) (s t : Bool) : -lv i j s t = lv i j (!s) (!t) := by
  fin_cases i <;> fin_cases j <;> cases s <;> cases t <;> decide

theorem lv_apply_left {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    lv i j s t i = boolSign s :=
  single_add_single_apply_left hij _ _

theorem lv_apply_right {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    lv i j s t j = boolSign t :=
  single_add_single_apply_right hij _ _

theorem lv_apply_of_ne {i j k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) (s t : Bool) :
    lv i j s t k = 0 :=
  single_add_single_apply_of_ne hki hkj _ _

theorem torusChar_add (α β : Fin 4 → ℤ) (t : Fin 4 → Kˣ) :
    torusChar (α + β) t = torusChar α t * torusChar β t := by
  simp only [torusChar_apply, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

theorem torusChar_single (i : Fin 4) (z : ℤ) (t : Fin 4 → Kˣ) :
    torusChar (Pi.single i z) t = t i ^ z := by
  rw [torusChar_apply, Finset.prod_eq_single (s := Finset.univ)
    (f := fun k => t k ^ ((Pi.single i z : Fin 4 → ℤ) k)) i
    (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

theorem torusChar_lv (i j : Fin 4) (s t : Bool) (c : Fin 4 → Kˣ) :
    torusChar (lv i j s t) c = c i ^ boolSign s * c j ^ boolSign t := by
  rw [show lv i j s t = Pi.single i (boolSign s) + Pi.single j (boolSign t) from rfl,
    torusChar_add, torusChar_single, torusChar_single]

theorem reflTorus_lv_i {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : Fin 4 → Kˣ) :
    reflTorus (lv i j s t) c i =
      c i * (c i ^ boolSign s * c j ^ boolSign t) ^ (-boolSign s) := by
  rw [reflTorus, torusChar_lv, lv_apply_left hij]

theorem reflTorus_lv_j {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : Fin 4 → Kˣ) :
    reflTorus (lv i j s t) c j =
      c j * (c i ^ boolSign s * c j ^ boolSign t) ^ (-boolSign t) := by
  rw [reflTorus, torusChar_lv, lv_apply_right hij]

theorem reflTorus_lv_of_ne {i j k : Fin 4} (hki : k ≠ i) (hkj : k ≠ j) (s t : Bool)
    (c : Fin 4 → Kˣ) : reflTorus (lv i j s t) c k = c k := by
  rw [reflTorus, lv_apply_of_ne hki hkj, neg_zero, zpow_zero, mul_one]

theorem reflTorus_lv_j_pow_not {i j : Fin 4} (hij : i ≠ j) (s t : Bool)
    (c : Fin 4 → Kˣ) :
    reflTorus (lv i j s t) c j ^ boolSign (!t) = c i ^ boolSign s := by
  rw [reflTorus_lv_j hij, boolSign_not, mul_zpow, ← zpow_mul,
    show (-boolSign t) * (-boolSign t) = 1 by
      rw [neg_mul_neg, boolSign_mul_self],
    zpow_one]
  rw [← mul_assoc, mul_right_comm, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

theorem reflTorus_lv_j_pow_neg {i j : Fin 4} (hij : i ≠ j) (s t : Bool)
    (c : Fin 4 → Kˣ) :
    reflTorus (lv i j s t) c j ^ boolSign t = c i ^ boolSign (!s) := by
  rw [reflTorus_lv_j hij, boolSign_not, mul_zpow, ← zpow_mul,
    show (-boolSign t) * boolSign t = -1 by
      rw [neg_mul, boolSign_mul_self],
    zpow_neg_one, mul_inv_rev, ← zpow_neg, ← zpow_neg, ← mul_assoc]
  rw [← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem reflTorus_lv_i_pow_not {i j : Fin 4} (hij : i ≠ j) (s t : Bool)
    (c : Fin 4 → Kˣ) :
    reflTorus (lv i j s t) c i ^ boolSign (!s) = c j ^ boolSign t := by
  rw [reflTorus_lv_i hij, boolSign_not, mul_zpow, ← zpow_mul,
    show (-boolSign s) * (-boolSign s) = 1 by
      rw [neg_mul_neg, boolSign_mul_self],
    zpow_one]
  rw [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

theorem reflTorus_lv_i_pow_neg {i j : Fin 4} (hij : i ≠ j) (s t : Bool)
    (c : Fin 4 → Kˣ) :
    reflTorus (lv i j s t) c i ^ boolSign s = c j ^ boolSign (!t) := by
  rw [reflTorus_lv_i hij, boolSign_not, mul_zpow, ← zpow_mul,
    show (-boolSign s) * boolSign s = -1 by
      rw [neg_mul, boolSign_mul_self],
    zpow_neg_one, mul_inv_rev, ← zpow_neg, ← zpow_neg, ← mul_assoc]
  rw [mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

section CharTwo

variable [Finite K] [CharP K 2]

theorem act_dg_pvec (c : Fin 4 → Kˣ) (k : Fin 4) (b : Bool) :
    D4Rank.act (dg c) (AutOm.pvec k b) = (c k ^ boolSign b : K) • AutOm.pvec k b := by
  rw [act_dg]
  cases b
  · rw [AutOm.pvec_false, boolSign_false, zpow_neg_one]
    funext i
    rw [Pi.smul_apply]
    rcases ie_or_jf i with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [twHom_ie]
      simp [ie_ne_jf]
    · rw [twHom_jf]
      by_cases h : l = k
      · subst h
        simp [Units.val_inv_eq_inv_val]
      · simp [jf_injective.ne h]
  · rw [AutOm.pvec_true, boolSign_true, zpow_one]
    funext i
    rw [Pi.smul_apply]
    rcases ie_or_jf i with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [twHom_ie]
      by_cases h : l = k
      · subst h
        simp
      · simp [ie_injective.ne h]
    · rw [twHom_jf]
      simp [ie_ne_jf]

omit [Finite K] [CharP K 2] in
theorem act_eichlerC (g : Om8 K) (u w y : Fin (2 * 4) → K) :
    D4Rank.act g (AutOm.eichlerC (coordinateQuadPlus 4 K) u w y) =
      AutOm.eichlerC (coordinateQuadPlus 4 K) (D4Rank.act g u) (D4Rank.act g w)
        (D4Rank.act g y) := by
  rw [AutOm.eichlerC, AutOm.eichlerC, D4Rank.act_sub, D4Rank.act_sub, D4Rank.act_add,
    D4Rank.act_smul, D4Rank.act_smul, D4Rank.act_smul, D4Rank.polar_act, D4Rank.polar_act,
    D4Rank.Q_act]

omit [Finite K] [CharP K 2] in
theorem eichlerC_smul_smul {d : ℕ} (Q : QuadraticForm K (Fin d → K)) {u w : Fin d → K}
    (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (a b : K) (y : Fin d → K) :
    AutOm.eichlerC Q (a • u) (b • w) y = AutOm.eichlerC Q u ((a * b) • w) y := by
  have hQu : Q (a • u) = 0 := by rw [QuadraticMap.map_smul, hu, smul_zero]
  have hpol : polar Q (a • u) w = 0 := by rw [polar_smul_left, huw, smul_zero]
  have hwu : polar Q w u = 0 := by rw [polar_comm, huw]
  rw [CFSG.ClassicalGroups.Orthogonal.eichlerC_smul_right_eq Q hQu hw hpol b y,
    smul_smul (-b) a u,
    CFSG.ClassicalGroups.Orthogonal.eichlerC_smul_right_eq Q hw hu hwu ((-b) * a) y]
  congr 1
  ring

omit [Finite K] in
theorem act_X8_pvec {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) (k : Fin 4) (r : Bool) :
    D4Rank.act (X8 γ c) (AutOm.pvec k r) =
      AutOm.pvec k r + (if k = j ∧ r = !t then c • AutOm.pvec i s else 0) -
        (if k = i ∧ r = !s then c • AutOm.pvec j t else 0) := by
  rw [D4Rank.act, X8_mulVec hij h c, AutOm.eichlerC, QuadraticMap.map_smul, AutOm.form_pvec,
    smul_zero, zero_mul, zero_smul, sub_zero, polar_smul_right, AutOm.polar_pvec,
    AutOm.polar_pvec]
  by_cases h1 : k = j ∧ r = !t <;> by_cases h2 : k = i ∧ r = !s <;>
    simp [h1, h2, smul_eq_mul, ite_smul]

omit [Finite K] in
theorem act_X8_lv_iu {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (X8 (fromStd (lv i j s t)) (1 : K)) (AutOm.pvec i s) = AutOm.pvec i s := by
  rw [act_X8_pvec (K := K) hij (toStdD_fromStd_lv i j s t hij) (1 : K)]
  have h1 : ¬(i = j ∧ s = Bool.not t) := by simp [hij]
  have h2 : ¬(i = i ∧ s = Bool.not s) := by
    simp only [true_and]
    have h : s ≠ Bool.not s := by cases s <;> simp
    exact h
  rw [if_neg h1, if_neg h2]
  simp

omit [Finite K] in
theorem act_X8_lv_inu {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (X8 (fromStd (lv i j s t)) (1 : K)) (AutOm.pvec i (!s)) =
      AutOm.pvec i (!s) + AutOm.pvec j t := by
  rw [act_X8_pvec (K := K) hij (toStdD_fromStd_lv i j s t hij) (1 : K)]
  have h1 : ¬(i = j ∧ Bool.not s = Bool.not t) := by simp [hij]
  have h2 : i = i ∧ Bool.not s = Bool.not s := ⟨rfl, rfl⟩
  rw [if_neg h1, if_pos h2, one_smul, sub_eq_add_neg, D4Rank.neg_vec]
  simp

omit [Finite K] in
theorem act_X8_lv_jt {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (X8 (fromStd (lv i j s t)) (1 : K)) (AutOm.pvec j t) = AutOm.pvec j t := by
  rw [act_X8_pvec (K := K) hij (toStdD_fromStd_lv i j s t hij) (1 : K)]
  have h1 : ¬(j = j ∧ t = Bool.not t) := by
    simp only [true_and]
    have h : t ≠ Bool.not t := by cases t <;> simp
    exact h
  have h2 : ¬(j = i ∧ t = Bool.not s) := by simp [Ne.symm hij]
  rw [if_neg h1, if_neg h2]
  simp

omit [Finite K] in
theorem act_X8_lv_jnt {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (X8 (fromStd (lv i j s t)) (1 : K)) (AutOm.pvec j (!t)) =
      AutOm.pvec j (!t) + AutOm.pvec i s := by
  rw [act_X8_pvec (K := K) hij (toStdD_fromStd_lv i j s t hij) (1 : K)]
  have h1 : j = j ∧ Bool.not t = Bool.not t := ⟨rfl, rfl⟩
  have h2 : ¬(j = i ∧ Bool.not t = Bool.not s) := by simp [Ne.symm hij]
  rw [if_pos h1, if_neg h2, one_smul, sub_eq_add_neg, D4Rank.neg_vec]
  simp

omit [Finite K] in
theorem act_X8_lv_other {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (s t : Bool) (r : Bool) :
    D4Rank.act (X8 (fromStd (lv i j s t)) (1 : K)) (AutOm.pvec k r) = AutOm.pvec k r := by
  rw [act_X8_pvec (K := K) hij (toStdD_fromStd_lv i j s t hij) (1 : K)]
  have h1 : ¬(k = j ∧ r = !t) := by simp [hkj]
  have h2 : ¬(k = i ∧ r = !s) := by simp [hki]
  rw [if_neg h1, if_neg h2]
  simp

omit [Finite K] in
private theorem add_add_self_cancel (a b : Fin (2 * 4) → K) : a + (b + a) = b := by
  rw [add_comm b a, ← add_assoc, D4Rank.two_smul_vec, zero_add]

@[expose] noncomputable def weyl8 (i j : Fin 4) (s t : Bool) : Om8 K :=
  X8 (fromStd (lv i j s t)) (1 : K) * X8 (fromStd (lv i j (!s) (!t))) (1 : K) *
    X8 (fromStd (lv i j s t)) (1 : K)

omit [Finite K] in
theorem act_weyl8_iu {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (weyl8 (K := K) i j s t) (AutOm.pvec i s) = AutOm.pvec j (!t) := by
  have hX2 : D4Rank.act (X8 (fromStd (lv i j (!s) (!t))) (1 : K)) (AutOm.pvec i s) =
      AutOm.pvec i s + AutOm.pvec j (!t) := by
    simpa only [Bool.not_not] using act_X8_lv_inu (K := K) hij (!s) (!t)
  rw [weyl8, D4Rank.act_mul, D4Rank.act_mul, act_X8_lv_iu hij s t, hX2, D4Rank.act_add,
    act_X8_lv_iu hij s t, act_X8_lv_jnt hij s t]
  exact add_add_self_cancel (K := K) _ _

omit [Finite K] in
theorem act_weyl8_inu {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (weyl8 (K := K) i j s t) (AutOm.pvec i (!s)) = AutOm.pvec j t := by
  have hX2 : D4Rank.act (X8 (fromStd (lv i j (!s) (!t))) (1 : K)) (AutOm.pvec i (!s) +
      AutOm.pvec j t) = AutOm.pvec j t := by
    rw [D4Rank.act_add, act_X8_lv_iu hij (!s) (!t)]
    have h2 : D4Rank.act (X8 (fromStd (lv i j (!s) (!t))) (1 : K)) (AutOm.pvec j t) =
        AutOm.pvec j t + AutOm.pvec i (!s) := by
      simpa only [Bool.not_not] using act_X8_lv_jnt (K := K) hij (!s) (!t)
    rw [h2]
    exact add_add_self_cancel (K := K) _ _
  rw [weyl8, D4Rank.act_mul, D4Rank.act_mul, act_X8_lv_inu hij s t, hX2,
    act_X8_lv_jt hij s t]

omit [Finite K] in
theorem act_weyl8_jt {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (weyl8 (K := K) i j s t) (AutOm.pvec j t) = AutOm.pvec i (!s) := by
  have hX2 : D4Rank.act (X8 (fromStd (lv i j (!s) (!t))) (1 : K)) (AutOm.pvec j t) =
      AutOm.pvec i (!s) + AutOm.pvec j t := by
    have h := act_X8_lv_jnt (K := K) hij (!s) (!t)
    rw [show Bool.not (Bool.not t) = t from Bool.not_not t] at h
    rw [h, add_comm]
  rw [weyl8, D4Rank.act_mul, D4Rank.act_mul, act_X8_lv_jt hij s t, hX2, D4Rank.act_add,
    act_X8_lv_inu hij s t, act_X8_lv_jt hij s t, add_assoc, D4Rank.two_smul_vec, add_zero]

omit [Finite K] in
theorem act_weyl8_jnt {i j : Fin 4} (hij : i ≠ j) (s t : Bool) :
    D4Rank.act (weyl8 (K := K) i j s t) (AutOm.pvec j (!t)) = AutOm.pvec i s := by
  have hX2 : D4Rank.act (X8 (fromStd (lv i j (!s) (!t))) (1 : K)) (AutOm.pvec i s) =
      AutOm.pvec i s + AutOm.pvec j (!t) := by
    simpa only [Bool.not_not] using act_X8_lv_inu (K := K) hij (!s) (!t)
  rw [weyl8, D4Rank.act_mul, D4Rank.act_mul, act_X8_lv_jnt hij s t, D4Rank.act_add,
    act_X8_lv_jt hij (!s) (!t), hX2,
    show AutOm.pvec j (!t) + (AutOm.pvec i s + AutOm.pvec j (!t)) = AutOm.pvec i s from
      add_add_self_cancel (K := K) _ _]
  exact act_X8_lv_iu hij s t

omit [Finite K] in
theorem act_weyl8_other {i j k : Fin 4} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (s t : Bool) (r : Bool) :
    D4Rank.act (weyl8 (K := K) i j s t) (AutOm.pvec k r) = AutOm.pvec k r := by
  rw [weyl8, D4Rank.act_mul, D4Rank.act_mul, act_X8_lv_other hij hki hkj s t r,
    act_X8_lv_other hij hki hkj (!s) (!t) r, act_X8_lv_other hij hki hkj s t r]

omit [Finite K] [CharP K 2] in
theorem eq_of_act_pvec {x y : Om8 K}
    (h : ∀ k r, D4Rank.act x (AutOm.pvec k r) = D4Rank.act y (AutOm.pvec k r)) : x = y := by
  refine L613KG.om8_ext fun v => ?_
  have hW : ∀ k r, AutOm.pvec k r ∈ LinearMap.ker (D4Rank.omRep x - D4Rank.omRep y) := by
    intro k r
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact h k r
  have htop : LinearMap.ker (D4Rank.omRep x - D4Rank.omRep y) = ⊤ :=
    AutOm.eq_top_of_pvec_mem hW
  have hv : v ∈ LinearMap.ker (D4Rank.omRep x - D4Rank.omRep y) := by
    rw [htop]
    exact Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hv
  exact hv

theorem weyl8_mul_dg {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (c : Fin 4 → Kˣ) :
    weyl8 (K := K) i j s t * dg c = dg (reflTorus (lv i j s t) c) * weyl8 (K := K) i j s t := by
  refine eq_of_act_pvec fun k r => ?_
  rw [D4Rank.act_mul, D4Rank.act_mul, act_dg_pvec, D4Rank.act_smul]
  by_cases hki : k = i
  · subst hki
    rcases Bool.eq_or_eq_not r s with hr | hr
    · rw [hr, act_weyl8_iu hij s t, act_dg_pvec]
      congr 1
      simpa only [Units.val_zpow_eq_zpow_val] using
        (congrArg Units.val (reflTorus_lv_j_pow_not hij s t c)).symm
    · rw [hr, act_weyl8_inu hij s t, act_dg_pvec]
      congr 1
      simpa only [Units.val_zpow_eq_zpow_val] using
        (congrArg Units.val (reflTorus_lv_j_pow_neg hij s t c)).symm
  · by_cases hkj : k = j
    · subst hkj
      rcases Bool.eq_or_eq_not r t with hr | hr
      · rw [hr, act_weyl8_jt hij s t, act_dg_pvec]
        congr 1
        simpa only [Units.val_zpow_eq_zpow_val] using
          (congrArg Units.val (reflTorus_lv_i_pow_not hij s t c)).symm
      · rw [hr, act_weyl8_jnt hij s t, act_dg_pvec]
        congr 1
        simpa only [Units.val_zpow_eq_zpow_val] using
          (congrArg Units.val (reflTorus_lv_i_pow_neg hij s t c)).symm
    · rw [act_weyl8_other hij hki hkj s t r, act_dg_pvec, reflTorus_lv_of_ne hki hkj s t c]

private theorem dotProduct_add_self (α β : Fin 4 → ℤ) :
    (α + β) ⬝ᵥ (α + β) = α ⬝ᵥ α + 2 * (α ⬝ᵥ β) + β ⬝ᵥ β := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm β α]
  ring

theorem add_ne_zero_of_dotProduct_nonneg {α β : Fin 4 → ℤ} (hα : IsD4Root α)
    (hβ : IsD4Root β) (h : 0 ≤ α ⬝ᵥ β) : α + β ≠ 0 := by
  intro h0
  have hα' : α ⬝ᵥ α = 2 := hα
  have hb : β = -α := eq_neg_of_add_eq_zero_right h0
  rw [hb, dotProduct_neg, hα'] at h
  norm_num at h

theorem not_isLong_add_of_dotProduct_nonneg {α β : Fin 4 → ℤ} (hα : IsD4Root α)
    (hβ : IsD4Root β) (h : 0 ≤ α ⬝ᵥ β) : ¬ IsLong (α + β) := by
  intro hl
  have hsum : (α + β) ⬝ᵥ (α + β) = 2 := isD4Root_of_isLong hl
  have hα' : α ⬝ᵥ α = 2 := hα
  have hβ' : β ⬝ᵥ β = 2 := hβ
  rw [dotProduct_add_self, hα', hβ'] at hsum
  linarith

omit [Finite K] [CharP K 2] in
theorem X8_add (α : Fin 4 → ℤ) (c d : K) :
    X8 (fromStd α) (c + d) = X8 (fromStd α) c * X8 (fromStd α) d := by
  rw [X8, X8, X8, xr_add, map_mul]

omit [Finite K] [CharP K 2] in
theorem X8_fromStd_eq_model {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) :
    X8 (fromStd α) c = model8 (rootElt (plusFrame 4 K three_le_four) α c) := by
  rw [X8, show xr (fromStd α) c =
    rootElt (plusFrame 4 K three_le_four) α c from by
    rw [show xr (fromStd α) c =
      rootElt (plusFrame 4 K three_le_four) (toStdD 4 (fromStd α)) c from rfl,
      toStdD_fromStd_of_isD4Root hα]]

omit [Finite K] in
theorem commutator_X8 {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β)
    (h : α ⬝ᵥ β = -1) (c d : K) :
    ⁅X8 (fromStd α) c, X8 (fromStd β) d⁆ = X8 (fromStd (α + β)) (c * d) := by
  have hαlong : IsLong α := isLong_of_isD4Root hα
  have hβlong : IsLong β := isLong_of_isD4Root hβ
  have hsum : IsD4Root (α + β) := IsD4Root.add hα hβ h
  have hlong : IsLong (α + β) := isLong_of_isD4Root hsum
  have hne : α + β ≠ 0 := by
    intro h0
    have hα' : α ⬝ᵥ α = 2 := hα
    have hb : β = -α := eq_neg_of_add_eq_zero_right h0
    rw [hb, dotProduct_neg, hα'] at h
    norm_num at h
  have hcs : (chainSign α β : K) = 1 :=
    intCast_eq_one_of_natAbs (by
      rcases chainSign_eq_one_or_eq_neg_one α β with h' | h' <;> rw [h'] <;> rfl)
  rw [X8_fromStd_eq_model hα c, X8_fromStd_eq_model hβ d,
    ← map_commutatorElement model8 (rootElt (plusFrame 4 K three_le_four) α c)
      (rootElt (plusFrame 4 K three_le_four) β d),
    commutator_rootElt (plusFrame 4 K three_le_four) hαlong hβlong hne hlong c d, hcs, one_mul,
    ← X8_fromStd_eq_model hsum (c * d)]

omit [Finite K] [CharP K 2] in
theorem commute_X8 {α β : Fin 4 → ℤ} (hα : IsD4Root α) (hβ : IsD4Root β)
    (h : 0 ≤ α ⬝ᵥ β) (c d : K) : Commute (X8 (fromStd α) c) (X8 (fromStd β) d) := by
  have hαlong : IsLong α := isLong_of_isD4Root hα
  have hβlong : IsLong β := isLong_of_isD4Root hβ
  have hne : α + β ≠ 0 := add_ne_zero_of_dotProduct_nonneg hα hβ h
  have hnot : ¬ IsLong (α + β) := not_isLong_add_of_dotProduct_nonneg hα hβ h
  rw [X8_fromStd_eq_model hα c, X8_fromStd_eq_model hβ d]
  exact (commute_rootElt (plusFrame 4 K three_le_four) hαlong hβlong hne hnot c d).map model8

theorem weyl8_conj {β : Fin 4 → ℤ} (hβ : IsD4Root β) (c : Fin 4 → Kˣ) :
    X8 (fromStd β) (1 : K) * X8 (fromStd (-β)) (1 : K) * X8 (fromStd β) (1 : K) * dg c *
      (X8 (fromStd β) (1 : K) * X8 (fromStd (-β)) (1 : K) * X8 (fromStd β) (1 : K))⁻¹ =
      dg (reflTorus β c) := by
  obtain ⟨i, j, s, t, hij, hβeq, hto⟩ := exists_lv_of_isD4Root hβ
  have hneg : -β = lv i j (!s) (!t) := by rw [hβeq, lv_neg]
  rw [hneg, hβeq]
  have hmul := weyl8_mul_dg (K := K) hij s t c
  calc weyl8 (K := K) i j s t * dg c * (weyl8 (K := K) i j s t)⁻¹
      = (dg (reflTorus (lv i j s t) c) * weyl8 (K := K) i j s t) *
          (weyl8 (K := K) i j s t)⁻¹ := by rw [hmul]
    _ = dg (reflTorus (lv i j s t) c) := by group

omit [Finite K] [CharP K 2] in
theorem closure_X8_eq_top :
    Subgroup.closure {g : Om8 K | ∃ γ ∈ rootsD4, ∃ c : K, X8 γ c = g} = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨w, rfl⟩ := AutOm.spinModelPlus_surjective three_le_four z
  have hle : (⨆ γ ∈ rootsD4, plusRootGroup 4 K three_le_four γ) ≤
      Subgroup.comap model8
        (Subgroup.closure {g : Om8 K | ∃ γ ∈ rootsD4, ∃ c : K, X8 γ c = g}) := by
    refine iSup₂_le fun γ hγ z hz => ?_
    obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization three_le_four γ hγ).1 z).1 hz
    exact Subgroup.subset_closure ⟨γ, hγ, c, rfl⟩
  rw [plusDatum_iSup_eq_top 4 K three_le_four] at hle
  exact hle (Subgroup.mem_top w)

omit [Finite K] [CharP K 2] in
theorem closure_rootSet_eq :
    {g : Om8 K | ∃ α, IsD4Root α ∧ ∃ c : K, X8 (fromStd α) c = g} =
      {g : Om8 K | ∃ γ ∈ rootsD4, ∃ c : K, X8 γ c = g} := by
  ext g
  constructor
  · rintro ⟨α, hα, c, rfl⟩
    exact ⟨fromStd α, mem_rootsD4_fromStd_of_isD4Root hα, c, rfl⟩
  · rintro ⟨γ, hγ, c, rfl⟩
    obtain ⟨i, j, s, t, hij, hto, hγeq⟩ := exists_eq_fromStd hγ
    exact ⟨lv i j s t, isD4Root_lv i j s t hij, c, by rw [hγeq]⟩

theorem dgHom_conj_X8 {α : Fin 4 → ℤ} (hα : IsD4Root α) (c : K) (t : Fin 4 → Kˣ) :
    dgHom t * X8 (fromStd α) c * (dgHom t)⁻¹ =
      X8 (fromStd α) (((torusChar α t : Kˣ) : K) * c) := by
  obtain ⟨i, j, u, v, hij, hαeq, hto⟩ := exists_lv_of_isD4Root hα
  have hdg : dgHom t = dg t := rfl
  have hsc : (t j ^ boolSign v : K) * (c * (t i ^ boolSign u : K)) =
      ((torusChar α t : Kˣ) : K) * c := by
    rw [hαeq, torusChar_lv, Units.val_mul, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val]
    ring
  refine L613KG.om8_ext fun y => ?_
  have hX : ∀ z, D4Rank.act (X8 (fromStd α) c) z =
      AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec j v) (c • AutOm.pvec i u) z :=
    fun z => X8_mulVec hij hto c z
  have hXk : D4Rank.act (X8 (fromStd α) (((torusChar α t : Kˣ) : K) * c)) y =
      AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec j v)
        ((((torusChar α t : Kˣ) : K) * c) • AutOm.pvec i u) y :=
    X8_mulVec hij hto _ y
  rw [hdg, D4Rank.act_mul, D4Rank.act_mul, hX, act_eichlerC, D4Rank.act_act_inv,
    act_dg_pvec, D4Rank.act_smul, act_dg_pvec, smul_smul,
    eichlerC_smul_smul (coordinateQuadPlus 4 K) (AutOm.form_pvec j v)
      (AutOm.form_pvec i u) (AutOm.polar_pvec_of_ne (Ne.symm hij) v u), hsc, ← hXk]

end CharTwo

@[expose] noncomputable def om8Datum (K : Type) [Field K] [Finite K] [CharP K 2] :
    D4Datum (Om8 K) K where
  x α c := X8 (fromStd α) c
  h := dgHom
  x_add := fun α _ c d => X8_add α c d
  h_conj := fun α hα t c => dgHom_conj_X8 hα c t
  weyl_conj := fun β hβ t => weyl8_conj hβ t
  comm_eq := fun α β hα hβ h c d => commutator_X8 hα hβ h c d
  commute := fun α β hα hβ h c d => commute_X8 hα hβ h c d
  closure_eq := by
    rw [closure_rootSet_eq]
    exact closure_X8_eq_top

theorem om8Datum_x (K : Type) [Field K] [Finite K] [CharP K 2] (α : Fin 4 → ℤ) (c : K) :
    (om8Datum K).x α c = X8 (fromStd α) c := rfl

theorem om8Datum_h (K : Type) [Field K] [Finite K] [CharP K 2] (t : Fin 4 → Kˣ) :
    (om8Datum K).h t = dg t := rfl

theorem om8Datum_x_mulVec (K : Type) [Field K] [Finite K] [CharP K 2] {i j : Fin 4}
    (hij : i ≠ j) (s t : Bool) (c : K) (y : Fin (2 * 4) → K) :
    Matrix.mulVec (((om8Datum K).x (lv i j s t) c : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) y =
      AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec j t) (c • AutOm.pvec i s) y :=
  X8_mulVec hij (toStdD_fromStd_lv i j s t hij) c y

end CFSG.LieType.D4Small
