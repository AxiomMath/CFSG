module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

structure OctaSys (ι V : Type*) [CommGroup V] where
  z : ι → V
  nn : ι → ι → ZMod 2
  sg : ι → ι → ZMod 2
  sq : ∀ v : V, v * v = 1
  z_inj : Function.Injective z
  z_ne : ∀ p, z p ≠ 1
  nn_self : ∀ p, nn p p = 0
  nn_symm : ∀ p q, nn p q = nn q p
  nn_add : ∀ t p q s, z s = z p * z q → nn t s = nn t p + nn t q
  third : ∀ p q, nn p q = 1 → ∃ s, z s = z p * z q
  sign_col : ∀ p q t, nn p q = 1 → nn p t = 1 → nn q t = 1 → z t = z p * z q →
    sg p t + sg p q + sg q t = 0
  sign_ncol : ∀ p q t, nn p q = 1 → nn p t = 1 → nn q t = 1 → z t ≠ z p * z q →
    sg p t + sg p q + sg q t = 1

theorem eq_of_mul_eq_one_of_sq {G : Type*} [CommGroup G] (sq : ∀ x : G, x * x = 1) {a b : G}
    (h : a * b = 1) : a = b := by
  calc a = a * (b * b) := by rw [sq b, mul_one]
    _ = a * b * b := by rw [mul_assoc]
    _ = b := by rw [h, one_mul]

namespace OctaSys

variable {ι V : Type*} [CommGroup V] (S : OctaSys ι V)

@[expose] def Reach (p q : ι) : Prop := Relation.ReflTransGen (fun a b => S.nn a b = 0) p q

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem z_mul_eq_one_iff {p q : ι} : S.z p * S.z q = 1 ↔ p = q := by
  constructor
  · intro h
    exact S.z_inj (eq_of_mul_eq_one_of_sq S.sq h)
  · rintro rfl
    exact S.sq _

theorem reach_symm {p q : ι} (h : S.Reach p q) : S.Reach q p := by
  unfold Reach at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head ((S.nn_symm _ _).trans hbc) ih

theorem reach_of_nn_eq_zero {p q : ι} (h : S.nn p q = 0) : S.Reach p q :=
  Relation.ReflTransGen.single h

theorem reach_trans {p q r : ι} (h : S.Reach p q) (h' : S.Reach q r) : S.Reach p r :=
  Relation.ReflTransGen.trans h h'

theorem nn_eq_one_of_far_aux {v p q : ι} (hq : ¬ S.Reach v q) (hvp : S.nn v p = 0) :
    S.nn q p = 1 := by
  rcases zmod2_cases (S.nn q p) with h | h
  · exact absurd (S.reach_trans (S.reach_of_nn_eq_zero hvp)
      (S.reach_of_nn_eq_zero ((S.nn_symm p q).trans h))) hq
  · exact h

theorem nn_eq_zero_of_far {v p y q : ι} (hq : ¬ S.Reach v q) (hvp : S.nn v p = 0)
    (hvy : S.nn v y = 0) : S.nn p y = 0 := by
  have two : (1 : ZMod 2) + 1 = 0 := by decide
  by_contra h
  have h1 : S.nn p y = 1 := by
    rcases zmod2_cases (S.nn p y) with h' | h'
    · exact absurd h' h
    · exact h'
  obtain ⟨w, hw⟩ := S.third p y h1
  have hvw : S.nn v w = 0 := by
    rw [S.nn_add v p y w hw, hvp, hvy, add_zero]
  have hqp : S.nn q p = 1 := S.nn_eq_one_of_far_aux hq hvp
  have hqy : S.nn q y = 1 := S.nn_eq_one_of_far_aux hq hvy
  have hqw : S.nn q w = 0 := by
    rw [S.nn_add q p y w hw, hqp, hqy, two]
  apply hq
  exact S.reach_trans (S.reach_of_nn_eq_zero hvw) (S.reach_symm (S.reach_of_nn_eq_zero hqw))

theorem nn_eq_one_of_far {v p q : ι} (hq : ¬ S.Reach v q) (hvp : S.nn v p = 0) :
    S.nn q p = 1 :=
  S.nn_eq_one_of_far_aux hq hvp

theorem five_clique_core (p : Fin 5 → ι) (hinj : Function.Injective p)
    (hadj : ∀ a b, S.nn (p a) (p b) = 0) (q : ι) (hq : ∀ a, S.nn q (p a) = 1)
    (i j k : Fin 5) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hindep : S.z (p 0) * S.z (p i) * S.z (p j) * S.z (p k) ≠ 1) : False := by
  have two : (1 : ZMod 2) + 1 = 0 := by decide
  obtain ⟨q0, hq0⟩ := S.third q (p 0) (hq 0)
  obtain ⟨qk, hqk⟩ := S.third q (p k) (hq k)
  have n_q0pj : S.nn q0 (p j) = 1 := by
    linear_combination (S.nn_symm q0 (p j)) + (S.nn_add (p j) q (p 0) q0 hq0)
      + (S.nn_symm (p j) q) + hq j + hadj j 0
  obtain ⟨qt, hqt⟩ := S.third q0 (p j) n_q0pj
  have n_p0Q : S.nn (p 0) q = 1 := (S.nn_symm (p 0) q).trans (hq 0)
  have n_piQ : S.nn (p i) q = 1 := (S.nn_symm (p i) q).trans (hq i)
  have n_p0q0 : S.nn (p 0) q0 = 1 := by
    linear_combination (S.nn_add (p 0) q (p 0) q0 hq0) + n_p0Q + S.nn_self (p 0)
  have n_piq0 : S.nn (p i) q0 = 1 := by
    linear_combination (S.nn_add (p i) q (p 0) q0 hq0) + n_piQ + hadj i 0
  have n_p0qk : S.nn (p 0) qk = 1 := by
    linear_combination (S.nn_add (p 0) q (p k) qk hqk) + n_p0Q + hadj 0 k
  have n_piqk : S.nn (p i) qk = 1 := by
    linear_combination (S.nn_add (p i) q (p k) qk hqk) + n_piQ + hadj i k
  have n_p0qt : S.nn (p 0) qt = 1 := by
    linear_combination (S.nn_add (p 0) q0 (p j) qt hqt) + n_p0q0 + hadj 0 j
  have n_piqt : S.nn (p i) qt = 1 := by
    linear_combination (S.nn_add (p i) q0 (p j) qt hqt) + n_piq0 + hadj i j
  have n_Qq0 : S.nn q q0 = 1 := by
    linear_combination (S.nn_add q q (p 0) q0 hq0) + S.nn_self q + hq 0
  have n_Qqk : S.nn q qk = 1 := by
    linear_combination (S.nn_add q q (p k) qk hqk) + S.nn_self q + hq k
  have n_q0qt : S.nn q0 qt = 1 := by
    linear_combination (S.nn_add q0 q0 (p j) qt hqt) + S.nn_self q0 + n_q0pj
  have n_qtq0 : S.nn qt q0 = 1 := by
    linear_combination n_q0qt - (S.nn_symm q0 qt)
  have n_qkq0 : S.nn qk q0 = 0 := by
    linear_combination (S.nn_add qk q (p 0) q0 hq0) + (S.nn_symm qk q) + n_Qqk
      + (S.nn_symm qk (p 0)) + n_p0qk + two
  have n_qtqk : S.nn qt qk = 1 := by
    linear_combination (S.nn_symm qt qk) + (S.nn_add qk q0 (p j) qt hqt) + n_qkq0
      + (S.nn_symm qk (p j)) + (S.nn_add (p j) q (p k) qk hqk) + (S.nn_symm (p j) q)
      + hq j + hadj j k
  have hcol : S.z q0 = S.z (p 0) * S.z q := by rw [hq0, mul_comm]
  have f2 : S.z qk ≠ S.z (p 0) * S.z q := by
    intro h
    rw [hqk, mul_comm (S.z (p 0)) (S.z q)] at h
    exact hk (hinj (S.z_inj (mul_left_cancel h)))
  have f3 : S.z q0 ≠ S.z (p 0) * S.z qt := by
    intro h
    rw [hqt, hq0] at h
    have h' : S.z q * S.z (p 0) = S.z q * S.z (p j) := by
      rw [h, show S.z (p 0) * (S.z q * S.z (p 0) * S.z (p j))
        = (S.z (p 0) * S.z (p 0)) * (S.z q * S.z (p j)) by ac_rfl, S.sq, one_mul]
    exact hj (hinj (S.z_inj (mul_left_cancel h'))).symm
  have f4 : S.z qk ≠ S.z (p 0) * S.z qt := by
    intro h
    rw [hqk, hqt, hq0] at h
    have h' : S.z q * S.z (p k) = S.z q * S.z (p j) := by
      rw [h, show S.z (p 0) * (S.z q * S.z (p 0) * S.z (p j))
        = (S.z (p 0) * S.z (p 0)) * (S.z q * S.z (p j)) by ac_rfl, S.sq, one_mul]
    exact hjk (hinj (S.z_inj (mul_left_cancel h'))).symm
  have f5 : S.z q0 ≠ S.z (p i) * S.z q := by
    intro h
    rw [hq0, mul_comm (S.z (p i)) (S.z q)] at h
    exact hi (hinj (S.z_inj (mul_left_cancel h))).symm
  have f6 : S.z qk ≠ S.z (p i) * S.z q := by
    intro h
    rw [hqk, mul_comm (S.z (p i)) (S.z q)] at h
    exact hik (hinj (S.z_inj (mul_left_cancel h))).symm
  have f7 : S.z q0 ≠ S.z (p i) * S.z qt := by
    intro h
    rw [hqt, hq0] at h
    have h1 : S.z (p i) * S.z (p j) = 1 := by
      apply mul_right_cancel (b := S.z q * S.z (p 0))
      rw [one_mul]
      calc S.z (p i) * S.z (p j) * (S.z q * S.z (p 0))
          = S.z (p i) * (S.z q * S.z (p 0) * S.z (p j)) := by ac_rfl
        _ = S.z q * S.z (p 0) := h.symm
    exact hij (hinj (S.z_mul_eq_one_iff.mp h1))
  have f8 : S.z qk ≠ S.z (p i) * S.z qt := by
    intro h
    rw [hqk, hqt, hq0] at h
    have h2 : S.z (p k) = S.z (p 0) * S.z (p i) * S.z (p j) := by
      apply mul_left_cancel (a := S.z q)
      calc S.z q * S.z (p k) = S.z (p i) * (S.z q * S.z (p 0) * S.z (p j)) := h
        _ = S.z q * (S.z (p 0) * S.z (p i) * S.z (p j)) := by ac_rfl
    apply hindep
    rw [h2]
    exact S.sq _
  have e1 := S.sign_col (p 0) q q0 n_p0Q n_p0q0 n_Qq0 hcol
  have e2 := S.sign_ncol (p 0) q qk n_p0Q n_p0qk n_Qqk f2
  have e3 := S.sign_ncol (p 0) qt q0 n_p0qt n_p0q0 n_qtq0 f3
  have e4 := S.sign_ncol (p 0) qt qk n_p0qt n_p0qk n_qtqk f4
  have e5 := S.sign_ncol (p i) q q0 n_piQ n_piq0 n_Qq0 f5
  have e6 := S.sign_ncol (p i) q qk n_piQ n_piqk n_Qqk f6
  have e7 := S.sign_ncol (p i) qt q0 n_piqt n_piq0 n_qtq0 f7
  have e8 := S.sign_ncol (p i) qt qk n_piqt n_piqk n_qtqk f8
  have key : (2 : ZMod 2) * (S.sg (p 0) q0 + S.sg (p 0) q + S.sg (p 0) qk + S.sg (p 0) qt
      + S.sg (p i) q0 + S.sg (p i) q + S.sg (p i) qk + S.sg (p i) qt
      + S.sg q q0 + S.sg q qk + S.sg qt q0 + S.sg qt qk) = 7 := by
    linear_combination e1 + e2 + e3 + e4 + e5 + e6 + e7 + e8
  have h20 : (2 : ZMod 2) = 0 := by decide
  rw [h20, zero_mul] at key
  exact absurd key (by decide)

theorem five_clique_false (p : Fin 5 → ι) (hinj : Function.Injective p)
    (hadj : ∀ a b, S.nn (p a) (p b) = 0) (q : ι) (hq : ¬ S.Reach (p 0) q) : False := by
  have hq' : ∀ a, S.nn q (p a) = 1 := fun a => S.nn_eq_one_of_far hq (hadj 0 a)
  by_cases h : S.z (p 0) * S.z (p 1) * S.z (p 2) * S.z (p 3) = 1
  · refine S.five_clique_core p hinj hadj q hq' 1 2 4 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ?_
    intro h'
    have h3 : S.z (p 0) * S.z (p 1) * S.z (p 2) = S.z (p 3) :=
      eq_of_mul_eq_one_of_sq S.sq h
    have h4 : S.z (p 0) * S.z (p 1) * S.z (p 2) = S.z (p 4) :=
      eq_of_mul_eq_one_of_sq S.sq h'
    exact absurd (hinj (S.z_inj (h3.symm.trans h4))) (by decide)
  · exact S.five_clique_core p hinj hadj q hq' 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) h

theorem exists_fourth {p₀ p₁ p₂ q : ι} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂) (h12 : p₁ ≠ p₂)
    (hadj : ∀ a b, a ∈ ({p₀, p₁, p₂} : Set ι) → b ∈ ({p₀, p₁, p₂} : Set ι) → S.nn a b = 0)
    (hq : ¬ S.Reach p₀ q) :
    ∃ s, S.z s = S.z p₀ * S.z p₁ * S.z p₂ ∧ s ≠ p₀ ∧ s ≠ p₁ ∧ s ≠ p₂ ∧
      S.nn p₀ s = 0 ∧ S.nn p₁ s = 0 ∧ S.nn p₂ s = 0 := by
  have two : (1 : ZMod 2) + 1 = 0 := by decide
  have a01 : S.nn p₀ p₁ = 0 := hadj _ _ (by simp) (by simp)
  have a02 : S.nn p₀ p₂ = 0 := hadj _ _ (by simp) (by simp)
  have a12 : S.nn p₁ p₂ = 0 := hadj _ _ (by simp) (by simp)
  have n0 : S.nn q p₀ = 1 := S.nn_eq_one_of_far hq (S.nn_self p₀)
  have n1 : S.nn q p₁ = 1 := S.nn_eq_one_of_far hq a01
  have n2 : S.nn q p₂ = 1 := S.nn_eq_one_of_far hq a02
  obtain ⟨q0, hq0⟩ := S.third q p₀ n0
  have m1 : S.nn q0 p₁ = 1 := by
    linear_combination (S.nn_symm q0 p₁) + (S.nn_add p₁ q p₀ q0 hq0) + (S.nn_symm p₁ q) + n1
      + (S.nn_symm p₁ p₀) + a01
  obtain ⟨s1, hs1⟩ := S.third q0 p₁ m1
  obtain ⟨u, hu⟩ := S.third q p₂ n2
  have b1 : S.nn u q = 1 := by
    linear_combination (S.nn_symm u q) + (S.nn_add q q p₂ u hu) + S.nn_self q + n2
  have b2 : S.nn u p₀ = 1 := by
    linear_combination (S.nn_symm u p₀) + (S.nn_add p₀ q p₂ u hu) + (S.nn_symm p₀ q) + n0 + a02
  have b3 : S.nn u q0 = 0 := by
    linear_combination (S.nn_add u q p₀ q0 hq0) + b1 + b2 + two
  have b4 : S.nn u p₁ = 1 := by
    linear_combination (S.nn_symm u p₁) + (S.nn_add p₁ q p₂ u hu) + (S.nn_symm p₁ q) + n1 + a12
  have b5 : S.nn s1 u = 1 := by
    linear_combination (S.nn_symm s1 u) + (S.nn_add u q0 p₁ s1 hs1) + b3 + b4
  obtain ⟨s, hs⟩ := S.third s1 u b5
  have hzs : S.z s = S.z p₀ * S.z p₁ * S.z p₂ := by
    rw [hs, hs1, hq0, hu]
    rw [show S.z q * S.z p₀ * S.z p₁ * (S.z q * S.z p₂)
        = (S.z q * S.z q) * (S.z p₀ * S.z p₁ * S.z p₂) by ac_rfl, S.sq, one_mul]
  have c0q0 : S.nn p₀ q0 = 1 := by
    linear_combination (S.nn_add p₀ q p₀ q0 hq0) + (S.nn_symm p₀ q) + n0 + S.nn_self p₀
  have c0s1 : S.nn p₀ s1 = 1 := by
    linear_combination (S.nn_add p₀ q0 p₁ s1 hs1) + c0q0 + a01
  have c0u : S.nn p₀ u = 1 := by
    linear_combination (S.nn_symm p₀ u) + b2
  have c0s : S.nn p₀ s = 0 := by
    linear_combination (S.nn_add p₀ s1 u s hs) + c0s1 + c0u + two
  have c1q0 : S.nn p₁ q0 = 1 := (S.nn_symm p₁ q0).trans m1
  have c1s1 : S.nn p₁ s1 = 1 := by
    linear_combination (S.nn_add p₁ q0 p₁ s1 hs1) + c1q0 + S.nn_self p₁
  have c1u : S.nn p₁ u = 1 := by
    linear_combination (S.nn_symm p₁ u) + b4
  have c1s : S.nn p₁ s = 0 := by
    linear_combination (S.nn_add p₁ s1 u s hs) + c1s1 + c1u + two
  have c2q0 : S.nn p₂ q0 = 1 := by
    linear_combination (S.nn_add p₂ q p₀ q0 hq0) + (S.nn_symm p₂ q) + n2 + (S.nn_symm p₂ p₀)
      + a02
  have c2s1 : S.nn p₂ s1 = 1 := by
    linear_combination (S.nn_add p₂ q0 p₁ s1 hs1) + c2q0 + (S.nn_symm p₂ p₁) + a12
  have c2u : S.nn p₂ u = 1 := by
    linear_combination (S.nn_add p₂ q p₂ u hu) + (S.nn_symm p₂ q) + n2 + S.nn_self p₂
  have c2s : S.nn p₂ s = 0 := by
    linear_combination (S.nn_add p₂ s1 u s hs) + c2s1 + c2u + two
  have hs0 : s ≠ p₀ := by
    intro h
    rw [h] at hzs
    have h1 : S.z p₁ * S.z p₂ = 1 := by
      apply mul_left_cancel (a := S.z p₀)
      rw [mul_one, ← mul_assoc]
      exact hzs.symm
    exact h12 (S.z_mul_eq_one_iff.mp h1)
  have hs1' : s ≠ p₁ := by
    intro h
    rw [h] at hzs
    have h1 : S.z p₀ * S.z p₂ = 1 := by
      apply mul_left_cancel (a := S.z p₁)
      rw [mul_one, show S.z p₁ * (S.z p₀ * S.z p₂) = S.z p₀ * S.z p₁ * S.z p₂ by ac_rfl]
      exact hzs.symm
    exact h02 (S.z_mul_eq_one_iff.mp h1)
  have hs2' : s ≠ p₂ := by
    intro h
    rw [h] at hzs
    have h1 : S.z p₀ * S.z p₁ = 1 := by
      apply mul_left_cancel (a := S.z p₂)
      rw [mul_one, show S.z p₂ * (S.z p₀ * S.z p₁) = S.z p₀ * S.z p₁ * S.z p₂ by ac_rfl]
      exact hzs.symm
    exact h01 (S.z_mul_eq_one_iff.mp h1)
  exact ⟨s, hzs, hs0, hs1', hs2', c0s, c1s, c2s⟩

theorem eq_of_nn_eq_zero_of_far {p₀ p₁ p₂ s q m : ι} (h01 : p₀ ≠ p₁) (h02 : p₀ ≠ p₂)
    (h12 : p₁ ≠ p₂) (hs0 : s ≠ p₀) (hs1 : s ≠ p₁) (hs2 : s ≠ p₂)
    (hadj : ∀ a b, a ∈ ({p₀, p₁, p₂, s} : Set ι) → b ∈ ({p₀, p₁, p₂, s} : Set ι) →
      S.nn a b = 0)
    (hq : ¬ S.Reach p₀ q) (hm0 : m ≠ p₀) (hm : S.nn p₀ m = 0) :
    m = p₁ ∨ m = p₂ ∨ m = s := by
  by_contra hne
  have hm1 : m ≠ p₁ := fun h => hne (Or.inl h)
  have hm2 : m ≠ p₂ := fun h => hne (Or.inr (Or.inl h))
  have hms : m ≠ s := fun h => hne (Or.inr (Or.inr h))
  have a01 : S.nn p₀ p₁ = 0 := hadj _ _ (by simp) (by simp)
  have a02 : S.nn p₀ p₂ = 0 := hadj _ _ (by simp) (by simp)
  have a0s : S.nn p₀ s = 0 := hadj _ _ (by simp) (by simp)
  have a12 : S.nn p₁ p₂ = 0 := hadj _ _ (by simp) (by simp)
  have a1s : S.nn p₁ s = 0 := hadj _ _ (by simp) (by simp)
  have a2s : S.nn p₂ s = 0 := hadj _ _ (by simp) (by simp)
  have b1 : S.nn p₁ m = 0 := S.nn_eq_zero_of_far hq a01 hm
  have b2 : S.nn p₂ m = 0 := S.nn_eq_zero_of_far hq a02 hm
  have bs : S.nn s m = 0 := S.nn_eq_zero_of_far hq a0s hm
  have hinj : Function.Injective ![p₀, p₁, p₂, s, m] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | exact absurd hab h01 | exact absurd hab h02 | exact absurd hab h12
      | exact absurd hab hs0 | exact absurd hab hs1 | exact absurd hab hs2
      | exact absurd hab hm0 | exact absurd hab hm1 | exact absurd hab hm2
      | exact absurd hab hms
      | exact absurd hab h01.symm | exact absurd hab h02.symm | exact absurd hab h12.symm
      | exact absurd hab hs0.symm | exact absurd hab hs1.symm | exact absurd hab hs2.symm
      | exact absurd hab hm0.symm | exact absurd hab hm1.symm | exact absurd hab hm2.symm
      | exact absurd hab hms.symm
  have hadj5 : ∀ a b, S.nn (![p₀, p₁, p₂, s, m] a) (![p₀, p₁, p₂, s, m] b) = 0 := by
    have sym : ∀ x y, S.nn x y = 0 → S.nn y x = 0 := fun x y h => (S.nn_symm y x).trans h
    intro a b
    fin_cases a <;> fin_cases b <;> first
      | exact S.nn_self _
      | exact a01 | exact a02 | exact a0s | exact a12 | exact a1s | exact a2s
      | exact hm | exact b1 | exact b2 | exact bs
      | exact sym _ _ a01 | exact sym _ _ a02 | exact sym _ _ a0s | exact sym _ _ a12
      | exact sym _ _ a1s | exact sym _ _ a2s | exact sym _ _ hm | exact sym _ _ b1
      | exact sym _ _ b2 | exact sym _ _ bs
  exact S.five_clique_false ![p₀, p₁, p₂, s, m] hinj hadj5 q hq

end OctaSys

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
