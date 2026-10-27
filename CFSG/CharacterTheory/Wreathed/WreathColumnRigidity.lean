module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed

namespace WreathColumn

variable {I : Type*} [Fintype I] [DecidableEq I]

@[expose] noncomputable def degree (d : I → ℝ) : (I → ℤ) →+ ℝ where
  toFun v := ∑ i, (v i : ℝ) * d i
  map_zero' := by simp
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq I] in
theorem degree_apply (d : I → ℝ) (v : I → ℤ) : degree d v = ∑ i, (v i : ℝ) * d i :=
  rfl

theorem degree_single (d : I → ℝ) (j : I) (x : ℤ) : degree d (Pi.single j x) = x * d j := by
  rw [degree_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [hij]
  · simp

omit [DecidableEq I] in
theorem mul_self_le_dotProduct_self (v : I → ℤ) (j : I) : v j * v j ≤ v ⬝ᵥ v :=
  Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg (v i))
    (Finset.mem_univ j)

theorem eq_single_of_mul_self_eq (v : I → ℤ) (j : I) (h : v j * v j = v ⬝ᵥ v) :
    v = Pi.single j (v j) := by
  have hsum : ∑ i ∈ Finset.univ.erase j, v i * v i = 0 := by
    have e := Finset.add_sum_erase Finset.univ (fun i => v i * v i) (Finset.mem_univ j)
    change v j * v j + ∑ i ∈ Finset.univ.erase j, v i * v i = v ⬝ᵥ v at e
    linarith
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Pi.single_eq_of_ne hij]
    exact mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (v i))).mp hsum i (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩))

theorem degree_single_ne_zero {d : I → ℝ} (hd : ∀ i, 0 < d i) (j : I) {x : ℤ} (hx : x ≠ 0) :
    degree d (Pi.single j x) ≠ 0 := by
  rw [degree_single]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hx) (hd j).ne'

theorem entry_of_norm_four {d : I → ℝ} (hd : ∀ i, 0 < d i) {v : I → ℤ} (hv : v ⬝ᵥ v = 4)
    (hvd : degree d v = 0) (j : I) : v j = -1 ∨ v j = 0 ∨ v j = 1 := by
  have hle := mul_self_le_dotProduct_self v j
  rw [hv] at hle
  have hne : v j * v j ≠ 4 := by
    intro h4
    have hs := eq_single_of_mul_self_eq v j (by rw [h4, hv])
    have hvj : v j ≠ 0 := by
      intro h0
      rw [h0] at h4
      norm_num at h4
    exact degree_single_ne_zero hd j hvj (hs ▸ hvd)
  have h2 : v j ≠ 2 := fun h => hne (by rw [h]; norm_num)
  have hm2 : v j ≠ -2 := fun h => hne (by rw [h]; norm_num)
  have hb : -2 ≤ v j ∧ v j ≤ 2 := by constructor <;> nlinarith
  omega

omit [DecidableEq I] in
theorem entry_of_norm_le_three {v : I → ℤ} (hv : v ⬝ᵥ v ≤ 3) (j : I) :
    v j = -1 ∨ v j = 0 ∨ v j = 1 := by
  have hle := mul_self_le_dotProduct_self v j
  have hb : -1 ≤ v j ∧ v j ≤ 1 := by constructor <;> nlinarith
  omega

omit [DecidableEq I] in
theorem dotProduct_self_eq_card {v : I → ℤ} (hv : ∀ j, v j = -1 ∨ v j = 0 ∨ v j = 1) :
    v ⬝ᵥ v = ((Finset.univ.filter fun j => v j ≠ 0).card : ℤ) := by
  rw [dotProduct, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases hv j with h | h | h <;> simp [h]

theorem eq_sum_single_support (v : I → ℤ) :
    v = ∑ t ∈ Finset.univ.filter (fun j => v j ≠ 0), Pi.single t (v t) := by
  funext j
  rw [Finset.sum_apply, Finset.sum_pi_single]
  by_cases hj : v j = 0 <;> simp [hj]

theorem exists_four_units {v : I → ℤ} (hv1 : ∀ j, v j = -1 ∨ v j = 0 ∨ v j = 1)
    (hv : v ⬝ᵥ v = 4) :
    ∃ T : Finset I, T.card = 4 ∧ (∀ t ∈ T, v t = 1 ∨ v t = -1) ∧
      v = ∑ t ∈ T, Pi.single t (v t) := by
  refine ⟨Finset.univ.filter fun j => v j ≠ 0, ?_, ?_, eq_sum_single_support v⟩
  · have h := dotProduct_self_eq_card hv1
    rw [hv] at h
    exact_mod_cast h.symm
  · intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    rcases hv1 t with h | h | h
    · exact Or.inr h
    · exact absurd h ht'
    · exact Or.inl h

theorem exists_two_units {v : I → ℤ} (hv : v ⬝ᵥ v = 2) :
    ∃ a b, a ≠ b ∧ (v a = 1 ∨ v a = -1) ∧ (v b = 1 ∨ v b = -1) ∧
      v = Pi.single a (v a) + Pi.single b (v b) := by
  have hv1 : ∀ j, v j = -1 ∨ v j = 0 ∨ v j = 1 := entry_of_norm_le_three (by rw [hv]; norm_num)
  have hT : (Finset.univ.filter fun j => v j ≠ 0).card = 2 := by
    have h := dotProduct_self_eq_card hv1
    rw [hv] at h
    exact_mod_cast h.symm
  obtain ⟨a, b, hab, hTab⟩ := Finset.card_eq_two.mp hT
  have hunit : ∀ t, t ∈ Finset.univ.filter (fun j => v j ≠ 0) → v t = 1 ∨ v t = -1 := by
    intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    rcases hv1 t with h | h | h
    · exact Or.inr h
    · exact absurd h ht'
    · exact Or.inl h
  refine ⟨a, b, hab, hunit a (by rw [hTab]; simp), hunit b (by rw [hTab]; simp), ?_⟩
  conv_lhs => rw [eq_sum_single_support v, hTab]
  rw [Finset.sum_pair hab]

theorem exists_double_of_even {w : I → ℤ} (hw : ∀ j, Even (w j)) (hn : w ⬝ᵥ w = 4) :
    ∃ p β, (β = 1 ∨ β = -1) ∧ w = Pi.single p (2 * β) := by
  have hne : ∃ p, w p ≠ 0 := by
    by_contra h
    push Not at h
    have : w = 0 := funext h
    rw [this] at hn
    simp at hn
  obtain ⟨p, hp⟩ := hne
  have hle := mul_self_le_dotProduct_self w p
  rw [hn] at hle
  obtain ⟨m, hm⟩ := hw p
  have hm0 : m ≠ 0 := by
    intro h
    apply hp
    rw [hm, h]
    ring
  have hm1 : m = 1 ∨ m = -1 := by
    rw [hm] at hle
    have hmm : m * m ≤ 1 := by nlinarith
    have hb : -1 ≤ m ∧ m ≤ 1 := by constructor <;> nlinarith
    omega
  have hsq : w p * w p = 4 := by
    rw [hm]
    rcases hm1 with h | h <;> rw [h] <;> norm_num
  have hs := eq_single_of_mul_self_eq w p (by rw [hsq, hn])
  refine ⟨p, m, hm1, ?_⟩
  rw [hs, hm, two_mul]

theorem disjoint_of_norm_two {d : I → ℝ} (hd : ∀ i, 0 < d i) {P Q : I → ℤ}
    (hP : P ⬝ᵥ P = 2) (hQ : Q ⬝ᵥ Q = 2) (hPQ : P ⬝ᵥ Q = 0) (hdeg : degree d P = degree d Q) :
    ∀ j, P j * Q j = 0 := by
  have hD : (P - Q) ⬝ᵥ (P - Q) = 4 := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm Q P]
    linarith
  have hDd : degree d (P - Q) = 0 := by rw [map_sub, hdeg, sub_self]
  have hent := entry_of_norm_four hd hD hDd
  have hP1 := entry_of_norm_le_three (v := P) (by rw [hP]; norm_num)
  have hQ1 := entry_of_norm_le_three (v := Q) (by rw [hQ]; norm_num)
  intro j
  by_contra hj
  have hPj : P j ≠ 0 := left_ne_zero_of_mul hj
  have hQj : Q j ≠ 0 := right_ne_zero_of_mul hj
  have hej := hent j
  simp only [Pi.sub_apply] at hej
  have heq : P j = Q j := by
    rcases hP1 j with h | h | h <;> rcases hQ1 j with h' | h' | h' <;> omega
  have hS : (P + Q) ⬝ᵥ (P + Q) = 4 := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm Q P]
    linarith
  have hSj : (P + Q) j * (P + Q) j = 4 := by
    rw [Pi.add_apply, heq]
    rcases hQ1 j with h | h | h
    · rw [h]; norm_num
    · exact absurd h hQj
    · rw [h]; norm_num
  have hs := eq_single_of_mul_self_eq (P + Q) j (by rw [hSj, hS])
  have hPi : ∀ i, i ≠ j → P i = 0 := by
    intro i hij
    have h1 : P i + Q i = 0 := by
      have := congrFun hs i
      simpa [Pi.single_eq_of_ne hij] using this
    have h2 := hent i
    simp only [Pi.sub_apply] at h2
    omega
  have hPP : P ⬝ᵥ P = P j * P j := by
    rw [dotProduct, Finset.sum_eq_single j]
    · intro i _ hij
      rw [hPi i hij, zero_mul]
    · simp
  rw [hP] at hPP
  rcases hP1 j with h | h | h <;> rw [h] at hPP <;> norm_num at hPP

theorem sum_single_dotProduct (T : Finset I) (f w : I → ℤ) :
    (∑ t ∈ T, Pi.single t (f t)) ⬝ᵥ w = ∑ t ∈ T, f t * w t := by
  rw [sum_dotProduct]
  exact Finset.sum_congr rfl fun t _ => single_dotProduct _ _ _

omit [Fintype I] in
theorem sum_single_apply (T : Finset I) (f : I → ℤ) (j : I) :
    (∑ t ∈ T, Pi.single t (f t)) j = if j ∈ T then f j else 0 := by
  rw [Finset.sum_apply, Finset.sum_pi_single]

theorem degree_sum_single (d : I → ℝ) (T : Finset I) (f : I → ℤ) :
    degree d (∑ t ∈ T, Pi.single t (f t)) = ∑ t ∈ T, (f t : ℝ) * d t := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun t _ => degree_single d t (f t)

omit [DecidableEq I] in
theorem odd_of_modEq_unit {x y : ℤ} (h : x ≡ y [ZMOD 2]) (hy : y = 1 ∨ y = -1) : Odd x := by
  rw [Int.odd_iff]
  unfold Int.ModEq at h
  rcases hy with rfl | rfl <;> omega

omit [DecidableEq I] in
theorem even_of_modEq_zero {x : ℤ} (h : x ≡ 0 [ZMOD 2]) : Even x := by
  rw [Int.even_iff]
  unfold Int.ModEq at h
  omega

theorem exists_core_double {T : Finset I} (hT : T.card = 4) {Ys : I → ℤ}
    (hYsT : ∀ t ∈ T, Ys t = 1 ∨ Ys t = -1) (hYs : Ys = ∑ t ∈ T, Pi.single t (Ys t))
    {v : I → ℤ} (hpar : ∀ i, v i ≡ Ys i [ZMOD 2]) (hv : v ⬝ᵥ v = 8) :
    (∀ t ∈ T, v t = 1 ∨ v t = -1) ∧ ∃ p β, p ∉ T ∧ (β = 1 ∨ β = -1) ∧
      v = ∑ t ∈ T, Pi.single t (v t) + Pi.single p (2 * β) := by
  have hYs0 : ∀ i, i ∉ T → Ys i = 0 := by
    intro i hi
    rw [hYs, sum_single_apply]
    simp [hi]
  have hodd : ∀ t ∈ T, Odd (v t) := fun t ht => odd_of_modEq_unit (hpar t) (hYsT t ht)
  have heven : ∀ i, i ∉ T → Even (v i) := fun i hi =>
    even_of_modEq_zero (by rw [← hYs0 i hi]; exact hpar i)
  have hsplit : ∑ t ∈ T, v t * v t + ∑ i ∈ Tᶜ, v i * v i = 8 := by
    rw [Finset.sum_add_sum_compl]
    exact hv
  have hge : ∀ t ∈ T, 1 ≤ v t * v t := by
    intro t ht
    obtain ⟨m, hm⟩ := hodd t ht
    rw [hm]
    rcases le_or_gt 0 m with h | h <;> nlinarith
  have hrest : 0 ≤ ∑ i ∈ Tᶜ, v i * v i := Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hcore1 : ∀ t ∈ T, v t = 1 ∨ v t = -1 := by
    intro t ht
    have h3 : 3 ≤ ∑ s ∈ T.erase t, v s * v s := by
      have hc : (T.erase t).card = 3 := by rw [Finset.card_erase_of_mem ht, hT]
      calc (3 : ℤ) = ∑ s ∈ T.erase t, (1 : ℤ) := by rw [Finset.sum_const, hc]; norm_num
        _ ≤ ∑ s ∈ T.erase t, v s * v s :=
          Finset.sum_le_sum fun s hs => hge s (Finset.mem_of_mem_erase hs)
    have h2 := Finset.add_sum_erase T (fun s => v s * v s) ht
    have hle : v t * v t ≤ 5 := by linarith
    obtain ⟨m, hm⟩ := hodd t ht
    rw [hm] at hle ⊢
    have hb : -1 ≤ m ∧ m ≤ 0 := by constructor <;> nlinarith
    omega
  have hcore : ∑ t ∈ T, v t * v t = 4 := by
    rw [Finset.sum_congr rfl fun t ht => (by rcases hcore1 t ht with h | h <;> rw [h] <;> norm_num :
      v t * v t = 1), Finset.sum_const, hT]
    norm_num
  set w : I → ℤ := fun i => if i ∈ T then 0 else v i with hw
  have hw_even : ∀ i, Even (w i) := by
    intro i
    by_cases hi : i ∈ T
    · simp [hw, hi]
    · simp only [hw, hi, ↓reduceIte]
      exact heven i hi
  have hw_norm : w ⬝ᵥ w = 4 := by
    rw [dotProduct, ← Finset.sum_add_sum_compl T]
    have h1 : ∑ i ∈ T, w i * w i = 0 := Finset.sum_eq_zero fun i hi => by simp [hw, hi]
    have h2 : ∑ i ∈ Tᶜ, w i * w i = ∑ i ∈ Tᶜ, v i * v i := Finset.sum_congr rfl fun i hi => by
      simp [hw, Finset.mem_compl.mp hi]
    rw [h1, h2]
    linarith
  obtain ⟨p, β, hβ, hwp⟩ := exists_double_of_even hw_even hw_norm
  have hpT : p ∉ T := by
    intro hp
    have h := congrFun hwp p
    simp only [hw, hp, ↓reduceIte, Pi.single_eq_same] at h
    rcases hβ with rfl | rfl <;> norm_num at h
  refine ⟨hcore1, p, β, hpT, hβ, ?_⟩
  funext i
  rw [Pi.add_apply, sum_single_apply, ← congrFun hwp i]
  by_cases hi : i ∈ T <;> simp [hw, hi]

theorem double_ne_of_dotProduct_eq_zero {d : I → ℝ} (hd : ∀ i, 0 < d i) {T : Finset I}
    (hT : T.card = 4) {X C : I → ℤ} (hXT : ∀ t ∈ T, X t = 1 ∨ X t = -1)
    (hCT : ∀ t ∈ T, C t = 1 ∨ C t = -1) {p i₄ : I} {α δ₄ : ℤ} (hp : p ∉ T)
    (hα : α = 1 ∨ α = -1) (hδ₄ : δ₄ = 1 ∨ δ₄ = -1)
    (hX : X = ∑ t ∈ T, Pi.single t (X t) + Pi.single p (2 * α))
    (hC : C = ∑ t ∈ T, Pi.single t (C t) + Pi.single i₄ (2 * δ₄))
    (hCX : C ⬝ᵥ X = 0) (hXd : degree d X = 0) (hCd : degree d C = 0) : p ≠ i₄ := by
  intro hpi
  subst hpi
  have hXp : X p = 2 * α := by
    conv_lhs => rw [hX]
    rw [Pi.add_apply, sum_single_apply, Pi.single_eq_same]
    simp [hp]
  have hCp : C p = 2 * δ₄ := by
    conv_lhs => rw [hC]
    rw [Pi.add_apply, sum_single_apply, Pi.single_eq_same]
    simp [hp]
  have hcx : ∑ t ∈ T, C t * X t = -(4 * (δ₄ * α)) := by
    have h := hCX
    rw [hC, add_dotProduct, sum_single_dotProduct, single_dotProduct, hXp] at h
    linarith
  set σ := δ₄ * α with hσ
  have hσ1 : σ * σ = 1 := by
    rcases hα with rfl | rfl <;> rcases hδ₄ with rfl | rfl <;> norm_num [hσ]
  have hterm : ∀ t ∈ T, C t * X t * σ + 1 = 0 := by
    have hnn : ∀ t ∈ T, 0 ≤ C t * X t * σ + 1 := by
      intro t ht
      rcases hXT t ht with h1 | h1 <;> rcases hCT t ht with h2 | h2 <;>
        rcases hα with h3 | h3 <;> rcases hδ₄ with h4 | h4 <;> simp [hσ, h1, h2, h3, h4]
    have hsum : ∑ t ∈ T, (C t * X t * σ + 1) = 0 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hcx, Finset.sum_const, hT]
      linear_combination (-4 : ℤ) * hσ1
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  have hvec : C + σ • X = Pi.single p (4 * δ₄) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j ∈ T
    · have hjp : j ≠ p := fun h => hp (h ▸ hj)
      rw [Pi.single_eq_of_ne hjp]
      have h := hterm j hj
      have hX2 : X j * X j = 1 := by rcases hXT j hj with h1 | h1 <;> rw [h1] <;> norm_num
      linear_combination (X j * σ) * h - (C j * σ * σ) * hX2 - C j * hσ1
    · by_cases hjp : j = p
      · subst hjp
        rw [hCp, hXp, Pi.single_eq_same, hσ]
        rcases hα with rfl | rfl <;> ring
      · rw [Pi.single_eq_of_ne hjp]
        have hCj : C j = 0 := by
          rw [hC, Pi.add_apply, sum_single_apply, Pi.single_eq_of_ne hjp]
          simp [hj]
        have hXj : X j = 0 := by
          rw [hX, Pi.add_apply, sum_single_apply, Pi.single_eq_of_ne hjp]
          simp [hj]
        rw [hCj, hXj]
        ring
  have hδ0 : 4 * δ₄ ≠ 0 := by rcases hδ₄ with rfl | rfl <;> norm_num
  have h := degree_single_ne_zero hd p hδ0
  rw [← hvec, map_add, map_zsmul, hCd, hXd, smul_zero, add_zero] at h
  exact h rfl

omit [Fintype I] [DecidableEq I] in
theorem exists_sign_pattern {T : Finset I} (hT : T.card = 4) {y c : I → ℤ}
    (hy : ∀ t ∈ T, y t = 1 ∨ y t = -1) (hc : ∀ t ∈ T, c t = 1 ∨ c t = -1)
    (hy0 : ∑ t ∈ T, y t = 0) (hc0 : ∑ t ∈ T, c t = 0) (hyc : ∑ t ∈ T, y t * c t = 0)
    {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) : ∃ t ∈ T, y t = a ∧ c t = b := by
  by_contra hne
  push Not at hne
  have hzero : ∀ t ∈ T, (1 + a * y t) * (1 + b * c t) = 0 := by
    intro t ht
    have h := hne t ht
    rcases hy t ht with h1 | h1 <;> rcases hc t ht with h2 | h2 <;> rcases ha with rfl | rfl <;>
      rcases hb with rfl | rfl <;> simp_all
  have hsum : ∑ t ∈ T, (1 + a * y t) * (1 + b * c t) = 4 := by
    have e : ∀ t, (1 + a * y t) * (1 + b * c t) =
        1 + a * y t + b * c t + (a * b) * (y t * c t) := fun t => by ring
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hy0, hc0, hyc, Finset.sum_const, hT]
    simp
  rw [Finset.sum_eq_zero hzero] at hsum
  norm_num at hsum

omit [Fintype I] in
theorem sum_four {M : Type*} [AddCommMonoid M] (f : I → M) {a b c e : I} (hab : a ≠ b)
    (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    ∑ t ∈ ({a, b, c, e} : Finset I), f t = f a + f b + f c + f e := by
  rw [Finset.sum_insert (by simp [hab, hac, hae]), Finset.sum_insert (by simp [hbc, hbe]),
    Finset.sum_pair hce]
  abel

omit [Fintype I] in
theorem exists_relabel {T : Finset I} (hT : T.card = 4) {y c : I → ℤ}
    (hy : ∀ t ∈ T, y t = 1 ∨ y t = -1) (hc : ∀ t ∈ T, c t = 1 ∨ c t = -1)
    (hy0 : ∑ t ∈ T, y t = 0) (hc0 : ∑ t ∈ T, c t = 0) (hyc : ∑ t ∈ T, y t * c t = 0) :
    ∃ i₀ i₁ i₂ i₃ : I, i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₀ ≠ i₃ ∧ i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧
      T = {i₀, i₁, i₂, i₃} ∧ y i₀ = 1 ∧ c i₀ = 1 ∧ y i₁ = 1 ∧ c i₁ = -1 ∧ y i₂ = -1 ∧
      c i₂ = 1 ∧ y i₃ = -1 ∧ c i₃ = -1 := by
  obtain ⟨i₀, h0, y0, c0⟩ := exists_sign_pattern hT hy hc hy0 hc0 hyc (Or.inl rfl) (Or.inl rfl)
  obtain ⟨i₁, h1, y1, c1⟩ := exists_sign_pattern hT hy hc hy0 hc0 hyc (Or.inl rfl) (Or.inr rfl)
  obtain ⟨i₂, h2, y2, c2⟩ := exists_sign_pattern hT hy hc hy0 hc0 hyc (Or.inr rfl) (Or.inl rfl)
  obtain ⟨i₃, h3, y3, c3⟩ := exists_sign_pattern hT hy hc hy0 hc0 hyc (Or.inr rfl) (Or.inr rfl)
  have h01 : i₀ ≠ i₁ := fun h => by rw [h, c1] at c0; norm_num at c0
  have h02 : i₀ ≠ i₂ := fun h => by rw [h, y2] at y0; norm_num at y0
  have h03 : i₀ ≠ i₃ := fun h => by rw [h, y3] at y0; norm_num at y0
  have h12 : i₁ ≠ i₂ := fun h => by rw [h, y2] at y1; norm_num at y1
  have h13 : i₁ ≠ i₃ := fun h => by rw [h, y3] at y1; norm_num at y1
  have h23 : i₂ ≠ i₃ := fun h => by rw [h, c3] at c2; norm_num at c2
  refine ⟨i₀, i₁, i₂, i₃, h01, h02, h03, h12, h13, h23, ?_, y0, c0, y1, c1, y2, c2, y3, c3⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> assumption
  · rw [hT, Finset.card_insert_of_notMem (by simp [h01, h02, h03]),
      Finset.card_insert_of_notMem (by simp [h12, h13]), Finset.card_pair h23]

theorem dotProduct_split (l : List I) (hl : l.Nodup) (v w : I → ℤ) :
    v ⬝ᵥ w = (l.map fun s => v s * w s).sum + ∑ j ∈ l.toFinsetᶜ, v j * w j := by
  rw [dotProduct, ← Finset.sum_add_sum_compl l.toFinset, List.sum_toFinset _ hl]

omit [Fintype I] [DecidableEq I] in
theorem eq_zero_of_sum_mul_self_eq_zero {S : Finset I} {v : I → ℤ}
    (h : ∑ j ∈ S, v j * v j = 0) {j : I} (hj : j ∈ S) : v j = 0 :=
  mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).mp h j hj)

omit [Fintype I] [DecidableEq I] in
theorem sum_mul_self_nonneg (S : Finset I) (v : I → ℤ) : 0 ≤ ∑ j ∈ S, v j * v j :=
  Finset.sum_nonneg fun j _ => mul_self_nonneg (v j)

omit [Fintype I] [DecidableEq I] in
theorem unit_cases_of_mul_self_le {x : ℤ} (h : x * x ≤ 3) : x = -1 ∨ x = 0 ∨ x = 1 := by
  have h1 : -1 ≤ x := by nlinarith
  have h2 : x ≤ 1 := by nlinarith
  omega

omit [Fintype I] [DecidableEq I] in
theorem three_unit_coords {a₀ a₁ a₂ a₃ b c R : ℤ} (hR : 0 ≤ R)
    (hY : a₀ + a₁ - a₂ - a₃ = 0) (hC : a₀ - a₁ + a₂ - a₃ + 2 * b = 0)
    (hX : a₀ + a₁ + a₂ + a₃ + 2 * c = -2)
    (hN : a₀ * a₀ + a₁ * a₁ + a₂ * a₂ + a₃ * a₃ + b * b + c * c + R = 3) :
    (a₀ = -1 ∧ a₁ = 0 ∧ a₂ = -1 ∧ a₃ = 0 ∧ b = 1 ∧ c = 0 ∧ R = 0) ∨
    (a₀ = -1 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = -1 ∧ b = 0 ∧ c = 0 ∧ R = 1) ∨
    (a₀ = 0 ∧ a₁ = -1 ∧ a₂ = -1 ∧ a₃ = 0 ∧ b = 0 ∧ c = 0 ∧ R = 1) ∨
    (a₀ = 0 ∧ a₁ = -1 ∧ a₂ = 0 ∧ a₃ = -1 ∧ b = -1 ∧ c = 0 ∧ R = 0) ∨
    (a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 ∧ b = 0 ∧ c = -1 ∧ R = 2) := by
  have s0 := mul_self_nonneg a₀
  have s1 := mul_self_nonneg a₁
  have s2 := mul_self_nonneg a₂
  have s3 := mul_self_nonneg a₃
  have s4 := mul_self_nonneg b
  have s5 := mul_self_nonneg c
  have e0 := unit_cases_of_mul_self_le (x := a₀) (by linarith)
  have e1 := unit_cases_of_mul_self_le (x := a₁) (by linarith)
  have e2 := unit_cases_of_mul_self_le (x := a₂) (by linarith)
  obtain rfl : a₃ = a₀ + a₁ - a₂ := by omega
  obtain rfl : b = a₁ - a₂ := by omega
  obtain rfl : c = -1 - a₀ - a₁ := by omega
  rcases e0 with rfl | rfl | rfl <;> rcases e1 with rfl | rfl | rfl <;>
    rcases e2 with rfl | rfl | rfl <;> norm_num at hN ⊢ <;> omega

omit [Fintype I] [DecidableEq I] in
theorem exists_half {v : I → ℤ} (hv : ∀ i, v i ≡ 0 [ZMOD 2]) :
    ∃ m : I → ℤ, (2 : ℤ) • m = v := by
  refine ⟨fun i => v i / 2, funext fun i => ?_⟩
  have h := hv i
  unfold Int.ModEq at h
  simp only [Pi.smul_apply, smul_eq_mul]
  omega

omit [DecidableEq I] in
theorem two_mul_dotProduct_of_smul_eq {M v : I → ℤ} (hM : (2 : ℤ) • M = v) (w : I → ℤ) :
    2 * (w ⬝ᵥ M) = w ⬝ᵥ v := by
  rw [← hM, dotProduct_smul, smul_eq_mul]

omit [DecidableEq I] in
theorem two_mul_degree_of_smul_eq (d : I → ℝ) {M v : I → ℤ} (hM : (2 : ℤ) • M = v) :
    2 * degree d M = degree d v := by
  rw [← hM, map_zsmul]
  simp

theorem degree_eq_of_vanish (d : I → ℝ) (l : List I) (hl : l.Nodup) {v : I → ℤ}
    (hv : ∀ j, j ∉ l → v j = 0) : degree d v = (l.map fun s => (v s : ℝ) * d s).sum := by
  rw [degree_apply, ← Finset.sum_add_sum_compl l.toFinset, List.sum_toFinset _ hl]
  have h0 : ∑ j ∈ l.toFinsetᶜ, (v j : ℝ) * d j = 0 := Finset.sum_eq_zero fun j hj => by
    rw [hv j (by simpa using hj)]
    simp
  rw [h0, add_zero]

theorem dotProduct_eq_of_vanish (l : List I) (hl : l.Nodup) {v : I → ℤ}
    (hv : ∀ j, j ∉ l → v j = 0) (w : I → ℤ) : v ⬝ᵥ w = (l.map fun s => v s * w s).sum := by
  rw [dotProduct_split l hl]
  have h0 : ∑ j ∈ l.toFinsetᶜ, v j * w j = 0 := Finset.sum_eq_zero fun j hj => by
    rw [hv j (by simpa using hj), zero_mul]
  rw [h0, add_zero]

omit [Fintype I] [DecidableEq I] in
theorem eq_mul_of_sign {δ x a : ℤ} (hδ : δ * δ = 1) (h : δ * x = a) : x = δ * a := by
  linear_combination δ * h - x * hδ

@[expose] def FrameShape (i₀ i₁ i₂ i₃ i₄ p : I) (δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ) (M : I → ℤ) : Prop :=
  (M i₀ = -δ₀ ∧ M i₁ = 0 ∧ M i₂ = -δ₂ ∧ M i₃ = 0 ∧ M i₄ = δ₄ ∧ M p = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 0) ∨
    (M i₀ = -δ₀ ∧ M i₁ = 0 ∧ M i₂ = 0 ∧ M i₃ = -δ₃ ∧ M i₄ = 0 ∧ M p = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 1) ∨
    (M i₀ = 0 ∧ M i₁ = -δ₁ ∧ M i₂ = -δ₂ ∧ M i₃ = 0 ∧ M i₄ = 0 ∧ M p = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 1) ∨
    (M i₀ = 0 ∧ M i₁ = -δ₁ ∧ M i₂ = 0 ∧ M i₃ = -δ₃ ∧ M i₄ = -δ₄ ∧ M p = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 0) ∨
    (M i₀ = 0 ∧ M i₁ = 0 ∧ M i₂ = 0 ∧ M i₃ = 0 ∧ M i₄ = 0 ∧ M p = -α ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 2)

theorem frame_types {i₀ i₁ i₂ i₃ i₄ p : I} (hl : [i₀, i₁, i₂, i₃, i₄, p].Nodup)
    {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ} (h₀ : δ₀ * δ₀ = 1) (h₁ : δ₁ * δ₁ = 1) (h₂ : δ₂ * δ₂ = 1)
    (h₃ : δ₃ * δ₃ = 1) (h₄ : δ₄ * δ₄ = 1) (hα : α * α = 1) {M : I → ℤ}
    (hY : δ₀ * M i₀ + δ₁ * M i₁ - δ₂ * M i₂ - δ₃ * M i₃ = 0)
    (hC : δ₀ * M i₀ - δ₁ * M i₁ + δ₂ * M i₂ - δ₃ * M i₃ + 2 * δ₄ * M i₄ = 0)
    (hX : δ₀ * M i₀ + δ₁ * M i₁ + δ₂ * M i₂ + δ₃ * M i₃ + 2 * α * M p = -2)
    (hN : M ⬝ᵥ M = 3) : FrameShape i₀ i₁ i₂ i₃ i₄ p δ₀ δ₁ δ₂ δ₃ δ₄ α M := by
  have hsplit := dotProduct_split _ hl M M
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsplit
  set R := ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j with hR
  have hRn : 0 ≤ R := sum_mul_self_nonneg _ M
  have sq : ∀ {δ x : ℤ}, δ * δ = 1 → (δ * x) * (δ * x) = x * x := fun {δ x} h => by
    linear_combination (x * x) * h
  have hN' : (δ₀ * M i₀) * (δ₀ * M i₀) + (δ₁ * M i₁) * (δ₁ * M i₁) + (δ₂ * M i₂) * (δ₂ * M i₂) +
      (δ₃ * M i₃) * (δ₃ * M i₃) + (δ₄ * M i₄) * (δ₄ * M i₄) + (α * M p) * (α * M p) + R = 3 := by
    rw [sq h₀, sq h₁, sq h₂, sq h₃, sq h₄, sq hα]
    linarith
  have hC' : δ₀ * M i₀ - δ₁ * M i₁ + δ₂ * M i₂ - δ₃ * M i₃ + 2 * (δ₄ * M i₄) = 0 := by
    linarith
  have hX' : δ₀ * M i₀ + δ₁ * M i₁ + δ₂ * M i₂ + δ₃ * M i₃ + 2 * (α * M p) = -2 := by linarith
  rcases three_unit_coords hRn hY hC' hX' hN' with
      ⟨e0, e1, e2, e3, e4, e5, e6⟩ | ⟨e0, e1, e2, e3, e4, e5, e6⟩ | ⟨e0, e1, e2, e3, e4, e5, e6⟩ |
      ⟨e0, e1, e2, e3, e4, e5, e6⟩ | ⟨e0, e1, e2, e3, e4, e5, e6⟩ <;>
    have f0 := eq_mul_of_sign h₀ e0 <;> have f1 := eq_mul_of_sign h₁ e1 <;>
    have f2 := eq_mul_of_sign h₂ e2 <;> have f3 := eq_mul_of_sign h₃ e3 <;>
    have f4 := eq_mul_of_sign h₄ e4 <;> have f5 := eq_mul_of_sign hα e5 <;>
    simp only [mul_neg, mul_one, mul_zero] at f0 f1 f2 f3 f4 f5
  · exact Or.inl ⟨f0, f1, f2, f3, f4, f5, e6⟩
  · exact Or.inr (Or.inl ⟨f0, f1, f2, f3, f4, f5, e6⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f0, f1, f2, f3, f4, f5, e6⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f0, f1, f2, f3, f4, f5, e6⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f0, f1, f2, f3, f4, f5, e6⟩)))

omit [Fintype I] [DecidableEq I] in
theorem eq_mul_of_mul_eq {a x s : ℤ} (hx : x * x = 1) (h : a * x = s) : a = s * x := by
  linear_combination x * h - a * hx

omit [Fintype I] [DecidableEq I] in
theorem mul_self_of_sign {x : ℤ} (hx : x = 1 ∨ x = -1) : x * x = 1 := by
  rcases hx with rfl | rfl <;> norm_num

omit [Fintype I] [DecidableEq I] in
theorem sign_mul {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

theorem vanish_of_rest_eq_zero {l : List I} {v : I → ℤ}
    (h : ∑ j ∈ l.toFinsetᶜ, v j * v j = 0) : ∀ j, j ∉ l → v j = 0 := fun j hj =>
  eq_zero_of_sum_mul_self_eq_zero h (by simpa using hj)

theorem core_eq_of_frame {i₀ i₁ i₂ i₃ i₄ p p' : I} (hl : [i₀, i₁, i₂, i₃, i₄, p].Nodup)
    (h0p : i₀ ≠ p) (h1p : i₁ ≠ p) (h2p : i₂ ≠ p) (h3p : i₃ ≠ p)
    {δ₀ δ₁ δ₂ δ₃ δ₄ α β : ℤ} (hδ₀ : δ₀ = 1 ∨ δ₀ = -1) (hδ₁ : δ₁ = 1 ∨ δ₁ = -1)
    (hδ₂ : δ₂ = 1 ∨ δ₂ = -1) (hδ₃ : δ₃ = 1 ∨ δ₃ = -1) (hδ₄ : δ₄ = 1 ∨ δ₄ = -1)
    (hα : α = 1 ∨ α = -1) (hβ : β = 1 ∨ β = -1) {v : I → ℤ}
    (hv : v = Pi.single i₀ (v i₀) + Pi.single i₁ (v i₁) + Pi.single i₂ (v i₂) +
      Pi.single i₃ (v i₃) + Pi.single p' (2 * β))
    (hv0 : v i₀ = 1 ∨ v i₀ = -1) (hv1 : v i₁ = 1 ∨ v i₁ = -1) (hv2 : v i₂ = 1 ∨ v i₂ = -1)
    (hv3 : v i₃ = 1 ∨ v i₃ = -1)
    (eY : δ₀ * v i₀ + δ₁ * v i₁ - δ₂ * v i₂ - δ₃ * v i₃ = 0)
    (eC : δ₀ * v i₀ - δ₁ * v i₁ + δ₂ * v i₂ - δ₃ * v i₃ = 0)
    (eX : δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ + 2 * α * v p = 4)
    {Mp Mm : I → ℤ} (hMp : FrameShape i₀ i₁ i₂ i₃ i₄ p δ₀ δ₁ δ₂ δ₃ δ₄ α Mp)
    (hMm : FrameShape i₀ i₁ i₂ i₃ i₄ p δ₀ δ₁ δ₂ δ₃ δ₄ α Mm)
    (hvMp : v ⬝ᵥ Mp = 0) (hvMm : v ⬝ᵥ Mm = 0) (hpm : Mp ⬝ᵥ Mm = 1) :
    v i₀ = δ₀ ∧ v i₁ = δ₁ ∧ v i₂ = δ₂ ∧ v i₃ = δ₃ ∧ p' ≠ p := by
  have sδ₀ := mul_self_of_sign hδ₀
  have sδ₁ := mul_self_of_sign hδ₁
  have sδ₂ := mul_self_of_sign hδ₂
  have sδ₃ := mul_self_of_sign hδ₃
  have sδ₄ := mul_self_of_sign hδ₄
  have u0 := sign_mul hδ₀ hv0
  have u1 := sign_mul hδ₁ hv1
  have u2 := sign_mul hδ₂ hv2
  have u3 := sign_mul hδ₃ hv3
  have hvp : v p = if p' = p then 2 * β else 0 := by
    conv_lhs => rw [hv]
    simp only [Pi.add_apply, Pi.single_apply, ite_eq_right h0p.symm, ite_eq_right h1p.symm,
      ite_eq_right h2p.symm, ite_eq_right h3p.symm, zero_add]
    by_cases hpp : p' = p
    · simp [hpp]
    · simp [hpp, Ne.symm hpp]
  by_cases hpp : p' = p
  · exfalso
    rw [hvp, ite_eq_left hpp] at eX
    have hαβ1 := sign_mul hα hβ
    have hsig : α * β = 1 ∧ δ₀ * v i₀ = δ₃ * v i₃ ∧ δ₁ * v i₁ = δ₂ * v i₂ ∧
        δ₁ * v i₁ = -(δ₀ * v i₀) := by
      have e2 : δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ + 4 * (α * β) = 4 := by linarith
      omega
    obtain ⟨hαβ, t03, t12, t01⟩ := hsig
    have cv : ∀ w : I → ℤ, v ⬝ᵥ w = v i₀ * w i₀ + v i₁ * w i₁ + v i₂ * w i₂ + v i₃ * w i₃ +
        2 * β * w p := fun w => by
      conv_lhs => rw [hv]
      simp only [add_dotProduct, single_dotProduct, hpp]
    have hT14 : ∀ M : I → ℤ, v ⬝ᵥ M = 0 → FrameShape i₀ i₁ i₂ i₃ i₄ p δ₀ δ₁ δ₂ δ₃ δ₄ α M →
        (M i₀ = -δ₀ ∧ M i₁ = 0 ∧ M i₂ = -δ₂ ∧ M i₃ = 0 ∧ M i₄ = δ₄ ∧ M p = 0 ∧
          ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 0) ∨
        (M i₀ = 0 ∧ M i₁ = -δ₁ ∧ M i₂ = 0 ∧ M i₃ = -δ₃ ∧ M i₄ = -δ₄ ∧ M p = 0 ∧
          ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j = 0) := by
      intro M hvM hty
      rw [cv] at hvM
      rcases hty with hM | ⟨m0, m1, m2, m3, -, m5, -⟩ | ⟨m0, m1, m2, m3, -, m5, -⟩ | hM |
          ⟨m0, m1, m2, m3, -, m5, -⟩
      · exact Or.inl hM
      · rw [m0, m1, m2, m3, m5] at hvM
        have : δ₀ * v i₀ + δ₃ * v i₃ = 0 := by linear_combination -hvM
        omega
      · rw [m0, m1, m2, m3, m5] at hvM
        have : δ₁ * v i₁ + δ₂ * v i₂ = 0 := by linear_combination -hvM
        omega
      · exact Or.inr hM
      · rw [m0, m1, m2, m3, m5] at hvM
        have : 2 * (α * β) = 0 := by linear_combination -hvM
        omega
    rcases hT14 Mp hvMp hMp with ⟨p0, p1, p2, p3, p4, p5, pR⟩ | ⟨p0, p1, p2, p3, p4, p5, pR⟩ <;>
      rcases hT14 Mm hvMm hMm with ⟨q0, q1, q2, q3, q4, q5, -⟩ | ⟨q0, q1, q2, q3, q4, q5, -⟩ <;>
      rw [dotProduct_eq_of_vanish _ hl (vanish_of_rest_eq_zero pR)] at hpm <;>
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm <;>
      rw [p0, p1, p2, p3, p4, p5, q0, q1, q2, q3, q4, q5] at hpm
    · have : (2 : ℤ) = 0 := by linear_combination hpm - sδ₀ - sδ₂ - sδ₄
      norm_num at this
    · have : (-2 : ℤ) = 0 := by linear_combination hpm + sδ₄
      norm_num at this
    · have : (-2 : ℤ) = 0 := by linear_combination hpm + sδ₄
      norm_num at this
    · have : (2 : ℤ) = 0 := by linear_combination hpm - sδ₁ - sδ₃ - sδ₄
      norm_num at this
  · rw [hvp, ite_eq_right hpp, mul_zero, add_zero] at eX
    have t0 : δ₀ * v i₀ = 1 := by omega
    have t1 : δ₁ * v i₁ = 1 := by omega
    have t2 : δ₂ * v i₂ = 1 := by omega
    have t3 : δ₃ * v i₃ = 1 := by omega
    refine ⟨?_, ?_, ?_, ?_, hpp⟩
    · rw [eq_mul_of_sign sδ₀ t0, mul_one]
    · rw [eq_mul_of_sign sδ₁ t1, mul_one]
    · rw [eq_mul_of_sign sδ₂ t2, mul_one]
    · rw [eq_mul_of_sign sδ₃ t3, mul_one]

theorem rest_six_eq {i₀ i₁ i₂ i₃ i₄ p q : I} (hl : [i₀, i₁, i₂, i₃, i₄, p].Nodup)
    (hl7 : [i₀, i₁, i₂, i₃, i₄, p, q].Nodup) (M : I → ℤ) :
    ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p].toFinsetᶜ, M j * M j =
      M q * M q + ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, M j * M j := by
  have h6 := dotProduct_split _ hl M M
  have h7 := dotProduct_split _ hl7 M M
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h6 h7
  linarith

@[expose] def RefinedShape (i₀ i₁ i₂ i₃ i₄ p q : I) (δ₀ δ₁ δ₂ δ₃ α : ℤ) (M : I → ℤ) : Prop :=
  (M i₀ = -δ₀ ∧ M i₁ = 0 ∧ M i₂ = 0 ∧ M i₃ = -δ₃ ∧ M i₄ = 0 ∧ M p = 0 ∧ M q = α ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, M j * M j = 0) ∨
    (M i₀ = 0 ∧ M i₁ = -δ₁ ∧ M i₂ = -δ₂ ∧ M i₃ = 0 ∧ M i₄ = 0 ∧ M p = 0 ∧ M q = α ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, M j * M j = 0) ∨
    (M i₀ = 0 ∧ M i₁ = 0 ∧ M i₂ = 0 ∧ M i₃ = 0 ∧ M i₄ = 0 ∧ M p = -α ∧ M q = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, M j * M j = 2)

theorem frame_shape_refine {i₀ i₁ i₂ i₃ i₄ p q : I} (hl : [i₀, i₁, i₂, i₃, i₄, p].Nodup)
    (hl7 : [i₀, i₁, i₂, i₃, i₄, p, q].Nodup) (hq6 : q ∉ [i₀, i₁, i₂, i₃, i₄, p])
    {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
    (sδ₀ : δ₀ * δ₀ = 1) (sδ₁ : δ₁ * δ₁ = 1) (sδ₂ : δ₂ * δ₂ = 1) (sδ₃ : δ₃ * δ₃ = 1)
    (sα : α * α = 1) {M : I → ℤ} (hM : FrameShape i₀ i₁ i₂ i₃ i₄ p δ₀ δ₁ δ₂ δ₃ δ₄ α M)
    (hq : δ₀ * M i₀ + δ₁ * M i₁ + δ₂ * M i₂ + δ₃ * M i₃ + 2 * α * M q = 0) :
    RefinedShape i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ α M := by
  have hsplit := rest_six_eq hl hl7 M
  have hR7 := sum_mul_self_nonneg ([i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ) M
  have hqq := mul_self_nonneg (M q)
  rcases hM with ⟨m0, m1, m2, m3, m4, m5, mR⟩ | ⟨m0, m1, m2, m3, m4, m5, mR⟩ |
      ⟨m0, m1, m2, m3, m4, m5, mR⟩ | ⟨m0, m1, m2, m3, m4, m5, mR⟩ | ⟨m0, m1, m2, m3, m4, m5, mR⟩
  · exfalso
    have hMq := vanish_of_rest_eq_zero mR q hq6
    rw [m0, m1, m2, m3, hMq] at hq
    have : (-2 : ℤ) = 0 := by linear_combination hq + sδ₀ + sδ₂
    norm_num at this
  · have hMq : M q = α := by
      rw [m0, m1, m2, m3] at hq
      have h2 : α * M q = 1 := by
        have h3 : 2 * (α * M q) = 2 := by linear_combination hq + sδ₀ + sδ₃
        omega
      rw [eq_mul_of_sign sα h2, mul_one]
    refine Or.inl ⟨m0, m1, m2, m3, m4, m5, hMq, ?_⟩
    rw [mR, hMq, sα] at hsplit
    linarith
  · have hMq : M q = α := by
      rw [m0, m1, m2, m3] at hq
      have h2 : α * M q = 1 := by
        have h3 : 2 * (α * M q) = 2 := by linear_combination hq + sδ₁ + sδ₂
        omega
      rw [eq_mul_of_sign sα h2, mul_one]
    refine Or.inr (Or.inl ⟨m0, m1, m2, m3, m4, m5, hMq, ?_⟩)
    rw [mR, hMq, sα] at hsplit
    linarith
  · exfalso
    have hMq := vanish_of_rest_eq_zero mR q hq6
    rw [m0, m1, m2, m3, hMq] at hq
    have : (-2 : ℤ) = 0 := by linear_combination hq + sδ₁ + sδ₃
    norm_num at this
  · have hMq : M q = 0 := by
      rw [m0, m1, m2, m3] at hq
      have h2 : α * M q = 0 := by
        have h3 : 2 * (α * M q) = 0 := by linear_combination hq
        omega
      rw [eq_mul_of_sign sα h2, mul_zero]
    refine Or.inr (Or.inr ⟨m0, m1, m2, m3, m4, m5, hMq, ?_⟩)
    rw [mR, hMq] at hsplit
    linarith

theorem halves_shape {d : I → ℝ} (hd : ∀ i, 0 < d i) {i₀ i₁ i₂ i₃ i₄ p q : I}
    (hl7 : [i₀, i₁, i₂, i₃, i₄, p, q].Nodup) {δ₀ δ₁ δ₂ δ₃ α : ℤ}
    (sδ₀ : δ₀ * δ₀ = 1) (sδ₁ : δ₁ * δ₁ = 1) (sδ₂ : δ₂ * δ₂ = 1) (sδ₃ : δ₃ * δ₃ = 1)
    (hα : α = 1 ∨ α = -1) {Mp Mm : I → ℤ} (hMp : RefinedShape i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ α Mp)
    (hMm : RefinedShape i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ α Mm) (hpm : Mp ⬝ᵥ Mm = 1)
    (hdeg : degree d Mp + degree d Mm = 0)
    (hXd : (δ₀ : ℝ) * d i₀ + δ₁ * d i₁ + δ₂ * d i₂ + δ₃ * d i₃ + 2 * α * d p = 0) :
    (Mp i₀ = 0 ∧ Mp i₁ = 0 ∧ Mp i₂ = 0 ∧ Mp i₃ = 0 ∧ Mp i₄ = 0 ∧ Mp p = -α ∧ Mp q = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, Mp j * Mp j = 2) ∧
    (Mm i₀ = 0 ∧ Mm i₁ = 0 ∧ Mm i₂ = 0 ∧ Mm i₃ = 0 ∧ Mm i₄ = 0 ∧ Mm p = -α ∧ Mm q = 0 ∧
      ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, Mm j * Mm j = 2) := by
  have sα := mul_self_of_sign hα
  have hdp := hd p
  have hdq := hd q
  have hT23 : ∀ {M M' : I → ℤ}, (∀ j, j ∉ [i₀, i₁, i₂, i₃, i₄, p, q] → M j = 0) →
      (∀ j, j ∉ [i₀, i₁, i₂, i₃, i₄, p, q] → M' j = 0) → degree d M + degree d M' = 0 →
      M i₀ + M' i₀ = -δ₀ → M i₁ + M' i₁ = -δ₁ → M i₂ + M' i₂ = -δ₂ → M i₃ + M' i₃ = -δ₃ →
      M i₄ + M' i₄ = 0 → M p + M' p = 0 → M q + M' q = 2 * α → False := by
    intro M M' hM hM' hsum e0 e1 e2 e3 e4 e5 e6
    rw [degree_eq_of_vanish d _ hl7 hM, degree_eq_of_vanish d _ hl7 hM'] at hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have c0 : (M i₀ : ℝ) + M' i₀ = -δ₀ := by exact_mod_cast e0
    have c1 : (M i₁ : ℝ) + M' i₁ = -δ₁ := by exact_mod_cast e1
    have c2 : (M i₂ : ℝ) + M' i₂ = -δ₂ := by exact_mod_cast e2
    have c3 : (M i₃ : ℝ) + M' i₃ = -δ₃ := by exact_mod_cast e3
    have c4 : (M i₄ : ℝ) + M' i₄ = 0 := by exact_mod_cast e4
    have c5 : (M p : ℝ) + M' p = 0 := by exact_mod_cast e5
    have c6 : (M q : ℝ) + M' q = 2 * α := by exact_mod_cast e6
    have key : (2 * α : ℝ) * (d p + d q) = 0 := by
      linear_combination hsum - d i₀ * c0 - d i₁ * c1 - d i₂ * c2 - d i₃ * c3 - d i₄ * c4 -
        d p * c5 - d q * c6 + hXd
    rcases hα with rfl | rfl <;> norm_num at key <;> linarith
  rcases hMp with ⟨p0, p1, p2, p3, p4, p5, p6, pR⟩ | ⟨p0, p1, p2, p3, p4, p5, p6, pR⟩ |
      hp5 <;>
    rcases hMm with ⟨q0, q1, q2, q3, q4, q5, q6, qR⟩ | ⟨q0, q1, q2, q3, q4, q5, q6, qR⟩ | hq5
  · exfalso
    rw [dotProduct_eq_of_vanish _ hl7 (vanish_of_rest_eq_zero pR)] at hpm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm
    rw [p0, p1, p2, p3, p4, p5, p6, q0, q1, q2, q3, q4, q5, q6] at hpm
    have : (2 : ℤ) = 0 := by linear_combination hpm - sδ₀ - sδ₃ - sα
    norm_num at this
  · exact (hT23 (vanish_of_rest_eq_zero pR) (vanish_of_rest_eq_zero qR) hdeg
      (by rw [p0, q0]; ring) (by rw [p1, q1]; ring) (by rw [p2, q2]; ring) (by rw [p3, q3]; ring)
      (by rw [p4, q4]; ring) (by rw [p5, q5]; ring) (by rw [p6, q6]; ring)).elim
  · exfalso
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, -⟩ := hq5
    rw [dotProduct_eq_of_vanish _ hl7 (vanish_of_rest_eq_zero pR)] at hpm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm
    rw [p0, p1, p2, p3, p4, p5, p6, q0, q1, q2, q3, q4, q5, q6] at hpm
    norm_num at hpm
  · exact (hT23 (vanish_of_rest_eq_zero pR) (vanish_of_rest_eq_zero qR) hdeg
      (by rw [p0, q0]; ring) (by rw [p1, q1]; ring) (by rw [p2, q2]; ring) (by rw [p3, q3]; ring)
      (by rw [p4, q4]; ring) (by rw [p5, q5]; ring) (by rw [p6, q6]; ring)).elim
  · exfalso
    rw [dotProduct_eq_of_vanish _ hl7 (vanish_of_rest_eq_zero pR)] at hpm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm
    rw [p0, p1, p2, p3, p4, p5, p6, q0, q1, q2, q3, q4, q5, q6] at hpm
    have : (2 : ℤ) = 0 := by linear_combination hpm - sδ₁ - sδ₂ - sα
    norm_num at this
  · exfalso
    obtain ⟨q0, q1, q2, q3, q4, q5, q6, -⟩ := hq5
    rw [dotProduct_eq_of_vanish _ hl7 (vanish_of_rest_eq_zero pR)] at hpm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm
    rw [p0, p1, p2, p3, p4, p5, p6, q0, q1, q2, q3, q4, q5, q6] at hpm
    norm_num at hpm
  · exfalso
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, -⟩ := hp5
    rw [dotProduct_comm, dotProduct_eq_of_vanish _ hl7 (vanish_of_rest_eq_zero qR)] at hpm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm
    rw [p0, p1, p2, p3, p4, p5, p6, q0, q1, q2, q3, q4, q5, q6] at hpm
    norm_num at hpm
  · exfalso
    obtain ⟨p0, p1, p2, p3, p4, p5, p6, -⟩ := hp5
    rw [dotProduct_comm, dotProduct_eq_of_vanish _ hl7 (vanish_of_rest_eq_zero qR)] at hpm
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hpm
    rw [p0, p1, p2, p3, p4, p5, p6, q0, q1, q2, q3, q4, q5, q6] at hpm
    norm_num at hpm
  · exact ⟨hp5, hq5⟩

theorem shift_dotProduct {p : I} {α : ℤ} (sα : α * α = 1) {M M' : I → ℤ} (hM : M p = -α)
    (hM' : M' p = -α) :
    (M + Pi.single p α) ⬝ᵥ (M' + Pi.single p α) = M ⬝ᵥ M' - 1 := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_single, single_dotProduct,
    single_dotProduct, Pi.single_eq_same, hM, hM']
  linear_combination -sα

omit [Fintype I] [DecidableEq I] in
theorem injective_vec_five {a₀ a₁ a₂ a₃ a₄ : I} (h01 : a₀ ≠ a₁) (h02 : a₀ ≠ a₂) (h03 : a₀ ≠ a₃)
    (h04 : a₀ ≠ a₄) (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h14 : a₁ ≠ a₄) (h23 : a₂ ≠ a₃)
    (h24 : a₂ ≠ a₄) (h34 : a₃ ≠ a₄) : Function.Injective ![a₀, a₁, a₂, a₃, a₄] := by
  intro x y hxy
  fin_cases x <;> fin_cases y <;> simp_all

end WreathColumn

open WreathColumn in
theorem positive_degree_integral_wreath_column_rigidity {I H K : Type*} [Fintype I]
    [DecidableEq I] [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (hH : 2 ≤ Fintype.card H) (hK : 1 ≤ Fintype.card K) (d : I → ℝ) (hd : ∀ i, 0 < d i)
    (A : H → I → ℤ) (E : K → I → ℤ) (Ystar : I → ℤ) (Y : K → I → ℤ) (C : I → ℤ)
    (hAd : ∀ h, ∑ i, (A h i : ℝ) * d i = 0) (hEd : ∀ k, ∑ i, (E k i : ℝ) * d i = 0)
    (hYsd : ∑ i, (Ystar i : ℝ) * d i = 0) (hYd : ∀ k, ∑ i, (Y k i : ℝ) * d i = 0)
    (hCd : ∑ i, (C i : ℝ) * d i = 0)
    (hAA : ∀ h h', A h ⬝ᵥ A h' = 4 + 4 * if h = h' then 1 else 0)
    (hEE : ∀ k l, E k ⬝ᵥ E l = 4 + 4 * if k = l then 1 else 0)
    (hAE : ∀ h k, A h ⬝ᵥ E k = 4)
    (hYsYs : Ystar ⬝ᵥ Ystar = 4) (hYsY : ∀ k, Ystar ⬝ᵥ Y k = 0)
    (hYY : ∀ k l, Y k ⬝ᵥ Y l = 4 * if k = l then 1 else 0) (hCC : C ⬝ᵥ C = 8)
    (hYsA : ∀ h, Ystar ⬝ᵥ A h = 0) (hYsE : ∀ k, Ystar ⬝ᵥ E k = 0) (hYsC : Ystar ⬝ᵥ C = 0)
    (hYA : ∀ k h, Y k ⬝ᵥ A h = 0) (hYE : ∀ k l, Y k ⬝ᵥ E l = 0) (hYC : ∀ k, Y k ⬝ᵥ C = 0)
    (hCA : ∀ h, C ⬝ᵥ A h = 0) (hCE : ∀ k, C ⬝ᵥ E k = 0)
    (hAC : ∀ h i, A h i ≡ C i [ZMOD 2]) (hCYs : ∀ i, C i ≡ Ystar i [ZMOD 2])
    (hEYY : ∀ k i, E k i ≡ Ystar i + Y k i [ZMOD 2]) :
    ∃ (i₀ i₁ i₂ i₃ i₄ : I) (p : H → I) (q : K → Fin 4 → I) (δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ)
      (η : K → Fin 4 → ℤ),
      Function.Injective (Sum.elim ![i₀, i₁, i₂, i₃, i₄]
        (Sum.elim p fun x : K × Fin 4 => q x.1 x.2)) ∧
      (∀ s ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α], s = 1 ∨ s = -1) ∧ (∀ k r, η k r = 1 ∨ η k r = -1) ∧
      (∀ h, A h = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ +
        Pi.single (p h) (2 * α)) ∧
      Ystar = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ - Pi.single i₂ δ₂ - Pi.single i₃ δ₃ ∧
      C = Pi.single i₀ δ₀ - Pi.single i₁ δ₁ + Pi.single i₂ δ₂ - Pi.single i₃ δ₃ +
        Pi.single i₄ (2 * δ₄) ∧
      (∀ k, E k = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ +
        ∑ r, Pi.single (q k r) (η k r)) ∧
      (∀ k, Y k = Pi.single (q k 0) (η k 0) + Pi.single (q k 1) (η k 1) -
        Pi.single (q k 2) (η k 2) - Pi.single (q k 3) (η k 3)) ∧
      ∃ D : ℝ, 0 < D ∧ (∀ h, d (p h) = D) ∧
        (δ₀ : ℝ) * d i₀ + δ₁ * d i₁ + δ₂ * d i₂ + δ₃ * d i₃ = -2 * α * D ∧
        ∀ k, (η k 0 : ℝ) * d (q k 0) + η k 1 * d (q k 1) = α * D ∧
          (η k 2 : ℝ) * d (q k 2) + η k 3 * d (q k 3) = α * D := by
  have hAd' : ∀ h, degree d (A h) = 0 := hAd
  have hEd' : ∀ k, degree d (E k) = 0 := hEd
  have hYsd' : degree d Ystar = 0 := hYsd
  have hYd' : ∀ k, degree d (Y k) = 0 := hYd
  have hCd' : degree d C = 0 := hCd
  have hAA' : ∀ h, A h ⬝ᵥ A h = 8 := fun h => by simpa using hAA h h
  have hAAne : ∀ h h', h ≠ h' → A h ⬝ᵥ A h' = 4 := fun h h' hne => by simpa [hne] using hAA h h'
  have hEE' : ∀ k, E k ⬝ᵥ E k = 8 := fun k => by simpa using hEE k k
  have hEEne : ∀ k l, k ≠ l → E k ⬝ᵥ E l = 4 := fun k l hne => by simpa [hne] using hEE k l
  have hYY' : ∀ k, Y k ⬝ᵥ Y k = 4 := fun k => by simpa using hYY k k
  have hYYne : ∀ k l, k ≠ l → Y k ⬝ᵥ Y l = 0 := fun k l hne => by simpa [hne] using hYY k l
  obtain ⟨T, hT, hYsT, hYsform⟩ := exists_four_units (entry_of_norm_four hd hYsYs hYsd') hYsYs
  have hApar : ∀ h i, A h i ≡ Ystar i [ZMOD 2] := fun h i => (hAC h i).trans (hCYs i)
  have hAcore := fun h => exists_core_double hT hYsT hYsform (hApar h) (hAA' h)
  choose hAT pf βf hpfT hβf hAform using hAcore
  obtain ⟨hCT, i₄, δ₄, hi₄T, hδ₄, hCform⟩ := exists_core_double hT hYsT hYsform hCYs hCC
  have hpfi₄ : ∀ h, pf h ≠ i₄ := fun h =>
    double_ne_of_dotProduct_eq_zero hd hT (hAT h) hCT (hpfT h) (hβf h) hδ₄ (hAform h) hCform
      (hCA h) (hAd' h) hCd'
  obtain ⟨h₀⟩ : Nonempty H := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨h₁, hh₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) h₀
  obtain ⟨k₀⟩ : Nonempty K := Fintype.card_pos_iff.mp (by omega)
  have hXform := hAform h₀
  have hXT := hAT h₀
  have hα := hβf h₀
  have hpT := hpfT h₀
  have hpi₄ := hpfi₄ h₀
  have hXX := hAA' h₀
  have hXd := hAd' h₀
  set X := A h₀ with hXdef
  set p := pf h₀ with hpdef
  set α := βf h₀ with hαdef
  have hXi₄ : X i₄ = 0 := by
    rw [hXform, Pi.add_apply, sum_single_apply, Pi.single_eq_of_ne hpi₄.symm]
    simp [hi₄T]
  have hsumY : ∑ t ∈ T, Ystar t * X t = 0 := by
    have h : Ystar ⬝ᵥ X = 0 := hYsA h₀
    rw [hYsform, sum_single_dotProduct] at h
    exact h
  have hsumC : ∑ t ∈ T, C t * X t = 0 := by
    have h : C ⬝ᵥ X = 0 := hCA h₀
    rw [hCform, add_dotProduct, sum_single_dotProduct, single_dotProduct, hXi₄, mul_zero,
      add_zero] at h
    exact h
  have hsumYC : ∑ t ∈ T, (Ystar t * X t) * (C t * X t) = 0 := by
    have h := hYsC
    rw [hYsform, sum_single_dotProduct] at h
    rw [← h]
    refine Finset.sum_congr rfl fun t ht => ?_
    linear_combination (Ystar t * C t) * mul_self_of_sign (hXT t ht)
  obtain ⟨i₀, i₁, i₂, i₃, h01, h02, h03, h12, h13, h23, hTeq, y0, c0, y1, c1, y2, c2, y3, c3⟩ :=
    exists_relabel (y := fun t => Ystar t * X t) (c := fun t => C t * X t) hT
      (fun t ht => sign_mul (hYsT t ht) (hXT t ht)) (fun t ht => sign_mul (hCT t ht) (hXT t ht))
      hsumY hsumC hsumYC
  have hi₀T : i₀ ∈ T := by rw [hTeq]; simp
  have hi₁T : i₁ ∈ T := by rw [hTeq]; simp
  have hi₂T : i₂ ∈ T := by rw [hTeq]; simp
  have hi₃T : i₃ ∈ T := by rw [hTeq]; simp
  have h04 : i₀ ≠ i₄ := fun h => hi₄T (h ▸ hi₀T)
  have h14 : i₁ ≠ i₄ := fun h => hi₄T (h ▸ hi₁T)
  have h24 : i₂ ≠ i₄ := fun h => hi₄T (h ▸ hi₂T)
  have h34 : i₃ ≠ i₄ := fun h => hi₄T (h ▸ hi₃T)
  have h0p : i₀ ≠ p := fun h => hpT (h ▸ hi₀T)
  have h1p : i₁ ≠ p := fun h => hpT (h ▸ hi₁T)
  have h2p : i₂ ≠ p := fun h => hpT (h ▸ hi₂T)
  have h3p : i₃ ≠ p := fun h => hpT (h ▸ hi₃T)
  set δ₀ := X i₀ with hδ₀def
  set δ₁ := X i₁ with hδ₁def
  set δ₂ := X i₂ with hδ₂def
  set δ₃ := X i₃ with hδ₃def
  have hδ₀ : δ₀ = 1 ∨ δ₀ = -1 := hXT i₀ hi₀T
  have hδ₁ : δ₁ = 1 ∨ δ₁ = -1 := hXT i₁ hi₁T
  have hδ₂ : δ₂ = 1 ∨ δ₂ = -1 := hXT i₂ hi₂T
  have hδ₃ : δ₃ = 1 ∨ δ₃ = -1 := hXT i₃ hi₃T
  have sδ₀ := mul_self_of_sign hδ₀
  have sδ₁ := mul_self_of_sign hδ₁
  have sδ₂ := mul_self_of_sign hδ₂
  have sδ₃ := mul_self_of_sign hδ₃
  have sδ₄ := mul_self_of_sign hδ₄
  have sα := mul_self_of_sign hα
  have hYs' : Ystar = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ - Pi.single i₂ δ₂ - Pi.single i₃ δ₃ := by
    rw [hYsform, hTeq, sum_four _ h01 h02 h03 h12 h13 h23, eq_mul_of_mul_eq sδ₀ y0,
      eq_mul_of_mul_eq sδ₁ y1, eq_mul_of_mul_eq sδ₂ y2, eq_mul_of_mul_eq sδ₃ y3]
    simp only [one_mul, neg_one_mul, Pi.single_neg]
    abel
  have hC' : C = Pi.single i₀ δ₀ - Pi.single i₁ δ₁ + Pi.single i₂ δ₂ - Pi.single i₃ δ₃ +
      Pi.single i₄ (2 * δ₄) := by
    rw [hCform, hTeq, sum_four _ h01 h02 h03 h12 h13 h23, eq_mul_of_mul_eq sδ₀ c0,
      eq_mul_of_mul_eq sδ₁ c1, eq_mul_of_mul_eq sδ₂ c2, eq_mul_of_mul_eq sδ₃ c3]
    simp only [one_mul, neg_one_mul, Pi.single_neg]
    abel
  have hX' : X = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ +
      Pi.single p (2 * α) := by
    conv_lhs => rw [hXform]
    rw [hTeq, sum_four _ h01 h02 h03 h12 h13 h23]
  have hXpar : ∀ i, X i ≡ Ystar i [ZMOD 2] := hApar h₀
  have hhalf : ∀ k, ∃ Mp Mm : I → ℤ,
      (2 : ℤ) • Mp = E k - X + Y k ∧ (2 : ℤ) • Mm = E k - X - Y k := by
    intro k
    obtain ⟨Mp, hMp⟩ := exists_half (v := E k - X + Y k) fun i => by
      have h1 := hEYY k i
      have h2 := hXpar i
      simp only [Pi.add_apply, Pi.sub_apply]
      unfold Int.ModEq at *
      omega
    obtain ⟨Mm, hMm⟩ := exists_half (v := E k - X - Y k) fun i => by
      have h1 := hEYY k i
      have h2 := hXpar i
      simp only [Pi.sub_apply]
      unfold Int.ModEq at *
      omega
    exact ⟨Mp, Mm, hMp, hMm⟩
  choose Mp Mm hMp hMm using hhalf
  have hXE : ∀ k, X ⬝ᵥ E k = 4 := fun k => hAE h₀ k
  have hEX : ∀ k, E k ⬝ᵥ X = 4 := fun k => by rw [dotProduct_comm]; exact hXE k
  have hYX : ∀ k, Y k ⬝ᵥ X = 0 := fun k => hYA k h₀
  have hXY : ∀ k, X ⬝ᵥ Y k = 0 := fun k => by rw [dotProduct_comm]; exact hYX k
  have hEY : ∀ k, E k ⬝ᵥ Y k = 0 := fun k => by rw [dotProduct_comm]; exact hYE k k
  have hMpw : ∀ k w, 2 * (w ⬝ᵥ Mp k) = w ⬝ᵥ E k - w ⬝ᵥ X + w ⬝ᵥ Y k := fun k w => by
    rw [two_mul_dotProduct_of_smul_eq (hMp k), dotProduct_add, dotProduct_sub]
  have hMmw : ∀ k w, 2 * (w ⬝ᵥ Mm k) = w ⬝ᵥ E k - w ⬝ᵥ X - w ⬝ᵥ Y k := fun k w => by
    rw [two_mul_dotProduct_of_smul_eq (hMm k), dotProduct_sub, dotProduct_sub]
  have hEMp : ∀ k, E k ⬝ᵥ Mp k = 2 := fun k => by
    have h := hMpw k (E k)
    rw [hEE', hEX, hEY] at h
    linarith
  have hEMm : ∀ k, E k ⬝ᵥ Mm k = 2 := fun k => by
    have h := hMmw k (E k)
    rw [hEE', hEX, hEY] at h
    linarith
  have hXMp : ∀ k, X ⬝ᵥ Mp k = -2 := fun k => by
    have h := hMpw k X
    rw [hXE, hXX, hXY] at h
    linarith
  have hXMm : ∀ k, X ⬝ᵥ Mm k = -2 := fun k => by
    have h := hMmw k X
    rw [hXE, hXX, hXY] at h
    linarith
  have hYMp : ∀ k, Y k ⬝ᵥ Mp k = 2 := fun k => by
    have h := hMpw k (Y k)
    rw [hYE, hYX, hYY'] at h
    linarith
  have hYMm : ∀ k, Y k ⬝ᵥ Mm k = -2 := fun k => by
    have h := hMmw k (Y k)
    rw [hYE, hYX, hYY'] at h
    linarith
  have hMpMp : ∀ k, Mp k ⬝ᵥ Mp k = 3 := fun k => by
    have h := hMpw k (Mp k)
    rw [dotProduct_comm (Mp k) (E k), dotProduct_comm (Mp k) X, dotProduct_comm (Mp k) (Y k),
      hEMp, hXMp, hYMp] at h
    linarith
  have hMmMm : ∀ k, Mm k ⬝ᵥ Mm k = 3 := fun k => by
    have h := hMmw k (Mm k)
    rw [dotProduct_comm (Mm k) (E k), dotProduct_comm (Mm k) X, dotProduct_comm (Mm k) (Y k),
      hEMm, hXMm, hYMm] at h
    linarith
  have hMpMm : ∀ k, Mp k ⬝ᵥ Mm k = 1 := fun k => by
    have h := hMmw k (Mp k)
    rw [dotProduct_comm (Mp k) (E k), dotProduct_comm (Mp k) X, dotProduct_comm (Mp k) (Y k),
      hEMp, hXMp, hYMp] at h
    linarith
  have hYsMp : ∀ k, Ystar ⬝ᵥ Mp k = 0 := fun k => by
    have h := hMpw k Ystar
    have h2 : Ystar ⬝ᵥ X = 0 := hYsA h₀
    rw [hYsE, h2, hYsY] at h
    linarith
  have hYsMm : ∀ k, Ystar ⬝ᵥ Mm k = 0 := fun k => by
    have h := hMmw k Ystar
    have h2 : Ystar ⬝ᵥ X = 0 := hYsA h₀
    rw [hYsE, h2, hYsY] at h
    linarith
  have hCY : ∀ k, C ⬝ᵥ Y k = 0 := fun k => by rw [dotProduct_comm]; exact hYC k
  have hCMp : ∀ k, C ⬝ᵥ Mp k = 0 := fun k => by
    have h := hMpw k C
    have h2 : C ⬝ᵥ X = 0 := hCA h₀
    rw [hCE, h2, hCY] at h
    linarith
  have hCMm : ∀ k, C ⬝ᵥ Mm k = 0 := fun k => by
    have h := hMmw k C
    have h2 : C ⬝ᵥ X = 0 := hCA h₀
    rw [hCE, h2, hCY] at h
    linarith
  have hAY : ∀ h k, A h ⬝ᵥ Y k = 0 := fun h k => by rw [dotProduct_comm]; exact hYA k h
  have hAMp : ∀ h, h ≠ h₀ → ∀ k, A h ⬝ᵥ Mp k = 0 := fun h hh k => by
    have h1 := hMpw k (A h)
    have h2 : A h ⬝ᵥ X = 4 := hAAne h h₀ hh
    rw [hAE, h2, hAY] at h1
    linarith
  have hAMm : ∀ h, h ≠ h₀ → ∀ k, A h ⬝ᵥ Mm k = 0 := fun h hh k => by
    have h1 := hMmw k (A h)
    have h2 : A h ⬝ᵥ X = 4 := hAAne h h₀ hh
    rw [hAE, h2, hAY] at h1
    linarith
  have hdMp : ∀ k, degree d (Mp k) = 0 := fun k => by
    have h := two_mul_degree_of_smul_eq d (hMp k)
    rw [map_add, map_sub, hEd', hXd, hYd'] at h
    linarith
  have hdMm : ∀ k, degree d (Mm k) = 0 := fun k => by
    have h := two_mul_degree_of_smul_eq d (hMm k)
    rw [map_sub, map_sub, hEd', hXd, hYd'] at h
    linarith
  have cY : ∀ v : I → ℤ, Ystar ⬝ᵥ v = δ₀ * v i₀ + δ₁ * v i₁ - δ₂ * v i₂ - δ₃ * v i₃ := fun v => by
    rw [hYs']
    simp only [add_dotProduct, sub_dotProduct, single_dotProduct]
  have cC : ∀ v : I → ℤ, C ⬝ᵥ v =
      δ₀ * v i₀ - δ₁ * v i₁ + δ₂ * v i₂ - δ₃ * v i₃ + 2 * δ₄ * v i₄ := fun v => by
    rw [hC']
    simp only [add_dotProduct, sub_dotProduct, single_dotProduct]
  have cX : ∀ v : I → ℤ, X ⬝ᵥ v =
      δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ + 2 * α * v p := fun v => by
    rw [hX']
    simp only [add_dotProduct, single_dotProduct]
  have hl6 : [i₀, i₁, i₂, i₃, i₄, p].Nodup := by
    simp [h01, h02, h03, h04, h0p, h12, h13, h14, h1p, h23, h24, h2p, h34, h3p, hpi₄.symm]
  have typesMp := fun k => frame_types hl6 sδ₀ sδ₁ sδ₂ sδ₃ sδ₄ sα
    (by rw [← cY]; exact hYsMp k) (by rw [← cC]; exact hCMp k) (by rw [← cX]; exact hXMp k)
    (hMpMp k)
  have typesMm := fun k => frame_types hl6 sδ₀ sδ₁ sδ₂ sδ₃ sδ₄ sα
    (by rw [← cY]; exact hYsMm k) (by rw [← cC]; exact hCMm k) (by rw [← cX]; exact hXMm k)
    (hMmMm k)
  have hAi₄ : ∀ h, A h i₄ = 0 := fun h => by
    rw [hAform h, Pi.add_apply, sum_single_apply, Pi.single_eq_of_ne (hpfi₄ h).symm]
    simp [hi₄T]
  have hAform' : ∀ h, A h = Pi.single i₀ (A h i₀) + Pi.single i₁ (A h i₁) +
      Pi.single i₂ (A h i₂) + Pi.single i₃ (A h i₃) + Pi.single (pf h) (2 * βf h) := fun h => by
    conv_lhs => rw [hAform h]
    rw [hTeq, sum_four _ h01 h02 h03 h12 h13 h23]
  have hcore : ∀ h, h ≠ h₀ →
      A h i₀ = δ₀ ∧ A h i₁ = δ₁ ∧ A h i₂ = δ₂ ∧ A h i₃ = δ₃ ∧ pf h ≠ p := fun h hh =>
    core_eq_of_frame hl6 h0p h1p h2p h3p hδ₀ hδ₁ hδ₂ hδ₃ hδ₄ hα (hβf h) (hAform' h)
      (hAT h i₀ hi₀T) (hAT h i₁ hi₁T) (hAT h i₂ hi₂T) (hAT h i₃ hi₃T)
      (by rw [← cY]; exact hYsA h) (by have e := hCA h; rw [cC, hAi₄] at e; linarith)
      (by rw [← cX]; exact hAAne h₀ h hh.symm) (typesMp k₀) (typesMm k₀) (hAMp h hh k₀)
      (hAMm h hh k₀) (hMpMm k₀)
  have hXd' : (δ₀ : ℝ) * d i₀ + δ₁ * d i₁ + δ₂ * d i₂ + δ₃ * d i₃ + 2 * α * d p = 0 := by
    rw [← hXd, hX']
    simp only [map_add, degree_single]
    push_cast
    ring
  have hβd : ∀ h, h ≠ h₀ → βf h = α ∧ d (pf h) = d p := by
    intro h hh
    obtain ⟨a0, a1, a2, a3, -⟩ := hcore h hh
    have e := hAd' h
    rw [hAform' h, a0, a1, a2, a3] at e
    simp only [map_add, degree_single] at e
    push_cast at e
    have key : (βf h : ℝ) * d (pf h) = α * d p := by linarith
    have hdh := hd (pf h)
    have hdp := hd p
    rcases hβf h with h1 | h1 <;> rcases hα with h2 | h2 <;> rw [h1, h2] at key <;>
      norm_num at key
    · exact ⟨by rw [h1, h2], key⟩
    · linarith
    · linarith
    · exact ⟨by rw [h1, h2], by linarith⟩
  have hAcoreform : ∀ h, A h = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ +
      Pi.single i₃ δ₃ + Pi.single (pf h) (2 * α) := by
    intro h
    by_cases hh : h = h₀
    · subst hh
      exact hX'
    · obtain ⟨a0, a1, a2, a3, -⟩ := hcore h hh
      rw [hAform' h, a0, a1, a2, a3, (hβd h hh).1]
  set q := pf h₁ with hqdef
  have hqT : q ∉ T := hpfT h₁
  have hqi₄ : q ≠ i₄ := hpfi₄ h₁
  have hqp : q ≠ p := (hcore h₁ hh₁).2.2.2.2
  have h0q : i₀ ≠ q := fun h => hqT (h ▸ hi₀T)
  have h1q : i₁ ≠ q := fun h => hqT (h ▸ hi₁T)
  have h2q : i₂ ≠ q := fun h => hqT (h ▸ hi₂T)
  have h3q : i₃ ≠ q := fun h => hqT (h ▸ hi₃T)
  have hl7 : [i₀, i₁, i₂, i₃, i₄, p, q].Nodup := by
    simp [h01, h02, h03, h04, h0p, h0q, h12, h13, h14, h1p, h1q, h23, h24, h2p, h2q, h34, h3p,
      h3q, hpi₄.symm, hqi₄.symm, hqp.symm]
  have hq6 : q ∉ [i₀, i₁, i₂, i₃, i₄, p] := by
    simp [h0q.symm, h1q.symm, h2q.symm, h3q.symm, hqi₄, hqp]
  have hA₁ : A h₁ = Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃ +
      Pi.single q (2 * α) := hAcoreform h₁
  have cA₁ : ∀ v : I → ℤ, A h₁ ⬝ᵥ v =
      δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ + 2 * α * v q := fun v => by
    rw [hA₁]
    simp only [add_dotProduct, single_dotProduct]
  have hshape : ∀ k,
      (Mp k i₀ = 0 ∧ Mp k i₁ = 0 ∧ Mp k i₂ = 0 ∧ Mp k i₃ = 0 ∧ Mp k i₄ = 0 ∧ Mp k p = -α ∧
        Mp k q = 0 ∧ ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, Mp k j * Mp k j = 2) ∧
      (Mm k i₀ = 0 ∧ Mm k i₁ = 0 ∧ Mm k i₂ = 0 ∧ Mm k i₃ = 0 ∧ Mm k i₄ = 0 ∧ Mm k p = -α ∧
        Mm k q = 0 ∧ ∑ j ∈ [i₀, i₁, i₂, i₃, i₄, p, q].toFinsetᶜ, Mm k j * Mm k j = 2) := by
    intro k
    exact halves_shape hd hl7 sδ₀ sδ₁ sδ₂ sδ₃ hα
      (frame_shape_refine hl6 hl7 hq6 sδ₀ sδ₁ sδ₂ sδ₃ sα (typesMp k)
        (by rw [← cA₁]; exact hAMp h₁ hh₁ k))
      (frame_shape_refine hl6 hl7 hq6 sδ₀ sδ₁ sδ₂ sδ₃ sα (typesMm k)
        (by rw [← cA₁]; exact hAMm h₁ hh₁ k))
      (hMpMm k) (by rw [hdMp, hdMm, add_zero]) hXd'
  set core : I → ℤ := Pi.single i₀ δ₀ + Pi.single i₁ δ₁ + Pi.single i₂ δ₂ + Pi.single i₃ δ₃
    with hcoredef
  obtain ⟨P, hP⟩ : ∃ P : K → I → ℤ, ∀ k, P k = Mp k + Pi.single p α := ⟨_, fun k => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : K → I → ℤ, ∀ k, Q k = Mm k + Pi.single p α := ⟨_, fun k => rfl⟩
  have hPP : ∀ k, P k ⬝ᵥ P k = 2 := fun k => by
    rw [hP, shift_dotProduct sα (hshape k).1.2.2.2.2.2.1 (hshape k).1.2.2.2.2.2.1, hMpMp]
    norm_num
  have hQQ : ∀ k, Q k ⬝ᵥ Q k = 2 := fun k => by
    rw [hQ, shift_dotProduct sα (hshape k).2.2.2.2.2.2.1 (hshape k).2.2.2.2.2.2.1, hMmMm]
    norm_num
  have hPQ : ∀ k, P k ⬝ᵥ Q k = 0 := fun k => by
    rw [hP, hQ, shift_dotProduct sα (hshape k).1.2.2.2.2.2.1 (hshape k).2.2.2.2.2.2.1, hMpMm]
    norm_num
  have hdP : ∀ k, degree d (P k) = α * d p := fun k => by
    rw [hP, map_add, hdMp, degree_single, zero_add]
  have hdQ : ∀ k, degree d (Q k) = α * d p := fun k => by
    rw [hQ, map_add, hdMm, degree_single, zero_add]
  have hPv : ∀ k, P k i₀ = 0 ∧ P k i₁ = 0 ∧ P k i₂ = 0 ∧ P k i₃ = 0 ∧ P k i₄ = 0 ∧ P k p = 0 ∧
      P k q = 0 := fun k => by
    obtain ⟨m0, m1, m2, m3, m4, m5, m6, -⟩ := (hshape k).1
    simp only [hP, Pi.add_apply, m0, m1, m2, m3, m4, m5, m6, Pi.single_eq_same,
      Pi.single_eq_of_ne h0p, Pi.single_eq_of_ne h1p, Pi.single_eq_of_ne h2p,
      Pi.single_eq_of_ne h3p, Pi.single_eq_of_ne hpi₄.symm, Pi.single_eq_of_ne hqp]
    norm_num
  have hQv : ∀ k, Q k i₀ = 0 ∧ Q k i₁ = 0 ∧ Q k i₂ = 0 ∧ Q k i₃ = 0 ∧ Q k i₄ = 0 ∧ Q k p = 0 ∧
      Q k q = 0 := fun k => by
    obtain ⟨m0, m1, m2, m3, m4, m5, m6, -⟩ := (hshape k).2
    simp only [hQ, Pi.add_apply, m0, m1, m2, m3, m4, m5, m6, Pi.single_eq_same,
      Pi.single_eq_of_ne h0p, Pi.single_eq_of_ne h1p, Pi.single_eq_of_ne h2p,
      Pi.single_eq_of_ne h3p, Pi.single_eq_of_ne hpi₄.symm, Pi.single_eq_of_ne hqp]
    norm_num
  have hEXM : ∀ k, E k = X + Mp k + Mm k := fun k => by
    funext i
    have h1 := congrFun (hMp k) i
    have h2 := congrFun (hMm k) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
    omega
  have hYMM : ∀ k, Y k = Mp k - Mm k := fun k => by
    funext i
    have h1 := congrFun (hMp k) i
    have h2 := congrFun (hMm k) i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.sub_apply] at h1 h2 ⊢
    omega
  have hsplitp : (Pi.single p (2 * α) : I → ℤ) = Pi.single p α + Pi.single p α := by
    rw [← Pi.single_add, two_mul]
  have hEform : ∀ k, E k = core + P k + Q k := fun k => by
    rw [hEXM k, hX', hP k, hQ k, hsplitp]
    abel
  have hYform : ∀ k, Y k = P k - Q k := fun k => by
    rw [hYMM k, hP k, hQ k]
    abel
  choose qa qb hqab hqa hqb hPab using fun k => exists_two_units (hPP k)
  choose qc qd hqcd hqc hqd hQcd using fun k => exists_two_units (hQQ k)
  have hdisj : ∀ k j, P k j * Q k j = 0 := fun k =>
    disjoint_of_norm_two hd (hPP k) (hQQ k) (hPQ k) (by rw [hdP, hdQ])
  have cCore : ∀ v : I → ℤ, core ⬝ᵥ v = δ₀ * v i₀ + δ₁ * v i₁ + δ₂ * v i₂ + δ₃ * v i₃ :=
    fun v => by
      rw [hcoredef]
      simp only [add_dotProduct, single_dotProduct]
  have hcP : ∀ k, core ⬝ᵥ P k = 0 := fun k => by
    obtain ⟨v0, v1, v2, v3, -⟩ := hPv k
    rw [cCore, v0, v1, v2, v3]
    ring
  have hcQ : ∀ k, core ⬝ᵥ Q k = 0 := fun k => by
    obtain ⟨v0, v1, v2, v3, -⟩ := hQv k
    rw [cCore, v0, v1, v2, v3]
    ring
  have hPc : ∀ k, P k ⬝ᵥ core = 0 := fun k => by rw [dotProduct_comm]; exact hcP k
  have hQc : ∀ k, Q k ⬝ᵥ core = 0 := fun k => by rw [dotProduct_comm]; exact hcQ k
  have hcorev : core i₀ = δ₀ ∧ core i₁ = δ₁ ∧ core i₂ = δ₂ ∧ core i₃ = δ₃ := by
    simp only [hcoredef, Pi.add_apply, Pi.single_apply, h01, h02, h03, h12, h13, h23,
      h01.symm, h02.symm, h03.symm, h12.symm, h13.symm, h23.symm, ↓reduceIte]
    simp
  have hcc : core ⬝ᵥ core = 4 := by
    rw [cCore, hcorev.1, hcorev.2.1, hcorev.2.2.1, hcorev.2.2.2]
    linear_combination sδ₀ + sδ₁ + sδ₂ + sδ₃
  have hcross : ∀ k l, k ≠ l →
      P k ⬝ᵥ P l = 0 ∧ P k ⬝ᵥ Q l = 0 ∧ Q k ⬝ᵥ P l = 0 ∧ Q k ⬝ᵥ Q l = 0 := by
    intro k l hkl
    have e1 := hEEne k l hkl
    have e2 := hYYne k l hkl
    have e3 := hYE k l
    have e4 := hYE l k
    rw [hEform k, hEform l] at e1
    rw [hYform k, hYform l] at e2
    rw [hYform k, hEform l] at e3
    rw [hYform l, hEform k] at e4
    simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, hcc, hcP, hcQ,
      hPc, hQc] at e1 e2 e3 e4
    rw [dotProduct_comm (P l) (P k), dotProduct_comm (P l) (Q k), dotProduct_comm (Q l) (P k),
      dotProduct_comm (Q l) (Q k)] at e4
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hxPP : ∀ k l, k ≠ l → ∀ j, P k j * P l j = 0 := fun k l hkl =>
    disjoint_of_norm_two hd (hPP k) (hPP l) (hcross k l hkl).1 (by rw [hdP, hdP])
  have hxPQ : ∀ k l, k ≠ l → ∀ j, P k j * Q l j = 0 := fun k l hkl =>
    disjoint_of_norm_two hd (hPP k) (hQQ l) (hcross k l hkl).2.1 (by rw [hdP, hdQ])
  have hxQP : ∀ k l, k ≠ l → ∀ j, Q k j * P l j = 0 := fun k l hkl =>
    disjoint_of_norm_two hd (hQQ k) (hPP l) (hcross k l hkl).2.2.1 (by rw [hdQ, hdP])
  have hxQQ : ∀ k l, k ≠ l → ∀ j, Q k j * Q l j = 0 := fun k l hkl =>
    disjoint_of_norm_two hd (hQQ k) (hQQ l) (hcross k l hkl).2.2.2 (by rw [hdQ, hdQ])
  have hPpf : ∀ k h, P k (pf h) = 0 ∧ Q k (pf h) = 0 := by
    intro k h
    by_cases hh : h = h₀
    · subst hh
      exact ⟨(hPv k).2.2.2.2.2.1, (hQv k).2.2.2.2.2.1⟩
    · have hpfp : pf h ≠ p := (hcore h hh).2.2.2.2
      have e1 := hAMp h hh k
      have e2 := hAMm h hh k
      rw [hAcoreform h, add_dotProduct, single_dotProduct, cCore] at e1 e2
      obtain ⟨m0, m1, m2, m3, -⟩ := (hshape k).1
      obtain ⟨n0, n1, n2, n3, -⟩ := (hshape k).2
      rw [m0, m1, m2, m3] at e1
      rw [n0, n1, n2, n3] at e2
      have hα0 : α ≠ 0 := by rcases hα with h | h <;> rw [h] <;> norm_num
      have f1 : Mp k (pf h) = 0 := by
        have : 2 * α * Mp k (pf h) = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' (mul_ne_zero two_ne_zero hα0)
        · exact h'
      have f2 : Mm k (pf h) = 0 := by
        have : 2 * α * Mm k (pf h) = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' (mul_ne_zero two_ne_zero hα0)
        · exact h'
      rw [hP, hQ, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hpfp, f1, f2]
      simp
  have nPa : ∀ k, P k (qa k) ≠ 0 := fun k => by rcases hqa k with h | h <;> rw [h] <;> norm_num
  have nPb : ∀ k, P k (qb k) ≠ 0 := fun k => by rcases hqb k with h | h <;> rw [h] <;> norm_num
  have nQc : ∀ k, Q k (qc k) ≠ 0 := fun k => by rcases hqc k with h | h <;> rw [h] <;> norm_num
  have nQd : ∀ k, Q k (qd k) ≠ 0 := fun k => by rcases hqd k with h | h <;> rw [h] <;> norm_num
  have hWnz : ∀ k (r : Fin 4), (![P k, P k, Q k, Q k] r) (![qa k, qb k, qc k, qd k] r) ≠ 0 := by
    intro k r
    fin_cases r
    · exact nPa k
    · exact nPb k
    · exact nQc k
    · exact nQd k
  have hWx : ∀ k l, k ≠ l → ∀ (r s : Fin 4) j,
      (![P k, P k, Q k, Q k] r) j * (![P l, P l, Q l, Q l] s) j = 0 := by
    intro k l hkl r s j
    fin_cases r <;> fin_cases s
    all_goals first
      | exact hxPP k l hkl j | exact hxPQ k l hkl j | exact hxQP k l hkl j
      | exact hxQQ k l hkl j
  have hWv : ∀ k (r : Fin 4), (![P k, P k, Q k, Q k] r) i₀ = 0 ∧
      (![P k, P k, Q k, Q k] r) i₁ = 0 ∧ (![P k, P k, Q k, Q k] r) i₂ = 0 ∧
      (![P k, P k, Q k, Q k] r) i₃ = 0 ∧ (![P k, P k, Q k, Q k] r) i₄ = 0 ∧
      ∀ h, (![P k, P k, Q k, Q k] r) (pf h) = 0 := by
    intro k r
    obtain ⟨a0, a1, a2, a3, a4, -⟩ := hPv k
    obtain ⟨b0, b1, b2, b3, b4, -⟩ := hQv k
    fin_cases r
    · exact ⟨a0, a1, a2, a3, a4, fun h => (hPpf k h).1⟩
    · exact ⟨a0, a1, a2, a3, a4, fun h => (hPpf k h).1⟩
    · exact ⟨b0, b1, b2, b3, b4, fun h => (hPpf k h).2⟩
    · exact ⟨b0, b1, b2, b3, b4, fun h => (hPpf k h).2⟩
  have hsign : ∀ s ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α], s = 1 ∨ s = -1 := by
    intro s hs
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  refine ⟨i₀, i₁, i₂, i₃, i₄, pf, fun k => ![qa k, qb k, qc k, qd k], δ₀, δ₁, δ₂, δ₃, δ₄, α,
    fun k => ![P k (qa k), P k (qb k), Q k (qc k), Q k (qd k)], ?_, hsign, ?_, hAcoreform, hYs',
    hC', ?_, ?_, d p, hd p, ?_, ?_, ?_⟩
  ·
    apply Function.Injective.sumElim
    · exact injective_vec_five h01 h02 h03 h04 h12 h13 h14 h23 h24 h34
    · apply Function.Injective.sumElim
      · intro h h' hpf
        by_contra hne
        have e := hAAne h h' hne
        have hAeq : A h = A h' := by rw [hAcoreform h, hAcoreform h', hpf]
        rw [hAeq, hAA'] at e
        norm_num at e
      · rintro ⟨k, r⟩ ⟨l, s⟩ hkl
        simp only at hkl
        by_cases hk : k = l
        · subst hk
          by_cases hrs : (r : ℕ) / 2 = (s : ℕ) / 2
          · fin_cases r <;> fin_cases s <;>
              first
                | rfl | exact absurd hkl (hqab k) | exact absurd hkl.symm (hqab k)
                | exact absurd hkl (hqcd k) | exact absurd hkl.symm (hqcd k)
                | (exfalso; simp at hrs)
          · exfalso
            have hz : (![P k, P k, Q k, Q k] r) (![qa k, qb k, qc k, qd k] r) *
                (![P k, P k, Q k, Q k] s) (![qa k, qb k, qc k, qd k] r) = 0 := by
              fin_cases r <;> fin_cases s <;> (try simp at hrs) <;>
                first
                  | exact hdisj k _ | (rw [mul_comm]; exact hdisj k _)
            rw [hkl] at hz
            rcases mul_eq_zero.mp hz with h0 | h0
            · rw [← hkl] at h0
              exact hWnz k r h0
            · exact hWnz k s h0
        · exfalso
          have hz := hWx k l hk r s (![qa k, qb k, qc k, qd k] r)
          rcases mul_eq_zero.mp hz with h0 | h0
          · exact hWnz k r h0
          · rw [hkl] at h0
            exact hWnz l s h0
      · rintro h ⟨k, r⟩ heq
        simp only at heq
        apply hWnz k r
        rw [← heq]
        exact (hWv k r).2.2.2.2.2 h
    · rintro r (h | ⟨k, s⟩) heq
      · simp only [Sum.elim_inl] at heq
        fin_cases r
        · exact hpfT h (heq ▸ hi₀T)
        · exact hpfT h (heq ▸ hi₁T)
        · exact hpfT h (heq ▸ hi₂T)
        · exact hpfT h (heq ▸ hi₃T)
        · exact hpfi₄ h heq.symm
      · simp only [Sum.elim_inr] at heq
        apply hWnz k s
        rw [← heq]
        obtain ⟨w0, w1, w2, w3, w4, -⟩ := hWv k s
        fin_cases r
        · exact w0
        · exact w1
        · exact w2
        · exact w3
        · exact w4
  · intro k r
    fin_cases r
    · exact hqa k
    · exact hqb k
    · exact hqc k
    · exact hqd k
  · intro k
    rw [Fin.sum_univ_four, hEform k]
    conv_lhs => rw [hPab k, hQcd k]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hcoredef]
    abel
  · intro k
    rw [hYform k]
    conv_lhs => rw [hPab k, hQcd k]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    abel
  · intro h
    by_cases hh : h = h₀
    · subst hh
      rfl
    · exact (hβd h hh).2
  · linarith
  · intro k
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    constructor
    · have e := hdP k
      rw [hPab k, map_add, degree_single, degree_single] at e
      exact e
    · have e := hdQ k
      rw [hQcd k, map_add, degree_single, degree_single] at e
      exact e

end CFSG.Wreathed
