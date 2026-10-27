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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankTwoShapes

open scoped BigOperators

private theorem int_eq_of_mul_self_le_two {x : ℤ} (h : x * x ≤ 2) : x = -1 ∨ x = 0 ∨ x = 1 := by
  have h1 : -1 ≤ x := by nlinarith
  have h2 : x ≤ 1 := by nlinarith
  omega

private theorem one_le_mul_self_of_ne_zero {x : ℤ} (h : x ≠ 0) : 1 ≤ x * x := by
  have := mul_self_pos.mpr h
  omega

private theorem sum_eq_add_of_two {α β : Type*} [DecidableEq α] [AddCommMonoid β] {I : Finset α}
    {p q : α} (hp : p ∈ I) (hq : q ∈ I) (hpq : p ≠ q) (f : α → β)
    (hf : ∀ i ∈ I, i ≠ p → i ≠ q → f i = 0) : ∑ i ∈ I, f i = f p + f q := by
  rw [← Finset.sum_pair hpq]
  symm
  apply Finset.sum_subset
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hp
    · rw [Finset.mem_singleton.mp hi]
      exact hq
  · intro i hi hi'
    exact hf i hi (fun h => hi' (h ▸ Finset.mem_insert_self _ _))
      (fun h => hi' (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

private structure IsPair {α : Type*} (I : Finset α) (v : α → ℤ) (p q : α) : Prop where
  left_mem : p ∈ I
  right_mem : q ∈ I
  ne : p ≠ q
  left : v p = 1 ∨ v p = -1
  right : v q = 1 ∨ v q = -1
  eq_zero : ∀ i ∈ I, i ≠ p → i ≠ q → v i = 0

private theorem entry_of_norm_two {α : Type*} {I : Finset α} {v : α → ℤ} {p : α} (hp : p ∈ I)
    (hv : ∑ i ∈ I, v i * v i = 2) : v p = -1 ∨ v p = 0 ∨ v p = 1 :=
  int_eq_of_mul_self_le_two
    (hv ▸ Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg (v i)) hp)

private theorem isPair_of_two {α : Type*} [DecidableEq α] {I : Finset α} {v : α → ℤ} {p q : α}
    (hp : p ∈ I) (hq : q ∈ I) (hpq : p ≠ q) (hvp : v p ≠ 0) (hvq : v q ≠ 0)
    (hv : ∑ i ∈ I, v i * v i = 2) : IsPair I v p q := by
  have hq' : q ∈ I.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have e1 : v p * v p + ∑ i ∈ I.erase p, v i * v i = ∑ i ∈ I, v i * v i :=
    Finset.add_sum_erase I (fun i => v i * v i) hp
  have e2 : v q * v q + ∑ i ∈ (I.erase p).erase q, v i * v i = ∑ i ∈ I.erase p, v i * v i :=
    Finset.add_sum_erase (I.erase p) (fun i => v i * v i) hq'
  have h1 := one_le_mul_self_of_ne_zero hvp
  have h2 := one_le_mul_self_of_ne_zero hvq
  have h3 : 0 ≤ ∑ i ∈ (I.erase p).erase q, v i * v i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hrest : ∑ i ∈ (I.erase p).erase q, v i * v i = 0 := by linarith
  refine ⟨hp, hq, hpq, mul_self_eq_one_iff.mp (by linarith), mul_self_eq_one_iff.mp (by linarith),
    fun i hi hip hiq => ?_⟩
  have hi' : i ∈ (I.erase p).erase q := Finset.mem_erase.mpr ⟨hiq, Finset.mem_erase.mpr ⟨hip, hi⟩⟩
  exact mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).mp hrest i hi')

private theorem exists_isPair_of_ne_zero {α : Type*} [DecidableEq α] {I : Finset α} {v : α → ℤ}
    {p : α} (hp : p ∈ I) (hvp : v p ≠ 0) (hv : ∑ i ∈ I, v i * v i = 2) :
    ∃ q, IsPair I v p q := by
  have e1 : v p * v p + ∑ i ∈ I.erase p, v i * v i = ∑ i ∈ I, v i * v i :=
    Finset.add_sum_erase I (fun i => v i * v i) hp
  have hvp1 : v p * v p = 1 := by
    rcases entry_of_norm_two hp hv with h | h | h
    · rw [h]
      norm_num
    · exact absurd h hvp
    · rw [h]
      norm_num
  have hrest : ∑ i ∈ I.erase p, v i * v i = 1 := by linarith
  obtain ⟨q, hq, hvq⟩ : ∃ q ∈ I.erase p, v q ≠ 0 := by
    by_contra H
    push Not at H
    rw [Finset.sum_eq_zero fun i hi => by rw [H i hi, zero_mul]] at hrest
    exact absurd hrest (by norm_num)
  exact ⟨q, isPair_of_two hp (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq).symm hvp
    hvq hv⟩

private theorem exists_isPair {α : Type*} [DecidableEq α] {I : Finset α} {v : α → ℤ}
    (hv : ∑ i ∈ I, v i * v i = 2) : ∃ p q, IsPair I v p q := by
  obtain ⟨p, hp, hvp⟩ : ∃ p ∈ I, v p ≠ 0 := by
    by_contra H
    push Not at H
    rw [Finset.sum_eq_zero fun i hi => by rw [H i hi, zero_mul]] at hv
    exact absurd hv (by norm_num)
  exact ⟨p, exists_isPair_of_ne_zero hp hvp hv⟩

private theorem dot_of_isPair {α : Type*} [DecidableEq α] {I : Finset α} {u v : α → ℤ} {p q : α}
    (hu : IsPair I u p q) (hv : ∑ i ∈ I, v i * v i = 2) (huv : ∑ i ∈ I, u i * v i = 1) :
    (v p ≠ 0 ∧ v q = 0 ∧ u p * v p = 1) ∨ (v p = 0 ∧ v q ≠ 0 ∧ u q * v q = 1) := by
  have hs : ∑ i ∈ I, u i * v i = u p * v p + u q * v q :=
    sum_eq_add_of_two hu.left_mem hu.right_mem hu.ne (fun i => u i * v i)
      (fun i hi h1 h2 => by simp [hu.eq_zero i hi h1 h2])
  rw [hs] at huv
  have hup := hu.left
  have huq := hu.right
  have hvp := entry_of_norm_two hu.left_mem hv
  have hvq := entry_of_norm_two hu.right_mem hv
  generalize u p = A at *
  generalize u q = B at *
  generalize v p = C at *
  generalize v q = D at *
  rcases hup with rfl | rfl <;> rcases huq with rfl | rfl <;>
    rcases hvp with rfl | rfl | rfl <;> rcases hvq with rfl | rfl | rfl <;> omega

private theorem exists_ne_of_four_le {ι : Type*} [DecidableEq ι] {J : Finset ι}
    (hJ : 4 ≤ J.card) (j₀ j₁ j₂ : ι) : ∃ j ∈ J, j ≠ j₀ ∧ j ≠ j₁ ∧ j ≠ j₂ := by
  by_contra H
  push Not at H
  have hsub : J ⊆ {j₀, j₁, j₂} := by
    intro j hj
    by_cases h0 : j = j₀
    · rw [h0]
      exact Finset.mem_insert_self _ _
    by_cases h1 : j = j₁
    · rw [h1]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    rw [H j hj h0 h1]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have := (Finset.card_le_card hsub).trans Finset.card_le_three
  omega

private theorem exists_common_coord {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    {I : Finset α} {J : Finset ι} (hJ : 4 ≤ J.card) (c : ι → α → ℤ)
    (hc2 : ∀ j ∈ J, ∑ i ∈ I, c j i * c j i = 2)
    (hc1 : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∑ i ∈ I, c j i * c k i = 1) :
    ∃ a ∈ I, ∀ j ∈ J, c j a ≠ 0 := by
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, b, hab⟩ := exists_isPair (hc2 j₀ hj₀)
  by_contra H
  push Not at H
  obtain ⟨j₁, hj₁, h₁a⟩ := H a hab.left_mem
  obtain ⟨j₂, hj₂, h₂b⟩ := H b hab.right_mem
  have h10 : j₀ ≠ j₁ := by
    rintro rfl
    have := hab.left
    omega
  have h20 : j₀ ≠ j₂ := by
    rintro rfl
    have := hab.right
    omega
  have h₁b : c j₁ b ≠ 0 := by
    rcases dot_of_isPair hab (hc2 j₁ hj₁) (hc1 j₀ hj₀ j₁ hj₁ h10) with h | h
    · exact absurd h₁a h.1
    · exact h.2.1
  have h₂a : c j₂ a ≠ 0 := by
    rcases dot_of_isPair hab (hc2 j₂ hj₂) (hc1 j₀ hj₀ j₂ hj₂ h20) with h | h
    · exact h.1
    · exact absurd h₂b h.2.1
  obtain ⟨x, hbx⟩ := exists_isPair_of_ne_zero hab.right_mem h₁b (hc2 j₁ hj₁)
  have h12 : j₁ ≠ j₂ := by
    rintro rfl
    exact h₁b h₂b
  have h₂x : c j₂ x ≠ 0 := by
    rcases dot_of_isPair hbx (hc2 j₂ hj₂) (hc1 j₁ hj₁ j₂ hj₂ h12) with h | h
    · exact absurd h₂b h.1
    · exact h.2.1
  have hax : a ≠ x := by
    rintro rfl
    have := hbx.right
    omega
  have hax' : IsPair I (c j₂) a x :=
    isPair_of_two hab.left_mem hbx.right_mem hax h₂a h₂x (hc2 j₂ hj₂)
  obtain ⟨j₃, hj₃, h30, h31, h32⟩ := exists_ne_of_four_le hJ j₀ j₁ j₂
  have e0 := dot_of_isPair hab (hc2 j₃ hj₃) (hc1 j₀ hj₀ j₃ hj₃ h30.symm)
  have e1 := dot_of_isPair hbx (hc2 j₃ hj₃) (hc1 j₁ hj₁ j₃ hj₃ h31.symm)
  have e2 := dot_of_isPair hax' (hc2 j₃ hj₃) (hc1 j₂ hj₂ j₃ hj₃ h32.symm)
  omega

private theorem sign_of_eq_zero {δ η : ℤ} {s t : ℝ} (hδ : δ = 1 ∨ δ = -1) (hη : η = 1 ∨ η = -1)
    (hs : 0 < s) (ht : 0 < t) (h : 0 = (δ : ℝ) * s + (η : ℝ) * t) : η = -δ ∧ t = s := by
  rcases hδ with rfl | rfl <;> rcases hη with rfl | rfl <;> push_cast at h
  · exfalso
    linarith
  · exact ⟨rfl, by linarith⟩
  · exact ⟨by norm_num, by linarith⟩
  · exfalso
    linarith

theorem integral_gram_three_common_rows {α ι : Type*} [DecidableEq α] [Fintype ι] [DecidableEq ι]
    (I : Finset α) (o : α) (ho : o ∈ I) (hr : 5 ≤ Fintype.card ι)
    (b : ι → α → ℤ) (hbo : ∀ j, b j o = -1)
    (hgram : ∀ j k, ∑ i ∈ I, b j i * b k i = 3 + if j = k then 1 else 0)
    (d : α → ℝ) (hd : ∀ i ∈ I, 0 < d i) (hann : ∀ j, ∑ i ∈ I, (b j i : ℝ) * d i = 0) :
    ∃ (i₁ i₂ : α) (k : ι → α) (δ₁ δ₂ ε : ℤ),
      i₁ ∈ I ∧ i₂ ∈ I ∧ (∀ j, k j ∈ I) ∧
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      i₁ ≠ o ∧ i₂ ≠ o ∧ i₁ ≠ i₂ ∧ Function.Injective k ∧
      (∀ j, k j ≠ o ∧ k j ≠ i₁ ∧ k j ≠ i₂) ∧
      (∀ j, ∀ i ∈ I, b j i = -(if i = o then 1 else 0) + δ₁ * (if i = i₁ then 1 else 0) +
          δ₂ * (if i = i₂ then 1 else 0) + ε * (if i = k j then 1 else 0)) ∧
      (∀ j j', d (k j) = d (k j')) := by
  obtain ⟨R⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨J, hJ⟩ : ∃ J : Finset ι, J = Finset.univ.erase R := ⟨_, rfl⟩
  have hmemJ : ∀ j, j ∈ J ↔ j ≠ R := fun j => by simp [hJ]
  have hJcard : 4 ≤ J.card := by
    rw [hJ, Finset.card_erase_of_mem (Finset.mem_univ R), Finset.card_univ]
    omega
  obtain ⟨c, hc⟩ : ∃ c : ι → α → ℤ, ∀ j i, c j i = b j i - b R i := ⟨_, fun _ _ => rfl⟩
  have hco : ∀ j, c j o = 0 := fun j => by rw [hc, hbo, hbo, sub_self]
  have hRR : ∑ i ∈ I, b R i * b R i = 4 := by
    rw [hgram, ite_eq_left rfl]
    norm_num
  have hgc : ∀ j k, ∑ i ∈ I, c j i * c k i =
      (∑ i ∈ I, b j i * b k i) - (∑ i ∈ I, b j i * b R i) - (∑ i ∈ I, b R i * b k i) +
        ∑ i ∈ I, b R i * b R i := by
    intro j k
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, hc]; ring
  have hc2 : ∀ j ∈ J, ∑ i ∈ I, c j i * c j i = 2 := by
    intro j hj
    have hjR := (hmemJ j).mp hj
    rw [hgc, hRR, hgram j j, hgram j R, hgram R j, ite_eq_left rfl, ite_eq_right hjR,
      ite_eq_right (Ne.symm hjR)]
    norm_num
  have hc1 : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∑ i ∈ I, c j i * c k i = 1 := by
    intro j hj k hk hjk
    rw [hgc, hRR, hgram j k, hgram j R, hgram R k, ite_eq_right hjk,
      ite_eq_right ((hmemJ j).mp hj), ite_eq_right (Ne.symm ((hmemJ k).mp hk))]
    norm_num
  have hbc : ∀ j ∈ J, ∑ i ∈ I, b R i * c j i = -1 := by
    intro j hj
    have e : ∑ i ∈ I, b R i * c j i = (∑ i ∈ I, b R i * b j i) - ∑ i ∈ I, b R i * b R i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; ring
    rw [e, hRR, hgram R j, ite_eq_right (Ne.symm ((hmemJ j).mp hj))]
    norm_num
  have hcd : ∀ j, ∑ i ∈ I, (c j i : ℝ) * d i = 0 := by
    intro j
    have e : ∑ i ∈ I, (c j i : ℝ) * d i =
        (∑ i ∈ I, (b j i : ℝ) * d i) - ∑ i ∈ I, (b R i : ℝ) * d i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hc]; push_cast; ring
    rw [e, hann, hann, sub_zero]
  obtain ⟨a, haI, ha⟩ := exists_common_coord hJcard c hc2 hc1
  have hx : ∀ j, ∃ x, j ∈ J → IsPair I (c j) a x := by
    intro j
    by_cases hj : j ∈ J
    · obtain ⟨x, hx⟩ := exists_isPair_of_ne_zero haI (ha j hj) (hc2 j hj)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨a, fun h => absurd h hj⟩
  choose x hx using hx
  obtain ⟨j₀, hj₀⟩ : J.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨δ, hδdef⟩ : ∃ δ, c j₀ a = δ := ⟨_, rfl⟩
  have hδ1 : δ = 1 ∨ δ = -1 := hδdef ▸ (hx j₀ hj₀).left
  have hδ : ∀ j ∈ J, c j a = δ := by
    intro j hj
    by_cases hjj : j₀ = j
    · rw [← hjj, hδdef]
    rcases dot_of_isPair (hx j₀ hj₀) (hc2 j hj) (hc1 j₀ hj₀ j hj hjj) with h | h
    · have := Int.eq_one_or_neg_one_of_mul_eq_one' h.2.2
      rw [hδdef] at this
      omega
    · exact absurd h.1 (ha j hj)
  have hxinj : ∀ j ∈ J, ∀ k ∈ J, x j = x k → j = k := by
    intro j hj k hk hjk
    by_contra hne
    rcases dot_of_isPair (hx j hj) (hc2 k hk) (hc1 j hj k hk hne) with h | h
    · have hxk := (hx k hk).right
      rw [← hjk] at hxk
      have := h.2.1
      omega
    · exact absurd h.1 (ha k hk)
  have hxo : ∀ j ∈ J, x j ≠ o := by
    intro j hj h
    have hcx := (hx j hj).right
    rw [h, hco] at hcx
    omega
  have hao : a ≠ o := fun h => ha j₀ hj₀ (h ▸ hco j₀)
  have hxd : ∀ j ∈ J, c j (x j) = -δ ∧ d (x j) = d a := by
    intro j hj
    have hp := hx j hj
    have hs : ∑ i ∈ I, (c j i : ℝ) * d i = (c j a : ℝ) * d a + (c j (x j) : ℝ) * d (x j) :=
      sum_eq_add_of_two haI hp.right_mem hp.ne (fun i => (c j i : ℝ) * d i)
        (fun i hi h1 h2 => by simp [hp.eq_zero i hi h1 h2])
    rw [hcd j, hδ j hj] at hs
    exact sign_of_eq_zero hδ1 hp.right (hd a haI) (hd (x j) hp.right_mem) hs
  have hbRx : ∀ j ∈ J, b R (x j) = b R a + δ := by
    intro j hj
    have hp := hx j hj
    have hs : ∑ i ∈ I, b R i * c j i = b R a * c j a + b R (x j) * c j (x j) :=
      sum_eq_add_of_two haI hp.right_mem hp.ne (fun i => b R i * c j i)
        (fun i hi h1 h2 => by simp [hp.eq_zero i hi h1 h2])
    rw [hbc j hj, hδ j hj, (hxd j hj).1] at hs
    rcases hδ1 with rfl | rfl <;> linarith
  have hsplit_o : b R o * b R o + ∑ i ∈ I.erase o, b R i * b R i = ∑ i ∈ I, b R i * b R i :=
    Finset.add_sum_erase I (fun i => b R i * b R i) ho
  rw [hRR, hbo] at hsplit_o
  have hzero : b R a + δ = 0 := by
    by_contra hz
    have hsub : J.image x ⊆ I.erase o := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_erase.mpr ⟨hxo j hj, (hx j hj).right_mem⟩
    have hcard : (J.image x).card = J.card :=
      Finset.card_image_of_injOn fun j hj k hk hjk => hxinj j hj k hk hjk
    have hge : (J.image x).card • (1 : ℤ) ≤ ∑ i ∈ J.image x, b R i * b R i := by
      apply Finset.card_nsmul_le_sum
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      rw [hbRx j hj]
      exact one_le_mul_self_of_ne_zero hz
    have hle : ∑ i ∈ J.image x, b R i * b R i ≤ ∑ i ∈ I.erase o, b R i * b R i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => mul_self_nonneg _
    rw [hcard, nsmul_eq_mul, mul_one] at hge
    have h4 : (4 : ℤ) ≤ J.card := by exact_mod_cast hJcard
    linarith
  have hbRa : b R a = -δ := by linarith
  have hbRx0 : ∀ j ∈ J, b R (x j) = 0 := fun j hj => by rw [hbRx j hj]; linarith
  have haIo : a ∈ I.erase o := Finset.mem_erase.mpr ⟨hao, haI⟩
  have hsplit_a : b R a * b R a + ∑ i ∈ (I.erase o).erase a, b R i * b R i =
      ∑ i ∈ I.erase o, b R i * b R i :=
    Finset.add_sum_erase (I.erase o) (fun i => b R i * b R i) haIo
  have hRa2 : b R a * b R a = 1 := by
    rw [hbRa, neg_mul_neg]
    rcases hδ1 with rfl | rfl <;> norm_num
  have hrest : ∑ i ∈ (I.erase o).erase a, b R i * b R i = 2 := by linarith
  obtain ⟨i₁, i₂, hi⟩ := exists_isPair hrest
  have hi₁a : i₁ ≠ a := Finset.ne_of_mem_erase hi.left_mem
  have hi₁o : i₁ ≠ o := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi.left_mem)
  have hi₁I : i₁ ∈ I := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi.left_mem)
  have hi₂a : i₂ ≠ a := Finset.ne_of_mem_erase hi.right_mem
  have hi₂o : i₂ ≠ o := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi.right_mem)
  have hi₂I : i₂ ∈ I := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi.right_mem)
  have hbR : ∀ i ∈ I, b R i = -(if i = o then 1 else 0) + b R i₁ * (if i = i₁ then 1 else 0) +
      b R i₂ * (if i = i₂ then 1 else 0) + -δ * (if i = a then 1 else 0) := by
    intro i hi'
    by_cases hio : i = o
    · rw [hio, ite_eq_left rfl, ite_eq_right (Ne.symm hi₁o), ite_eq_right (Ne.symm hi₂o),
        ite_eq_right (Ne.symm hao), hbo]
      ring
    by_cases hia : i = a
    · rw [hia, ite_eq_right hao, ite_eq_right (Ne.symm hi₁a), ite_eq_right (Ne.symm hi₂a),
        ite_eq_left rfl, hbRa]
      ring
    by_cases hi1 : i = i₁
    · rw [hi1, ite_eq_right hi₁o, ite_eq_left rfl, ite_eq_right hi.ne, ite_eq_right hi₁a]
      ring
    by_cases hi2 : i = i₂
    · rw [hi2, ite_eq_right hi₂o, ite_eq_right (Ne.symm hi.ne), ite_eq_left rfl, ite_eq_right hi₂a]
      ring
    rw [ite_eq_right hio, ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hia,
      hi.eq_zero i (Finset.mem_erase.mpr ⟨hia, Finset.mem_erase.mpr ⟨hio, hi'⟩⟩) hi1 hi2]
    ring
  have hcj : ∀ j ∈ J, ∀ i ∈ I,
      c j i = δ * (if i = a then 1 else 0) + -δ * (if i = x j then 1 else 0) := by
    intro j hj i hi'
    have hp := hx j hj
    by_cases hia : i = a
    · rw [hia, ite_eq_left rfl, ite_eq_right hp.ne, hδ j hj]
      ring
    by_cases hix : i = x j
    · rw [hix, ite_eq_right (Ne.symm hp.ne), ite_eq_left rfl, (hxd j hj).1]
      ring
    rw [ite_eq_right hia, ite_eq_right hix, hp.eq_zero i hi' hia hix]
    ring
  obtain ⟨k, hkR, hkx⟩ : ∃ k : ι → α, k R = a ∧ ∀ j, j ≠ R → k j = x j :=
    ⟨fun j => if j = R then a else x j, ite_eq_left rfl, fun j hj => ite_eq_right hj⟩
  have hkd : ∀ j, d (k j) = d a := by
    intro j
    by_cases hj : j = R
    · rw [hj, hkR]
    · rw [hkx j hj]
      exact (hxd j ((hmemJ j).mpr hj)).2
  refine ⟨i₁, i₂, k, b R i₁, b R i₂, -δ, hi₁I, hi₂I, ?_, hi.left, hi.right, ?_, hi₁o, hi₂o, hi.ne,
    ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = R
    · rw [hj, hkR]
      exact haI
    · rw [hkx j hj]
      exact (hx j ((hmemJ j).mpr hj)).right_mem
  · omega
  · intro j j' hjj
    by_cases hj : j = R <;> by_cases hj' : j' = R
    · rw [hj, hj']
    · rw [hj, hkR, hkx j' hj'] at hjj
      exact absurd hjj (hx j' ((hmemJ j').mpr hj')).ne
    · rw [hj', hkR, hkx j hj] at hjj
      exact absurd hjj.symm (hx j ((hmemJ j).mpr hj)).ne
    · rw [hkx j hj, hkx j' hj'] at hjj
      exact hxinj j ((hmemJ j).mpr hj) j' ((hmemJ j').mpr hj') hjj
  · intro j
    by_cases hj : j = R
    · rw [hj, hkR]
      exact ⟨hao, Ne.symm hi₁a, Ne.symm hi₂a⟩
    · rw [hkx j hj]
      have hjJ := (hmemJ j).mpr hj
      have h0 := hbRx0 j hjJ
      have h1 := hi.left
      have h2 := hi.right
      refine ⟨hxo j hjJ, fun h => ?_, fun h => ?_⟩
      · rw [h] at h0
        omega
      · rw [h] at h0
        omega
  · intro j i hi'
    by_cases hj : j = R
    · rw [hj, hkR]
      exact hbR i hi'
    · rw [hkx j hj]
      have e : b j i = b R i + c j i := by rw [hc]; ring
      rw [e, hbR i hi', hcj j ((hmemJ j).mpr hj) i hi']
      ring
  · intro j j'
    rw [hkd j, hkd j']

theorem integral_gram_three_common_rows_fintype {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι] (o : α) (hr : 5 ≤ Fintype.card ι)
    (b : ι → α → ℤ) (hbo : ∀ j, b j o = -1)
    (hgram : ∀ j k, ∑ i, b j i * b k i = 3 + if j = k then 1 else 0)
    (d : α → ℝ) (hd : ∀ i, 0 < d i) (hann : ∀ j, ∑ i, (b j i : ℝ) * d i = 0) :
    ∃ (i₁ i₂ : α) (k : ι → α) (δ₁ δ₂ ε : ℤ),
      (δ₁ = 1 ∨ δ₁ = -1) ∧ (δ₂ = 1 ∨ δ₂ = -1) ∧ (ε = 1 ∨ ε = -1) ∧
      i₁ ≠ o ∧ i₂ ≠ o ∧ i₁ ≠ i₂ ∧ Function.Injective k ∧
      (∀ j, k j ≠ o ∧ k j ≠ i₁ ∧ k j ≠ i₂) ∧
      (∀ j i, b j i = -(if i = o then 1 else 0) + δ₁ * (if i = i₁ then 1 else 0) +
          δ₂ * (if i = i₂ then 1 else 0) + ε * (if i = k j then 1 else 0)) ∧
      (∀ j j', d (k j) = d (k j')) := by
  obtain ⟨i₁, i₂, k, δ₁, δ₂, ε, -, -, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    integral_gram_three_common_rows Finset.univ o (Finset.mem_univ o) hr b hbo hgram d
      (fun i _ => hd i) hann
  exact ⟨i₁, i₂, k, δ₁, δ₂, ε, h1, h2, h3, h4, h5, h6, h7, h8,
    fun j i => h9 j i (Finset.mem_univ i), h10⟩

end CFSG.RankTwoShapes
