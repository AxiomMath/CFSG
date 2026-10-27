module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open Finset

variable {A : Type*} [Group A] [Fintype A] {ι : Type*} [Fintype ι]

@[expose] noncomputable def nOut (h : ι → Subgroup A) (w : ι → ℕ) (a : A) : ℕ :=
  open Classical in ∑ i, if a ∈ h i then 0 else w i

omit [Fintype A] in
theorem nOut_one (h : ι → Subgroup A) (w : ι → ℕ) : nOut h w 1 = 0 := by
  simp [nOut]

private theorem card_filter_mem (H : Subgroup A) [DecidablePred (· ∈ H)] :
    #(univ.filter fun a => a ∈ H) = Nat.card H := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem three_mul_card_not_mem (H : Subgroup A) [DecidablePred (· ∈ H)]
    (h3 : H.index = 3) : 3 * #(univ.filter fun a => a ∉ H) = 2 * Fintype.card A := by
  have hc := H.card_mul_index
  rw [h3, Nat.card_eq_fintype_card (α := A)] at hc
  have hs := card_filter_add_card_filter_not (s := (univ : Finset A)) (fun a => a ∈ H)
  rw [card_univ, card_filter_mem] at hs
  omega

private theorem nine_mul_card_inf {H K : Subgroup A} [H.Normal] (hH : H.index = 3)
    (hK : K.index = 3) (hne : H ≠ K) : Nat.card ↥(H ⊓ K) * 9 = Fintype.card A := by
  have hrel : H.relIndex K = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (hH ▸ H.relIndex_dvd_index_of_normal K) with h | h
    · have hKH := Subgroup.relIndex_eq_one.1 h
      have hcH := H.card_mul_index
      have hcK := K.card_mul_index
      rw [hH] at hcH
      rw [hK] at hcK
      exact absurd (Subgroup.eq_of_le_of_card_ge hKH (by omega)).symm hne
    · exact h
  have hc := (H ⊓ K).card_mul_index
  rwa [Subgroup.index_inf, hrel, hK, Nat.card_eq_fintype_card (α := A)] at hc

private theorem nine_mul_card_not_mem_two {H K : Subgroup A} [H.Normal]
    [DecidablePred (· ∈ H)] [DecidablePred (· ∈ K)] (hH : H.index = 3) (hK : K.index = 3)
    (hne : H ≠ K) :
    9 * #(univ.filter fun a => a ∉ H ∧ a ∉ K) = 4 * Fintype.card A := by
  classical
  have h9 := nine_mul_card_inf hH hK hne
  have h3H := three_mul_card_not_mem H hH
  have h3K := three_mul_card_not_mem K hK
  have hsH := card_filter_add_card_filter_not (s := (univ : Finset A)) (fun a => a ∈ H)
  have hsK := card_filter_add_card_filter_not (s := (univ : Finset A)) (fun a => a ∈ K)
  have hs := card_filter_add_card_filter_not (s := (univ : Finset A)) (fun a => a ∈ H ∨ a ∈ K)
  have hu := card_union_add_card_inter (univ.filter fun a => a ∈ H) (univ.filter fun a => a ∈ K)
  rw [← filter_or, ← filter_and] at hu
  have hinf : #(univ.filter fun a => a ∈ H ∧ a ∈ K) = Nat.card ↥(H ⊓ K) := by
    rw [← card_filter_mem (H ⊓ K)]
    exact congrArg card (filter_congr fun a _ => Subgroup.mem_inf.symm)
  have hnot : #(univ.filter fun a => a ∉ H ∧ a ∉ K) =
      #(univ.filter fun a => ¬ (a ∈ H ∨ a ∈ K)) :=
    congrArg card (filter_congr fun a _ => not_or.symm)
  rw [card_univ] at hsH hsK hs
  omega

private theorem ite_eq_boole_mul (P : Prop) [Decidable P] (x : ℕ) :
    (if P then 0 else x) = (if ¬ P then 1 else 0) * x := by
  by_cases hP : P <;> simp [hP]

theorem three_mul_sum_nOut (h : ι → Subgroup A) (w : ι → ℕ) (h3 : ∀ i, (h i).index = 3) :
    3 * ∑ a, nOut h w a = 2 * Fintype.card A * ∑ i, w i := by
  classical
  simp only [nOut]
  rw [sum_comm, mul_sum, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  simp_rw [ite_eq_boole_mul, ← sum_mul, sum_boole, Nat.cast_id]
  rw [← mul_assoc, three_mul_card_not_mem (h i) (h3 i)]

theorem nine_mul_sum_nOut_sq (h : ι → Subgroup A) (w : ι → ℕ) (h3 : ∀ i, (h i).index = 3)
    (hn : ∀ i, (h i).Normal) (hinj : Function.Injective h) :
    9 * ∑ a, nOut h w a ^ 2 =
      4 * Fintype.card A * (∑ i, w i) ^ 2 + 2 * Fintype.card A * ∑ i, w i ^ 2 := by
  classical
  have hpair : ∀ i j, 9 * #(univ.filter fun a => a ∉ h i ∧ a ∉ h j) =
      4 * Fintype.card A + if i = j then 2 * Fintype.card A else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h3' := three_mul_card_not_mem (h i) (h3 i)
      simp only [and_self, if_true]
      omega
    · haveI := hn i
      rw [if_neg hij, add_zero]
      exact nine_mul_card_not_mem_two (h3 i) (h3 j) (hinj.ne hij)
  have hsq : ∀ a, nOut h w a ^ 2 =
      ∑ i, ∑ j, (if a ∉ h i ∧ a ∉ h j then 1 else 0) * (w i * w j) := by
    intro a
    simp only [nOut, sq, ite_eq_boole_mul, sum_mul_sum]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    by_cases hi : a ∈ h i <;> by_cases hj : a ∈ h j <;> simp [hi, hj]
  set n := Fintype.card A
  have hcol : ∀ i j, ∑ a, (if a ∉ h i ∧ a ∉ h j then 1 else 0) * (w i * w j) =
      #(univ.filter fun a => a ∉ h i ∧ a ∉ h j) * (w i * w j) := fun i j => by
    rw [← sum_mul, sum_boole, Nat.cast_id]
  have hrow : ∀ i, ∑ j, (4 * n + if i = j then 2 * n else 0) * (w i * w j) =
      4 * n * (w i * ∑ j, w j) + 2 * n * w i ^ 2 := by
    intro i
    simp only [add_mul, sum_add_distrib]
    congr 1
    · rw [mul_sum, mul_sum]
    · rw [sum_eq_single i (fun j _ hji => by simp [Ne.symm hji]) (by simp)]
      simp only [if_true]
      ring
  calc 9 * ∑ a, nOut h w a ^ 2
      = 9 * ∑ i, ∑ j, ∑ a, (if a ∉ h i ∧ a ∉ h j then 1 else 0) * (w i * w j) := by
        simp_rw [hsq]
        rw [sum_comm]
        exact congrArg _ (sum_congr rfl fun i _ => sum_comm)
    _ = ∑ i, ∑ j, (4 * n + if i = j then 2 * n else 0) * (w i * w j) := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun j _ => ?_
        rw [hcol, ← mul_assoc, hpair]
    _ = 4 * n * (∑ i, w i) ^ 2 + 2 * n * ∑ i, w i ^ 2 := by
        simp_rw [hrow]
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← sum_mul, sq]

theorem sum_le_sum_sq (w : ι → ℕ) : ∑ i, w i ≤ ∑ i, w i ^ 2 :=
  sum_le_sum fun i _ => Nat.le_self_pow (by norm_num) (w i)

private theorem sums_of_two_three (N : A → ℕ) (h1 : N 1 = 0)
    (h23 : ∀ a, a ≠ 1 → N a = 2 ∨ N a = 3) :
    ∃ E : ℕ, ∑ a, N a = 2 * (Fintype.card A - 1) + E ∧
      ∑ a, N a ^ 2 = 4 * (Fintype.card A - 1) + 5 * E := by
  classical
  have hne : #(univ.filter fun a : A => a ≠ 1) = Fintype.card A - 1 := by
    rw [filter_ne', card_erase_of_mem (mem_univ _), card_univ]
  refine ⟨#(univ.filter fun a => N a = 3), ?_, ?_⟩
  · have hN : ∀ a, N a = 2 * (if a ≠ 1 then 1 else 0) + (if N a = 3 then 1 else 0) := by
      intro a
      by_cases ha : a = 1
      · subst ha
        simp [h1]
      · rcases h23 a ha with h | h <;> simp [ha, h]
    rw [sum_congr rfl fun a _ => hN a, sum_add_distrib, ← mul_sum, sum_boole, sum_boole,
      Nat.cast_id, Nat.cast_id, hne]
  · have hN : ∀ a, N a ^ 2 = 4 * (if a ≠ 1 then 1 else 0) + 5 * (if N a = 3 then 1 else 0) := by
      intro a
      by_cases ha : a = 1
      · subst ha
        simp [h1]
      · rcases h23 a ha with h | h <;> simp [ha, h]
    rw [sum_congr rfl fun a _ => hN a, sum_add_distrib, ← mul_sum, ← mul_sum, sum_boole,
      sum_boole, Nat.cast_id, Nat.cast_id, hne]

theorem false_of_nOut_const (h : ι → Subgroup A) (w : ι → ℕ) (h3 : ∀ i, (h i).index = 3)
    {c : ℕ} (hc : ¬ 3 ∣ c) (hval : ∀ a, a ≠ 1 → nOut h w a = 3 * c)
    (h27 : 27 ∣ Fintype.card A) : False := by
  classical
  have hm := three_mul_sum_nOut h w h3
  obtain ⟨m, hm1⟩ : ∃ m, Fintype.card A = m + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  have hsum : ∑ a, nOut h w a = 3 * c * m := by
    rw [← sum_erase_add _ _ (mem_univ (1 : A)), nOut_one, add_zero,
      sum_congr rfl fun a ha => hval a (ne_of_mem_erase ha), sum_const,
      card_erase_of_mem (mem_univ _), card_univ, hm1, smul_eq_mul, Nat.add_sub_cancel, mul_comm]
  obtain ⟨k, hk⟩ := h27
  rw [hsum, hm1] at hm
  have h9 : 27 ∣ 9 * (c * m) := ⟨2 * k * ∑ i, w i, by
    calc 9 * (c * m) = 3 * (3 * c * m) := by ring
      _ = 2 * (m + 1) * ∑ i, w i := hm
      _ = 27 * (2 * k * ∑ i, w i) := by rw [← hm1, hk]; ring⟩
  have h3cm : 3 ∣ c * m := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using h9)
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3cm with h' | h'
  · exact hc h'
  · omega

theorem false_of_nOut_two_three (h : ι → Subgroup A) (w : ι → ℕ) (h3 : ∀ i, (h i).index = 3)
    (hn : ∀ i, (h i).Normal) (hinj : Function.Injective h)
    (hval : ∀ a, a ≠ 1 → nOut h w a = 2 ∨ nOut h w a = 3) (hM : ∑ i, w i ≤ 4)
    (hA : Fintype.card A = 27 ∨ Fintype.card A = 81) : False := by
  obtain ⟨E, hE1, hE2⟩ := sums_of_two_three (nOut h w) (nOut_one h w) hval
  have m1 := three_mul_sum_nOut h w h3
  have m2 := nine_mul_sum_nOut_sq h w h3 hn hinj
  have hMS := sum_le_sum_sq w
  rw [hE1] at m1
  rw [hE2] at m2
  generalize ∑ i, w i = M at m1 m2 hM hMS
  generalize ∑ i, w i ^ 2 = S at m2 hMS
  rcases hA with hA | hA <;> rw [hA] at m1 m2 <;> interval_cases M <;> omega

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
