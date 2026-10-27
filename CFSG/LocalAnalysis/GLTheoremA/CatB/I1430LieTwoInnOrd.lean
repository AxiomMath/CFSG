module

public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20LieOrd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

private theorem profile_exp_eq_three {m N : ℕ} {Z : ℕ → Prop} (hP : Profile m N Z)
    (hm : m = 360) : N = 3 := by
  obtain ⟨r, hr, hmr⟩ := hP.two
  exact eq_of_two_pow_mul_odd hr (by decide : Odd 45)
    ((hmr.symm.trans hm).trans (by norm_num : (360 : ℕ) = 2 ^ 3 * 45))

private theorem card_eq_two_pow' {q : TauCeti.PrimePower} (hp : q.p = 2) :
    q.card = 2 ^ q.exponent := by
  rw [TauCeti.PrimePower.card_def, hp]

private theorem ordTwistedA_eq_orderTwistedA' (n Q : ℕ) (hQ : 1 ≤ Q) :
    ordTwistedA n Q = orderTwistedA n Q := by
  unfold ordTwistedA orderTwistedA
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
  have hc : ((Q ^ i : ℕ) : ℤ) = (Q : ℤ) ^ i := Nat.cast_pow Q i
  rcases Nat.even_or_odd i with hi | hi
  · rw [if_pos hi, hi.neg_one_pow]
    omega
  · rw [if_neg (Nat.not_even_iff_odd.2 hi), hi.neg_one_pow]
    omega

theorem not_mem_evenOrders_360 : (360 : ℕ) ∉ evenOrdersExceptUnitarySp4 := by
  rintro (⟨f, hf, h⟩ | hm)
  · rcases h with ⟨n, hn, hnf, hm⟩ | ⟨n, hn, hm⟩ | ⟨n, hn, hm | hm⟩ | ⟨hf2, hm⟩ | hm | hm | hm |
      hm | hm | hm | ⟨hodd, h3, hm | hm⟩
    · have hN := profile_exp_eq_three (profile_ordA hn hf) hm.symm
      have hn2 : n ≤ 2 := by
        by_contra hlt
        push Not at hlt
        have h6 : 6 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
        have := Nat.le_mul_of_pos_left (n * (n + 1) / 2) hf
        omega
      interval_cases n
      · have hf3 : f = 3 := by norm_num at hN; omega
        subst hf3
        revert hm
        decide +kernel
      · have hf1 : f = 1 := by norm_num at hN; omega
        subst hf1
        revert hm
        decide +kernel
    · have hN := profile_exp_eq_three (profile_ordBC hf) hm.symm
      have h9 : 9 ≤ n * n := Nat.mul_le_mul hn hn
      have := Nat.le_mul_of_pos_left (n * n) hf
      omega
    · have hN := profile_exp_eq_three (profile_ordD (by omega) hf) hm.symm
      have h12 : 12 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega : 3 ≤ n - 1)
      have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
      omega
    · have hN := profile_exp_eq_three (profile_ordTwistedD (by omega) hf) hm.symm
      have h12 : 12 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega : 3 ≤ n - 1)
      have := Nat.le_mul_of_pos_left (n * (n - 1)) hf
      omega
    · have hN := profile_exp_eq_three (profile_ordG2 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordTrialityD4 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordF4 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordE6 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordTwistedE6 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordE7 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordE8 hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordSuzuki hf) hm.symm
      omega
    · have hN := profile_exp_eq_three (profile_ordTwistedF4 hf) hm.symm
      omega
  · rw [Set.mem_singleton_iff] at hm
    revert hm
    unfold ordTits
    norm_num

private theorem false_of_orderBC_two_360 {q : TauCeti.PrimePower} (hp : q.p = 2)
    (h : orderBC 2 q.card = 360) : False := by
  have h2 : ordBC 2 (2 ^ q.exponent) = 360 := by rw [← card_eq_two_pow' hp]; exact h
  have hN := profile_exp_eq_three (profile_ordBC (n := 2) q.exponent_pos) h2
  omega

private theorem false_of_twistedA_360 {n : ℕ} {q : TauCeti.PrimePower} (hn : 2 ≤ n)
    (hv : n = 2 → 3 ≤ q.card) (hp : q.p = 2) (h : orderTwistedA n q.card = 360) : False := by
  have hq : q.card = 2 ^ q.exponent := card_eq_two_pow' hp
  have h2 : ordTwistedA n (2 ^ q.exponent) = 360 := by
    rw [← hq, ordTwistedA_eq_orderTwistedA' n _ (by rw [hq]; exact Nat.one_le_two_pow)]
    exact h
  have hN := profile_exp_eq_three (profile_ordTwistedA hn q.exponent_pos) h2
  have hn2 : n = 2 := by
    by_contra hne
    have h3 : 3 ≤ n := by omega
    have h6 : 6 ≤ n * (n + 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by nlinarith)
    have := Nat.le_mul_of_pos_left (n * (n + 1) / 2) q.exponent_pos
    omega
  subst hn2
  have hg : q.exponent = 1 := by norm_num at hN; omega
  have h3 := hv rfl
  rw [hq, hg] at h3
  omega

theorem false_of_lieOrderFormula_360 {e : TauCeti.LieTypeIndex} (he : e.Valid)
    (hc : e.characteristic = 2) (h : lieOrderFormula e = 360) : False := by
  have hs := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, Or.inl ⟨n, hs.1, ?_, ?_⟩⟩)
    · intro hnf
      have h4 : 4 ≤ q.card := hs.2 (Prod.mk.inj hnf).1
      rw [card_eq_two_pow' hp, (Prod.mk.inj hnf).2] at h4
      omega
    · rw [← card_eq_two_pow' hp]
      exact h.symm
  | twistedA n q =>
    have hp : q.p = 2 := by simpa using hc
    exact false_of_twistedA_360 hs.1 hs.2 hp h
  | B n q =>
    have hp : q.p = 2 := by simpa using hc
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by have := hs.1; omega
      exact false_of_orderBC_two_360 hp h
    · refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
      right
      left
      exact ⟨n, h3, by rw [← card_eq_two_pow' hp]; exact h.symm⟩
  | C n q =>
    have hp : q.p = 2 := by simpa using hc
    exact absurd hp hs.2
  | D n q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 2 right
    left
    exact ⟨n, hs, Or.inl (by rw [← card_eq_two_pow' hp]; exact h.symm)⟩
  | twistedD n q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 2 right
    left
    exact ⟨n, hs, Or.inr (by rw [← card_eq_two_pow' hp]; exact h.symm)⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 6 right
    left
    rw [← card_eq_two_pow' hp]
    exact h.symm
  | E7 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 8 right
    left
    rw [← card_eq_two_pow' hp]
    exact h.symm
  | E8 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 9 right
    left
    rw [← card_eq_two_pow' hp]
    exact h.symm
  | F4 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 5 right
    left
    rw [← card_eq_two_pow' hp]
    exact h.symm
  | G2 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 3 right
    left
    refine ⟨?_, by rw [← card_eq_two_pow' hp]; exact h.symm⟩
    by_contra hlt
    have h3 : 3 ≤ q.card := hs
    rw [card_eq_two_pow' hp, (by have := q.exponent_pos; omega : q.exponent = 1)] at h3
    omega
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 7 right
    left
    rw [← card_eq_two_pow' hp]
    exact h.symm
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hc
    refine not_mem_evenOrders_360 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 4 right
    left
    rw [← card_eq_two_pow' hp]
    exact h.symm
  | suzuki k =>
    refine not_mem_evenOrders_360 (Or.inl ⟨2 * k + 1, by omega, ?_⟩)
    iterate 10 right
    exact ⟨odd_two_mul_add_one k, by omega, Or.inl h.symm⟩
  | reeG2 k => simp at hc
  | reeF4 k =>
    refine not_mem_evenOrders_360 (Or.inl ⟨2 * k + 1, by omega, ?_⟩)
    iterate 10 right
    exact ⟨odd_two_mul_add_one k, by omega, Or.inr h.symm⟩
  | tits =>
    exact not_mem_evenOrders_360 (Or.inr h.symm)

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end
