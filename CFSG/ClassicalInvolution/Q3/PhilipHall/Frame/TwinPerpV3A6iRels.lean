module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6iEval

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem foldl_curtisEval (gens : List G) (w : List ℕ) (acc : G) :
    w.foldl (fun acc k => acc * if k % 2 = 0 then gens.getD (k / 2) 1
      else (gens.getD (k / 2) 1)⁻¹) acc = acc * curtisEval gens w := by
  induction w generalizing acc with
  | nil => simp [curtisEval]
  | cons k w ih =>
    have h1 : curtisEval gens (k :: w) = (if k % 2 = 0 then gens.getD (k / 2) 1
        else (gens.getD (k / 2) 1)⁻¹) * curtisEval gens w := by
      show List.foldl _ 1 (k :: w) = _
      rw [List.foldl_cons, ih, one_mul]
    rw [List.foldl_cons, ih, h1, mul_assoc]

theorem curtisEval_nil (gens : List G) : curtisEval gens [] = 1 := rfl

theorem curtisEval_cons (gens : List G) (k : ℕ) (w : List ℕ) :
    curtisEval gens (k :: w) = (if k % 2 = 0 then gens.getD (k / 2) 1
      else (gens.getD (k / 2) 1)⁻¹) * curtisEval gens w := by
  show List.foldl _ 1 (k :: w) = _
  rw [List.foldl_cons, foldl_curtisEval, one_mul]

theorem curtisEval_append (gens : List G) (u v : List ℕ) :
    curtisEval gens (u ++ v) = curtisEval gens u * curtisEval gens v := by
  induction u with
  | nil => simp [curtisEval_nil]
  | cons k u ih => rw [List.cons_append, curtisEval_cons, curtisEval_cons, ih, mul_assoc]

theorem curtisEval_single (gens : List G) (k : ℕ) :
    curtisEval gens [k] = if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹ := by
  rw [curtisEval_cons, curtisEval_nil, mul_one]

theorem curtisEval_invLetter (gens : List G) (k : ℕ) :
    curtisEval gens [curtisInvLetter k] = (curtisEval gens [k])⁻¹ := by
  rw [curtisEval_single, curtisEval_single, curtisInvLetter]
  by_cases hk : k % 2 = 0
  · have h1 : (k + 1) % 2 ≠ 0 := by omega
    have h2 : (k + 1) / 2 = k / 2 := by omega
    simp [hk, h1, h2]
  · have h1 : (k - 1) % 2 = 0 := by omega
    have h2 : (k - 1) / 2 = k / 2 := by omega
    simp [hk, h1, h2]

theorem curtisEval_invWord (gens : List G) (w : List ℕ) :
    curtisEval gens (curtisInvWord w) = (curtisEval gens w)⁻¹ := by
  induction w with
  | nil => simp [curtisInvWord, curtisEval_nil]
  | cons k w ih =>
    have e : curtisInvWord (k :: w) = curtisInvWord w ++ [curtisInvLetter k] := by
      simp [curtisInvWord]
    rw [e, curtisEval_append, ih, curtisEval_invLetter, curtisEval_cons (k := k) (w := w),
      curtisEval_single, mul_inv_rev]

theorem curtisEval_powWord (gens : List G) (w : List ℕ) (n : ℕ) :
    curtisEval gens (curtisPowWord w n) = (curtisEval gens w) ^ n := by
  induction n with
  | zero => simp [curtisPowWord, curtisEval_nil]
  | succ n ih =>
    have e : curtisPowWord w (n + 1) = w ++ curtisPowWord w n := by
      simp [curtisPowWord, List.replicate_succ]
    rw [e, curtisEval_append, ih, pow_succ']

theorem curtisEval_commWord (gens : List G) (u v : List ℕ) :
    curtisEval gens (curtisCommWord u v) = ⁅curtisEval gens u, curtisEval gens v⁆ := by
  simp only [curtisCommWord, curtisEval_append, curtisEval_invWord, commutatorElement_def,
    mul_assoc]

theorem curtisEval_letterA (gens : List G) (i : ℕ) :
    curtisEval gens [curtisLetterA i] = gens.getD (2 * i) 1 := by
  rw [curtisEval_single, curtisLetterA]
  have h1 : 4 * i % 2 = 0 := by omega
  have h2 : 4 * i / 2 = 2 * i := by omega
  simp [h1, h2]

theorem curtisEval_letterB (gens : List G) (i : ℕ) :
    curtisEval gens [curtisLetterB i] = gens.getD (2 * i + 1) 1 := by
  rw [curtisEval_single, curtisLetterB]
  have h1 : (4 * i + 2) % 2 = 0 := by omega
  have h2 : (4 * i + 2) / 2 = 2 * i + 1 := by omega
  simp [h1, h2]

theorem curtisEval_cons_letterA (gens : List G) (i : ℕ) (w : List ℕ) :
    curtisEval gens (curtisLetterA i :: w) = gens.getD (2 * i) 1 * curtisEval gens w := by
  have := curtisEval_append gens [curtisLetterA i] w
  rwa [curtisEval_letterA, List.singleton_append] at this

theorem curtisEval_cons_letterB (gens : List G) (i : ℕ) (w : List ℕ) :
    curtisEval gens (curtisLetterB i :: w) = gens.getD (2 * i + 1) 1 * curtisEval gens w := by
  have := curtisEval_append gens [curtisLetterB i] w
  rwa [curtisEval_letterB, List.singleton_append] at this

structure CurtisRelations (a b : ℕ → G) : Prop where
  rank_one : ∀ i < 4, a i ^ 2 = 1 ∧ b i ^ 2 = 1 ∧ (a i * b i) ^ 3 = 1
  non_adj : ∀ p ∈ ([(0, 2), (0, 3), (2, 3)] : List (ℕ × ℕ)),
    ⁅a p.1, a p.2⁆ = 1 ∧ ⁅a p.1, b p.2⁆ = 1 ∧ ⁅b p.1, a p.2⁆ = 1 ∧ ⁅b p.1, b p.2⁆ = 1
  adj : ∀ p ∈ ([(0, 1), (2, 1), (3, 1)] : List (ℕ × ℕ)),
    ⁅a p.1, b p.2⁆ = 1 ∧ ⁅b p.1, a p.2⁆ = 1 ∧ (a p.1 * a p.2) ^ 4 = 1 ∧ (b p.1 * b p.2) ^ 4 = 1 ∧
      a p.1 * b p.1 * a p.1 * a p.2 * (a p.1 * b p.1 * a p.1) = (a p.1 * a p.2) ^ 2 ∧
      a p.2 * b p.2 * a p.2 * a p.1 * (a p.2 * b p.2 * a p.2) = (a p.1 * a p.2) ^ 2

theorem curtisEval_two_a (gens : List G) (i j : ℕ) :
    curtisEval gens [curtisLetterA i, curtisLetterA j] =
      gens.getD (2 * i) 1 * gens.getD (2 * j) 1 := by
  simp only [curtisEval_cons_letterA, curtisEval_nil, mul_one]

theorem curtisEval_two_b (gens : List G) (i j : ℕ) :
    curtisEval gens [curtisLetterB i, curtisLetterB j] =
      gens.getD (2 * i + 1) 1 * gens.getD (2 * j + 1) 1 := by
  simp only [curtisEval_cons_letterB, curtisEval_nil, mul_one]

theorem curtisEval_two_ab (gens : List G) (i : ℕ) :
    curtisEval gens [curtisLetterA i, curtisLetterB i] =
      gens.getD (2 * i) 1 * gens.getD (2 * i + 1) 1 := by
  simp only [curtisEval_cons_letterA, curtisEval_cons_letterB, curtisEval_nil, mul_one]

theorem curtisEval_nWord (gens : List G) (i : ℕ) :
    curtisEval gens (curtisNWord i) =
      gens.getD (2 * i) 1 * gens.getD (2 * i + 1) 1 * gens.getD (2 * i) 1 := by
  simp only [curtisNWord, curtisEval_cons_letterA, curtisEval_cons_letterB, curtisEval_nil,
    mul_one, mul_assoc]

theorem curtisEval_nRel (gens : List G) (c d i j : ℕ) :
    curtisEval gens (curtisNRel c d i j) =
      (gens.getD (2 * c) 1 * gens.getD (2 * c + 1) 1 * gens.getD (2 * c) 1) * gens.getD (2 * d) 1 *
        (gens.getD (2 * c) 1 * gens.getD (2 * c + 1) 1 * gens.getD (2 * c) 1) *
          ((gens.getD (2 * i) 1 * gens.getD (2 * j) 1) ^ 2)⁻¹ := by
  simp only [curtisNRel, curtisEval_append, curtisEval_nWord, curtisEval_invWord,
    curtisEval_powWord, curtisEval_two_a, curtisEval_letterA, List.cons_append, List.nil_append,
    curtisEval_cons_letterA, curtisEval_nil, mul_one]

theorem curtisRankOne_iff (gens : List G) (i : ℕ) :
    (∀ r ∈ curtisRankOne i, curtisEval gens r = 1) ↔
      (gens.getD (2 * i) 1 ^ 2 = 1 ∧ gens.getD (2 * i + 1) 1 ^ 2 = 1 ∧
        (gens.getD (2 * i) 1 * gens.getD (2 * i + 1) 1) ^ 3 = 1) := by
  have e1 : curtisEval gens [curtisLetterA i, curtisLetterA i] =
      gens.getD (2 * i) 1 ^ 2 := by rw [curtisEval_two_a, pow_two]
  have e2 : curtisEval gens [curtisLetterB i, curtisLetterB i] =
      gens.getD (2 * i + 1) 1 ^ 2 := by rw [curtisEval_two_b, pow_two]
  have e3 : curtisEval gens (curtisPowWord [curtisLetterA i, curtisLetterB i] 3) =
      (gens.getD (2 * i) 1 * gens.getD (2 * i + 1) 1) ^ 3 := by
    rw [curtisEval_powWord, curtisEval_two_ab]
  constructor
  · intro h
    exact ⟨e1 ▸ h _ (by simp [curtisRankOne]), e2 ▸ h _ (by simp [curtisRankOne]),
      e3 ▸ h _ (by simp [curtisRankOne])⟩
  · rintro ⟨h1, h2, h3⟩ r hr
    simp only [curtisRankOne, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e1, h1]
    · rw [e2, h2]
    · rw [e3, h3]

theorem curtisNonAdj_iff (gens : List G) (i j : ℕ) :
    (∀ r ∈ curtisNonAdj i j, curtisEval gens r = 1) ↔
      (⁅gens.getD (2 * i) 1, gens.getD (2 * j) 1⁆ = 1 ∧
        ⁅gens.getD (2 * i) 1, gens.getD (2 * j + 1) 1⁆ = 1 ∧
        ⁅gens.getD (2 * i + 1) 1, gens.getD (2 * j) 1⁆ = 1 ∧
        ⁅gens.getD (2 * i + 1) 1, gens.getD (2 * j + 1) 1⁆ = 1) := by
  simp only [curtisNonAdj, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true, curtisEval_commWord, curtisEval_letterA, curtisEval_letterB]

theorem curtisAdj_iff (gens : List G) (i j : ℕ) :
    (∀ r ∈ curtisAdj i j, curtisEval gens r = 1) ↔
      (⁅gens.getD (2 * i) 1, gens.getD (2 * j + 1) 1⁆ = 1 ∧
        ⁅gens.getD (2 * i + 1) 1, gens.getD (2 * j) 1⁆ = 1 ∧
        (gens.getD (2 * i) 1 * gens.getD (2 * j) 1) ^ 4 = 1 ∧
        (gens.getD (2 * i + 1) 1 * gens.getD (2 * j + 1) 1) ^ 4 = 1 ∧
        gens.getD (2 * i) 1 * gens.getD (2 * i + 1) 1 * gens.getD (2 * i) 1 * gens.getD (2 * j) 1 *
          (gens.getD (2 * i) 1 * gens.getD (2 * i + 1) 1 * gens.getD (2 * i) 1) =
            (gens.getD (2 * i) 1 * gens.getD (2 * j) 1) ^ 2 ∧
        gens.getD (2 * j) 1 * gens.getD (2 * j + 1) 1 * gens.getD (2 * j) 1 * gens.getD (2 * i) 1 *
          (gens.getD (2 * j) 1 * gens.getD (2 * j + 1) 1 * gens.getD (2 * j) 1) =
            (gens.getD (2 * i) 1 * gens.getD (2 * j) 1) ^ 2) := by
  simp only [curtisAdj, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true, curtisEval_commWord, curtisEval_letterA, curtisEval_letterB, curtisEval_powWord,
    curtisEval_two_a, curtisEval_two_b, curtisEval_nRel, mul_inv_eq_one]

theorem curtisRels_iff (gens : List G) :
    (∀ r ∈ curtisRels, curtisEval gens r = 1) ↔
      CurtisRelations (fun i => gens.getD (2 * i) 1) (fun i => gens.getD (2 * i + 1) 1) := by
  constructor
  · intro h
    simp only [curtisRels, List.forall_mem_append, List.forall_mem_flatMap] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨fun i hi => (curtisRankOne_iff gens i).1 (h1 i (List.mem_range.2 hi)),
      fun p hp => (curtisNonAdj_iff gens p.1 p.2).1 (h2 p hp),
      fun p hp => (curtisAdj_iff gens p.1 p.2).1 (h3 p hp)⟩
  · rintro ⟨h1, h2, h3⟩
    simp only [curtisRels, List.forall_mem_append, List.forall_mem_flatMap]
    exact ⟨⟨fun i hi => (curtisRankOne_iff gens i).2 (h1 i (List.mem_range.1 hi)),
      fun p hp => (curtisNonAdj_iff gens p.1 p.2).2 (h2 p hp)⟩,
      fun p hp => (curtisAdj_iff gens p.1 p.2).2 (h3 p hp)⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6
