module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

@[expose] def wordOfNat (x : ℕ) : Word := fun i => if x.testBit i then 1 else 0

theorem wordOfNat_xor (x y : ℕ) : wordOfNat (x ^^^ y) = wordOfNat x + wordOfNat y := by
  funext i
  simp only [wordOfNat, Nat.testBit_xor, Pi.add_apply]
  cases x.testBit i <;> cases y.testBit i <;> decide

theorem wordOfNat_zero : wordOfNat 0 = 0 := by
  funext i
  simp [wordOfNat]

@[expose] def popCount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x => Nat.land (Nat.shiftRight x n) 1 + popCount n x

theorem popCount_eq (n x : ℕ) :
    popCount n x = ((Finset.range n).filter fun i => x.testBit i).card := by
  induction n with
  | zero => simp [popCount]
  | succ n ih =>
    rw [popCount, ih, Finset.range_add_one, Finset.filter_insert]
    have : Nat.land (Nat.shiftRight x n) 1 = if x.testBit n then 1 else 0 := by
      change (x >>> n) &&& 1 = _
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
      rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ n) with h | h <;> simp [h]
    rw [this]
    by_cases h : x.testBit n = true
    · simp [h, Finset.card_insert_of_notMem, add_comm]
    · simp [h]

@[expose] def wt (v : Word) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

theorem wt_wordOfNat (x : ℕ) : wt (wordOfNat x) = popCount 24 x := by
  rw [popCount_eq, Finset.card_filter, wt, Finset.card_filter,
    ← Fin.sum_univ_eq_sum_range (fun i => if x.testBit i then 1 else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wordOfNat]

@[expose] def spanCheck : (n : ℕ) → (Fin n → ℕ) → ℕ → (ℕ → Bool) → Bool
  | 0, _, acc, P => P acc
  | n + 1, r, acc, P =>
      spanCheck n (fun i => r i.succ) acc P &&
        spanCheck n (fun i => r i.succ) (Nat.xor acc (r 0)) P

theorem spanCheck_sound : ∀ (n : ℕ) (r : Fin n → ℕ) (acc : ℕ) (P : ℕ → Bool),
    spanCheck n r acc P = true → ∀ m : Fin n → ZMod 2,
      ∃ x, P x = true ∧ wordOfNat x = wordOfNat acc + ∑ k, m k • wordOfNat (r k) := by
  intro n
  induction n with
  | zero =>
    intro r acc P h m
    exact ⟨acc, h, by simp⟩
  | succ n ih =>
    intro r acc P h m
    rw [spanCheck, Bool.and_eq_true] at h
    obtain ⟨h0, h1⟩ := h
    rw [Fin.sum_univ_succ]
    have hm : m 0 = 0 ∨ m 0 = 1 := by
      generalize m 0 = t
      revert t
      decide
    rcases hm with hm | hm
    · obtain ⟨x, hx, hxe⟩ := ih _ acc P h0 (fun i => m i.succ)
      exact ⟨x, hx, by rw [hxe, hm]; simp⟩
    · obtain ⟨x, hx, hxe⟩ := ih _ (Nat.xor acc (r 0)) P h1 (fun i => m i.succ)
      refine ⟨x, hx, ?_⟩
      rw [hxe, hm]
      change wordOfNat (acc ^^^ r 0) + _ = _
      rw [wordOfNat_xor]
      simp only [one_smul]
      abel

@[expose] def rowWord (k : Fin 12) : Word := wordOfNat (rowMask k)

theorem rowWord_mem (k : Fin 12) : rowWord k ∈ golay := by
  rw [mem_golay_iff]
  revert k
  decide

theorem rowWord_pivot (j k : Fin 12) : rowWord j (pivot k) = if j = k then 1 else 0 := by
  revert j k
  decide

theorem rowWord_linearIndependent : LinearIndependent (ZMod 2) rowWord := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  simpa [Finset.sum_apply, rowWord_pivot] using congrFun hg (pivot j)

theorem finrank_span_rowWord :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range rowWord)) = 12 := by
  rw [finrank_span_eq_card rowWord_linearIndependent]
  simp

theorem finrank_golay : Module.finrank (ZMod 2) golay = 12 := by
  have h := LinearMap.finrank_range_add_finrank_ker synd
  rw [LinearMap.range_eq_top.2 synd_surjective, finrank_top] at h
  simp at h
  rw [golay]
  omega

theorem golay_eq_span : golay = Submodule.span (ZMod 2) (Set.range rowWord) := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_rowWord, finrank_golay])
  exact Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact rowWord_mem k)

theorem minDistCheck :
    spanCheck 12 rowMask 0 (fun x => Nat.beq x 0 || decide (8 ≤ popCount 24 x)) = true := by
  decide

theorem minDist {v : Word} (hv : v ∈ golay) (h0 : v ≠ 0) : 8 ≤ wt v := by
  rw [golay_eq_span] at hv
  obtain ⟨m, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 hv
  obtain ⟨x, hx, hxe⟩ := spanCheck_sound 12 rowMask 0 _ minDistCheck m
  have hc : (∑ k, m k • rowWord k) = wordOfNat x := by
    rw [hxe, wordOfNat_zero, zero_add]
    rfl
  rw [hc] at h0 ⊢
  have hx0 : x ≠ 0 := fun h => h0 (by rw [h, wordOfNat_zero])
  rw [wt_wordOfNat]
  simp only [Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq] at hx
  omega

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
