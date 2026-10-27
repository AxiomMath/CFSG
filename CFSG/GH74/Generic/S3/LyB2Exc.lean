module

public import CFSG.GH74.GLS.TwoThin.G.OrdersB2

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Blueprint Subgroup

theorem mul_sq_sub_one_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem no_sol_mul_sq_sub_one {N a : ℕ} (h1 : a * (a ^ 2 - 1) < N)
    (h2 : N < (a + 1) * ((a + 1) ^ 2 - 1)) (q : ℕ) : q * (q ^ 2 - 1) ≠ N := by
  intro hq
  rcases le_or_gt q a with h | h
  · have := mul_sq_sub_one_mono h
    omega
  · have := mul_sq_sub_one_mono (show a + 1 ≤ q by omega)
    omega

@[expose] def ExcOrder (N : ℕ) : Prop :=
  N = 2520 ∨ N = 20160 ∨ N = 181440 ∨ N = 1814400 ∨ N = 19958400

theorem ExcOrder.two_mul_ne {N : ℕ} (h : ExcOrder N) (q : ℕ) : 2 * N ≠ q * (q ^ 2 - 1) := by
  intro hq
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact no_sol_mul_sq_sub_one (a := 17) (by norm_num) (by norm_num) q hq.symm
  · exact no_sol_mul_sq_sub_one (a := 34) (by norm_num) (by norm_num) q hq.symm
  · exact no_sol_mul_sq_sub_one (a := 71) (by norm_num) (by norm_num) q hq.symm
  · exact no_sol_mul_sq_sub_one (a := 153) (by norm_num) (by norm_num) q hq.symm
  · exact no_sol_mul_sq_sub_one (a := 341) (by norm_num) (by norm_num) q hq.symm

theorem ExcOrder.ne_sixty {N : ℕ} (h : ExcOrder N) : N ≠ 60 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> norm_num

@[expose] def IsExcB2 (K : Type) [Group K] : Prop :=
  InB2 K ∧ ¬ HasSL2Model K Odd

theorem excOrder_alternating {n : ℕ} (h7 : 7 ≤ n) (h11 : n ≤ 11) :
    ExcOrder (Nat.card (alternatingGroup (Fin n))) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  interval_cases n <;> simp [ExcOrder, Nat.factorial]

theorem IsExcB2.simple_quotient
    {K : Type} [Group K] (h : IsExcB2 K) :
    IsSimpleGroup (K ⧸ center K) ∧ (∃ a b : K ⧸ center K, a * b ≠ b * a) ∧
      ExcOrder (Nat.card (K ⧸ center K)) := by
  have hq : IsQuasisimple K := h.1.1.1
  refine ⟨hq.2.1, hq.2.2, ?_⟩
  rcases inB2_cases h.1 with ⟨F, hF, hFin, hodd, ⟨e⟩⟩ | ⟨n, hn7, hn11, hdc⟩ | ⟨hL34, -⟩
  · exact absurd ⟨F, hF, hFin, hodd, ⟨e⟩⟩ h.2
  · obtain ⟨-, -, ⟨e⟩⟩ := hdc
    rw [Nat.card_congr e.toEquiv]
    exact excOrder_alternating hn7 hn11
  · rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) hL34]
    right; left
    exact ordA_two_four

end CFSG.GH74.Generic.S3
