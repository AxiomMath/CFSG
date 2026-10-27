module

public import CFSG.ClassicalInvolution.Orders.Basic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.Open.Defs

public section

namespace CFSG.ClassicalInvolution

open CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Symplectic CFSG.Open

variable {K : Type} [Field K] {n : ℕ}

theorem scalar_mem_statedSp_iff (hn : 1 ≤ n) (c : Kˣ) :
    (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K ↔
      (c : K) ^ 2 = 1 := by
  rw [CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn, ← Units.val_eq_one, Units.val_pow_eq_pow_val]

theorem card_scalars_subgroupOf_statedSp (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) :
    Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) = 2 := by
  have hm : (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Kˣ) :
      GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K := by
    rw [scalar_mem_statedSp_iff hn]
    simp
  rw [Nat.card_eq_two_iff]
  refine ⟨1, ⟨⟨_, hm⟩, ⟨-1, rfl⟩⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun x : (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) =>
      ((x : StatedSp n K) : GL (Fin n ⊕ Fin n) K)) h
    simp only at h1
    have h2' := congrArg (fun A : GL (Fin n ⊕ Fin n) K =>
      (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩)) h1
    simp [Matrix.GeneralLinearGroup.coe_scalar] at h2'
    exact h2 (by linear_combination h2')
  · ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 g.2
    have hsp : (Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c : GL (Fin n ⊕ Fin n) K) ∈
        StatedSp n K := by
      rw [hc]
      exact (g : StatedSp n K).2
    rw [scalar_mem_statedSp_iff hn] at hsp
    have hc1 : c = 1 ∨ c = -1 := by
      have : (c : K) = 1 ∨ (c : K) = -1 :=
        mul_self_eq_one_iff.1 (by rw [← pow_two]; exact hsp)
      rcases this with h | h
      · exact Or.inl (Units.ext h)
      · exact Or.inr (Units.ext h)
    rcases hc1 with rfl | rfl
    · left
      refine Subtype.ext (Subtype.ext ?_)
      rw [← hc]
      simp
    · right
      refine Subtype.ext (Subtype.ext ?_)
      rw [← hc]

theorem card_statedProj_statedSp_of_two_ne_zero [Finite K] (h2 : (2 : K) ≠ 0) (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSp n K)) * 2 =
      Nat.card K ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (Nat.card K ^ (2 * j) - 1) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))
  rw [card_scalars_subgroupOf_statedSp h2 hn,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp n] at h
  exact h.symm

theorem card_statedProj_statedSp_eq_ordBC [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSp n K)) = ordBC n (p ^ f) := by
  have h := card_statedProj_statedSp_of_two_ne_zero (two_ne_zero_of_card_eq_prime_pow hp hp2 hK) hn
  rw [hK, sq] at h
  rw [ordBC, gcd_two_sub_one_of_odd (odd_of_card_eq_prime_pow hp hp2 rfl), ← h,
    Nat.mul_div_cancel _ two_pos]

end CFSG.ClassicalInvolution
