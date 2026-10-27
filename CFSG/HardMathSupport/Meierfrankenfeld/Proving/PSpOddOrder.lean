module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem units_mul_self_eq_one_iff {K : Type} [Field K] (c : Kˣ) :
    (c : K) * (c : K) = 1 ↔ c ^ 2 = 1 := by
  constructor
  · intro h
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, sq, h, Units.val_one]
  · intro h
    have h' := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h'
    rw [← sq]
    exact h'

theorem scalar_mem_statedSp_iff {K : Type} [Field K] {n : ℕ} (hn : 1 ≤ n) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c ∈ StatedSp n K ↔ c ^ 2 = 1 :=
  CFSG.Open.StatedAPI.scalar_mem_statedSp_iff hn c

theorem card_statedScalars_subgroupOf_statedSp {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) = 2 := by
  have hSm : GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Kˣ) ∈ StatedSp n K :=
    (scalar_mem_statedSp_iff hn (-1)).2 (by rw [neg_one_sq])
  let y : (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) :=
    ⟨⟨GeneralLinearGroup.scalar (Fin n ⊕ Fin n) (-1 : Kˣ), hSm⟩,
      Subgroup.mem_subgroupOf.2 (MonoidHom.mem_range.2 ⟨-1, rfl⟩)⟩
  refine Nat.card_eq_two_iff.2 ⟨1, y, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun z : (StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K) =>
      ((z : StatedSp n K) : GL (Fin n ⊕ Fin n) K)) h
    have h3 := congrArg (fun g : GL (Fin n ⊕ Fin n) K =>
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.inl ⟨0, hn⟩) (Sum.inl ⟨0, hn⟩)) h1
    simp [GeneralLinearGroup.coe_scalar, y] at h3
    apply h2
    linear_combination h3
  · ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    obtain ⟨⟨g, hgS⟩, hzS⟩ := z
    have hzS' : g ∈ StatedScalars (Fin n ⊕ Fin n) K := Subgroup.mem_subgroupOf.1 hzS
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hzS'
    have hc2 : c ^ 2 = 1 := (scalar_mem_statedSp_iff hn c).1 (by rw [hc]; exact hgS)
    rcases mul_self_eq_one_iff.1 ((units_mul_self_eq_one_iff c).2 hc2) with h1 | h1
    · left
      have hc1 : c = 1 := Units.ext h1
      subst hc1
      apply Subtype.ext
      apply Subtype.ext
      simpa using hc.symm
    · right
      have hc1 : c = -1 := Units.ext (by simpa using h1)
      subst hc1
      apply Subtype.ext
      apply Subtype.ext
      simpa using hc.symm

theorem card_statedProj_statedSp_of_two_ne_zero {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) :
    Nat.card (StatedProj (StatedSp n K)) * 2 =
      Nat.card K ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (Nat.card K ^ (2 * j) - 1) := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))
  rw [card_statedScalars_subgroupOf_statedSp h2 hn,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp n] at hc
  exact hc.symm

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

end CFSG.HardMathSupport.Meierfrankenfeld.Proving
