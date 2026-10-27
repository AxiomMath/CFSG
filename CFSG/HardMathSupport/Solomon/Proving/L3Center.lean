module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Assembly.LowTwoRank Matrix

theorem exists_noncomm_of_perfect {G : Type} [Group G] [Nontrivial G] [Group.IsPerfect G] :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : IsMulCommutative G := ⟨⟨fun a b => h a b⟩⟩
  exact (Group.IsPerfect.not_isMulCommutative (G := G)) hc

theorem center_eq_bot_of_simple_nonabelian {Y : Type} [Group Y] [IsSimpleGroup Y]
    (hna : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)

theorem center_eq_bot_of_mulEquiv {Y G : Type} [Group Y] [Group G] [IsSimpleGroup G]
    [Group.IsPerfect G] (e : Y ≃* G) : Subgroup.center Y = ⊥ := by
  have : IsSimpleGroup Y := e.isSimpleGroup
  refine center_eq_bot_of_simple_nonabelian ?_
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_perfect (G := G)
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem center_eq_bot_of_sl_three (K : Type) [Field K] [Finite K] (Y : Type) [Group Y]
    (e : Y ≃* StatedProj (StatedSL 3 K)) : Subgroup.center Y = ⊥ := by
  obtain ⟨hnt, hsim, -⟩ :=
    CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by norm_num) (Or.inl (by norm_num))
  have hper : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 3) (by norm_num) (Or.inl (by norm_num))
  have e' : Y ≃* ProjectiveSpecialLinearGroup (Fin 3) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
  exact center_eq_bot_of_mulEquiv e'

theorem center_eq_bot_of_su_three_ne_two (Y : Type) [Group Y] (K : Type) [Field K] [Finite K]
    (q : ℕ) (hcard : Nat.card K = q ^ 2) (hq2 : q ≠ 2)
    (e : Y ≃* StatedProj (StatedSU 3 q K)) : Subgroup.center Y = ⊥ := by
  have := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hpk⟩ := FiniteField.card' K
  have hpk' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hpk]
  have hdvd : q ∣ p ^ (n : ℕ) := by
    rw [← hpk', hcard]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have : Fact p.Prime := ⟨hp⟩
  subst hqf
  have hnq : (3, p ^ f) ≠ (3, 2) := fun h => hq2 (Prod.mk.inj h).2
  obtain ⟨-, hnt, hsim⟩ :=
    CFSG.ClassicalGroups.Unitary.fam_unitary_projective_simple K p f hcard 3 le_rfl hnq
  have hper0 : Group.IsPerfect (StatedSU 3 (p ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcard (by norm_num) hnq
  have hper : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ f) K)) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  exact center_eq_bot_of_mulEquiv e

end CFSG.HardMathSupport.Solomon.Proving
