module

public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.Assembly.LowTwoRank

theorem exists_noncommuting_of_perfect_surjective {G P : Type*} [Group G] [Group P] [Nontrivial P]
    (hG : Group.IsPerfect G) (f : G →* P) (hf : Function.Surjective f) :
    ∃ a b : P, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have h1 : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a _ b _
    exact h b a
  have hG' : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rw [← commutator_def]
    exact hG.commutator_eq_top
  have h2 := Subgroup.map_commutator (⊤ : Subgroup G) (⊤ : Subgroup G) f
  rw [hG', Subgroup.map_top, MonoidHom.range_eq_top.2 hf, h1] at h2
  exact (Subgroup.nontrivial_iff_ne_bot ⊤).1 (inferInstance : Nontrivial (⊤ : Subgroup P)) h2.symm.symm

theorem exists_noncommuting_statedProj_statedSU (K : Type) [Field K] [Finite K] (p f : ℕ)
    [Fact p.Prime] (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ) (hn : 3 ≤ n)
    (hnq : (n, p ^ f) ≠ (3, 2)) :
    ∃ a b : StatedProj (StatedSU n (p ^ f) K), a * b ≠ b * a := by
  have hs := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hK n hn hnq
  have := hs.toNontrivial
  exact exists_noncommuting_of_perfect_surjective
    (CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK hn hnq)
    (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
