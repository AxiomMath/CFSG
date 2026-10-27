module

public import CFSG.LocalAnalysis.GL83PartI.I713.Extension

public section

namespace GL83.I713

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

variable {p : ℕ}

theorem pRank_top_le_one_of_card_lt {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    (h : Nat.card X < p ^ 2) : pRank p (⊤ : Subgroup X) ≤ 1 := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  by_contra hlt
  have h1 : p ^ 2 ≤ Nat.card E := hE ▸ Nat.pow_le_pow_right hp.pos (by omega)
  have h2 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
  omega

theorem pRank_top_eq_zero_of_not_dvd {X : Type*} [Group X] [Finite X] (hp : p.Prime)
    (h : ¬ p ∣ Nat.card X) : pRank p (⊤ : Subgroup X) = 0 := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup X)
  by_contra hne
  apply h
  have hpE : p ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self p hne
  exact hpE.trans (Subgroup.card_subgroup_dvd_card E)

theorem pRank_outer_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (hp : 1 < p) (e : X ≃* Y) :
    pRank p (⊤ : Subgroup (Outer X)) = pRank p (⊤ : Subgroup (Outer Y)) :=
  CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp (equivalence e)

@[expose] def OutClauseFor (K : Type*) [Group K] [Finite K] : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p (⊤ : Subgroup K) ≤ 1 → pRank p (⊤ : Subgroup (Outer K)) ≤ 1

theorem OutClauseFor.of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (h : OutClauseFor Y) : OutClauseFor X := by
  intro p hp hp2 hX
  rw [pRank_outer_eq_of_mulEquiv hp.one_lt e]
  exact h p hp hp2 (by rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e])

theorem outClauseFor_of_card_outer_le_four {K : Type*} [Group K] [Finite K]
    (h : Nat.card (Outer K) ≤ 4) : OutClauseFor K := by
  intro p hp hp2 _
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  refine pRank_top_le_one_of_card_lt hp (lt_of_le_of_lt h ?_)
  nlinarith

theorem outClauseFor_of_not_dvd {K : Type*} [Group K] [Finite K]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p (⊤ : Subgroup K) ≤ 1 → ¬ p ∣ Nat.card (Outer K)) :
    OutClauseFor K := by
  intro p hp hp2 hK
  rw [pRank_top_eq_zero_of_not_dvd hp (h p hp hp2 hK)]
  exact Nat.zero_le 1

end GL83.I713
