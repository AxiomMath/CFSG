module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure IsWitnessGen (p : ℕ) (P : Sylow p G) (M : Subgroup G) : Prop where
  maxLocal : rankThreeIsMaxTwoLocal M
  u0 : rankThreeGamma 2 p (P : Subgroup G) ≤ M
  u1 : rankThreeGamma 1 p (P : Subgroup G) ≤ M ∨ (5 ≤ p ∧ Group.IsSolvable ↥M) ∨
    (p = 3 ∧ rankThreeClauseC M (P : Subgroup G))
  u2 : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ pRank p (H ⊓ M) → H ≤ M

structure IsWitnessPrime (p : ℕ) (P : Sylow p G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  rank : 3 ≤ pRank p (P : Subgroup G)

theorem Standing.toGen (hS : Standing G) : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G where
  simple := hS.simple
  nonab := hS.nonab
  kProper := hS.kProper
  charTwo := hS.charTwo
  rank := hS.rank.ge

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem toGen (hw : IsWitness p P M) : IsWitnessGen p P M where
  maxLocal := hw.maxLocal
  u0 := hw.u0
  u1 := hw.u1.elim Or.inl fun h => h.elim (fun hB => Or.inr (Or.inl ⟨hB.1, hB.2.1⟩))
    (fun hC => Or.inr (Or.inr hC))
  u2 := hw.u2

end IsWitness

namespace IsWitnessPrime

theorem of_mem_sigmaA (hS : Standing G) {p : ℕ} (hp : p ∈ rankThreeSigmaA G) (P : Sylow p G) :
    IsWitnessPrime p P where
  prime := sigmaA_prime p hp
  odd := sigmaA_odd p hp
  rank := selected_sylow_rank_at_least_three hS.rank p hp P

end IsWitnessPrime

namespace IsWitnessGen

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem normalizer_sylow_le (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) :
    normalizer ((P : Subgroup G) : Set G) ≤ M :=
  (gamma_normalizer_le 2 p (P : Subgroup G) (P : Subgroup G) le_rfl (by
    have := hp.rank; omega)).trans hw.u0

theorem sylow_le (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) :
    (P : Subgroup G) ≤ M :=
  le_normalizer.trans (hw.normalizer_sylow_le hp)

theorem three_le_pRank (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) :
    3 ≤ pRank p M :=
  hp.rank.trans (pRank_mono p hp.prime.one_lt (hw.sylow_le hp))

theorem le_of_le_of_two_le_pRank (hp : p.Prime) (hw : IsWitnessGen p P M)
    {R H : Subgroup G} (hRM : R ≤ M) (hR : 2 ≤ pRank p R) (hH : IsTwoLocal H) (hRH : R ≤ H) :
    H ≤ M :=
  hw.u2 H hH (hR.trans (pRank_mono p hp.one_lt (le_inf hRH hRM)))

theorem eq_of_le_of_two_le_pRank (hp : p.Prime) (hw : IsWitnessGen p P M)
    {R H : Subgroup G} (hRM : R ≤ M) (hR : 2 ≤ pRank p R) (hH : rankThreeIsMaxTwoLocal H)
    (hRH : R ≤ H) : H = M :=
  (hH.2 M hw.maxLocal.1 (hw.le_of_le_of_two_le_pRank hp hRM hR hH.1 hRH)).symm

end IsWitnessGen

@[expose] def witnessThree (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M : Subgroup G) : Prop :=
  p ∈ rankThreeSigmaA G ∧ IsWitness p P M

theorem witnessThree_spec (hS : Standing G) :
    ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), witnessThree G p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M :=
  fun _ P _ h => ⟨IsWitnessPrime.of_mem_sigmaA hS h.1 P, h.2.toGen⟩

end CFSG.LocalAnalysis.RankThreeUC
