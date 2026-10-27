module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaFive3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding (KGenThree)

variable {G : Type} [Group G] [Finite G]

theorem five_le_of_prime_ne_two_ne_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    5 ≤ p := by
  have h2 := hp.two_le
  have h4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by norm_num)
  omega

@[expose] def D1ComponentAlphaSmallCaseThree3 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p G) (M H R : Subgroup G) (z : G)
    (Pbar : Sylow p (ReducedCentralizer p z)) (zbar : ReducedCentralizer p z)
    (K : Subgroup (ReducedCentralizer p z)), p = 3 →
    D1ComponentAlphaData3 p P M H R z Pbar zbar K →
    Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 → False

theorem D1ComponentAlphaData3.eq_three {p : ℕ} [Fact p.Prime] {P : Sylow p G}
    {M H R : Subgroup G} {z : G} {Pbar : Sylow p (ReducedCentralizer p z)}
    {zbar : ReducedCentralizer p z} {K : Subgroup (ReducedCentralizer p z)}
    (h : D1ComponentAlphaData3 p P M H R z Pbar zbar K) (hKF1 : KF1At G) :
    p = 3 := by
  by_contra hp3
  exact h.false_of_five_le hKF1 (five_le_of_prime_ne_two_ne_three Fact.out
    h.data.input.ne_two hp3)

end CFSG.LocalAnalysis.RankThreeTheoremC
