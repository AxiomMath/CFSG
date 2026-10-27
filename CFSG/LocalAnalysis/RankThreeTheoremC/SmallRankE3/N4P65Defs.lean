module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P5Prop65

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def StepP65OddFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Setting G → TheoremD1 G →
    ∀ (P : Sylow 5 G) (M : Subgroup G), SmallRankSituation G 5 P M → ∀ x z : G,
      SmallRankPoint P M x → SmallRankCentral P z → ∀ F : Subgroup G, F ≠ ⊥ → F ≤ M →
        Nat.Coprime 5 (Nat.card F) → Odd (Nat.card F) →
          zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) → normalizer (F : Set G) ≤ M

theorem slotProp65Five_of_stepP65OddFive (h : StepP65OddFive) : SlotProp65Five := by
  intro G _ _ hS hD1 P M x z T hf _ _ F hFM hF1 hFcop hBF
  have hodd : Odd (Nat.card F) := by
    have h2 : Nat.Coprime (Nat.card F) 2 :=
      Nat.Coprime.coprime_dvd_right (by norm_num : 2 ∣ 10) hFcop
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    exact absurd (Nat.Coprime.eq_one_of_dvd h2.symm (even_iff_two_dvd.mp hne)) (by norm_num)
  have hcop5 : Nat.Coprime 5 (Nat.card F) :=
    (Nat.Coprime.coprime_dvd_right (by norm_num : 5 ∣ 10) hFcop).symm
  exact h G hS hD1 P M hf.situation x z hf.point hf.central F hF1 hFM hcop5 hodd hBF

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
