module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def TheoremDAt (M : Subgroup G) : Prop :=
  ∀ T : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 T M → normalizer (T : Set G) ≤ M

@[expose] def FourteenFifteenAt (M : Subgroup G) : Prop :=
  ∀ q : ℕ, q.Prime → q ≠ 2 → q ∉ CFSG.Open.rankThreeSigmaA G → ∀ Q : Subgroup G, Q ≤ M →
    IsPGroup q Q → 2 ≤ CFSG.Open.pRank q Q → CFSG.Open.rankThreeGamma 1 q Q ≤ M →
      ∀ H : Subgroup G, CFSG.Open.IsTwoLocal H → Q ≤ H → ¬ H ≤ M →
        ∀ S : Sylow 2 G, ¬ (S : Subgroup G) ≤ M

@[expose] def AGL81FourteenFifteen : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CStarGen G → ∀ M : Subgroup G,
    CFSG.Open.rankThreeIsMaxTwoLocal M → (sigmaSet G M).Nonempty → FourteenFifteenAt M

theorem exists_sylow_eq_of_normalizer_le {p : ℕ} [Fact p.Prime] {M T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hN : normalizer (T : Set G) ≤ M) :
    ∃ S : Sylow p G, (S : Subgroup G) = T := by
  have hTG := CFSG.LocalAnalysis.RankThreeUC.isSylowOf_top_of_normalizer_le hT hN
  obtain ⟨-, hP, hdvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp hTG
  exact ⟨hP.toSylow (by simpa using hdvd), rfl⟩

theorem theoremCAt_of_theoremDAt (hC : CStarGen G) {M : Subgroup G}
    (hM : CFSG.Open.rankThreeIsMaxTwoLocal M) (h : FourteenFifteenAt M) (hD : TheoremDAt M) :
    CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt M := by
  intro q hq hq2 Q hQM hQp hQrank hΓ H hH hQH
  by_cases hqσ : q ∈ CFSG.Open.rankThreeSigmaA G
  · exact hC.embed q hqσ M hM Q hQM hQp hQrank H hH hQH
  · by_contra hHM
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 M
    obtain ⟨S, hS⟩ := exists_sylow_eq_of_normalizer_le hT (hD T hT)
    exact h q hq hq2 hqσ Q hQM hQp hQrank hΓ H hH hQH hHM S (by rw [hS]; exact hT.le)

end CFSG.LocalAnalysis.AGL81TheoremCD
