module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.GeneratedCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

theorem kc_glbCore_ne_top {K : Type} [Group K] [Finite K] {p : ℕ} {S H : Subgroup K}
    (hH : H ≠ ⊤)
    (h : ∀ Q : Subgroup K, Q ≤ S → 1 ≤ CFSG.Open.pRank p Q →
      Subgroup.normalizer (Q : Set K) ≤ H) :
    CFSG.Open.GLBCore p 1 S ≠ ⊤ := by
  intro htop
  apply hH
  have hle : CFSG.Open.GLBCore p 1 S ≤ H := by
    refine sSup_le ?_
    rintro N ⟨Q, hQS, hQ, rfl⟩
    exact h Q hQS hQ
  rw [htop] at hle
  exact top_le_iff.mp hle

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
