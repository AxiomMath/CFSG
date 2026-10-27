module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentTenFourteen

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open Subgroup

@[expose] def KFactTenFourteenTwoA5 : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (K Y₀ J : Subgroup Y) (R : Sylow p Y) (c : Y),
    p.Prime → p ≠ 2 → K.Normal → RankOneCent.TenFourteenOneGroup p ↥K → ¬ K ≤ Y₀ →
    centralizer (K : Set Y) ≤ Y₀ → c ∈ center Y → orderOf c = p →
    CFSG.Open.pRank p (R : Subgroup Y) ≤ 3 →
    (∀ A : Subgroup Y, A ≤ R → IsElemAbelian p A → Nat.card A = p ^ 2 →
      3 ≤ CFSG.Open.pRank p ((R : Subgroup Y) ⊓ centralizer (A : Set Y)) →
      normalizer (A : Set Y) ≤ Y₀) →
    J ≤ Y₀ → IsSubnormal J Y₀ → ⁅J, J⁆ = J →
    (∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) →
    ¬ J ≤ centralizer (K : Set Y) →
    p = 5 ∧ ∃ f : J →* alternatingGroup (Fin 5), Function.Surjective f ∧
      f.ker = (centralizer (K : Set Y)).subgroupOf J

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo
