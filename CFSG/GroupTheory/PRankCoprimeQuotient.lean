module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Assembly.Defs

public section

namespace CFSG.GroupTheory.PRankCoprimeQuotient

variable {G : Type*} [Group G] [Finite G]

theorem pRank_quotient_eq_of_not_dvd {p : ℕ} (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) : CFSG.pRank p (G ⧸ N) = CFSG.pRank p G := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_quotient_eq N hN

theorem assembly_pRank_quotient_eq_of_not_dvd {p : ℕ} (hp : p.Prime) (N : Subgroup G)
    [N.Normal] (hN : ¬ p ∣ Nat.card N) :
    CFSG.Assembly.pRank p (⊤ : Subgroup (G ⧸ N)) = CFSG.Assembly.pRank p (⊤ : Subgroup G) := by
  have : Fact p.Prime := ⟨hp⟩
  exact CFSG.SectionRank.pRank_quotient_eq N hN

end CFSG.GroupTheory.PRankCoprimeQuotient
