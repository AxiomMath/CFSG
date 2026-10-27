module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement Pointwise

theorem three_le_pRank_of_card {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hA : CFSG.Open.IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup G) := by
  haveI := Fact.mk hp
  have hpg : IsPGroup p A := by
    intro g
    exact ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  rw [hk] at h3
  have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  have := le_pRank_of_elemAbelian hp.two_le (le_top : A ≤ ⊤) hA hk
  omega

end CFSG.LocalAnalysis.GLTheoremA.H248
