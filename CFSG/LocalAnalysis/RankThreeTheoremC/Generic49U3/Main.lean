module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeTheoremC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

theorem u3_proper {G : Type} [Group G] [Finite G] (hS : Setting G) :
    ∀ Y : Subgroup G, Y ≠ ⊥ → IsPGroup 2 Y → Subgroup.normalizer (Y : Set G) ≠ ⊤ := by
  intro Y hY1 hY2 hN
  have hsimple : IsSimpleGroup G := hS.simple
  have hnormal : Y.Normal := Subgroup.normalizer_eq_top_iff.mp hN
  have hYtop : Y = ⊤ := (hsimple.eq_bot_or_eq_top_of_normal Y).resolve_left hY1
  have hG2 : IsPGroup 2 G := by
    rw [hYtop] at hY2
    exact hY2.of_equiv Subgroup.topEquiv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
  have hcen : Subgroup.center G = ⊤ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center G)
      exact absurd (Subtype.ext (by simpa [h] using hz)) hz1
    · exact h
  obtain ⟨a, b, hab⟩ := hS.nonab
  have ha : a ∈ Subgroup.center G := hcen ▸ Subgroup.mem_top a
  exact hab (Subgroup.mem_center_iff.mp ha b).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
