module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {M H R : Subgroup G}

theorem isPGroup_zpowers_of_pow_eq_one {X : Type*} [Group X] {q : ℕ} {u : X} (hu : u ^ q = 1) :
    IsPGroup q (Subgroup.zpowers u) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, ← hn]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]

end CFSG.AGLEmbeddingD2
