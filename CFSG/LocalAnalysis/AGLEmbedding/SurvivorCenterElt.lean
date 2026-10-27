module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralPerfectLifts
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Aux

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_inf_centerOf {p : ℕ} [Fact p.Prime] {R A : Subgroup G} (hR : IsPGroup p R)
    (hAR : A ≤ R) (hAn : R ≤ Subgroup.normalizer (A : Set G)) (hA : A ≠ ⊥) :
    ∃ w ∈ A, w ∈ centerOf R ∧ w ≠ 1 := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hn : (A.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAR).mpr hAn
  have hne : A.subgroupOf R ≠ ⊥ := by
    intro hbot
    apply hA
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAR ha⟩ : R) ∈ A.subgroupOf R := Subgroup.mem_subgroupOf.mpr ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨⟨⟨w, hwR⟩, hwA, hwZ⟩, hw1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne))
  refine ⟨w, Subgroup.mem_subgroupOf.mp hwA, ⟨hwR, ?_⟩, fun h => hw1 (Subtype.ext
    (Subtype.ext h))⟩
  show w ∈ Subgroup.centralizer (R : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨r, hr⟩)

end Aux

end CFSG.AGLEmbedding
