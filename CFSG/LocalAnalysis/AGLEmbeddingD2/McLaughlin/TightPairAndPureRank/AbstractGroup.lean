module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open CFSG.AGLEmbedding

variable {X : Type*} [Group X]

theorem quasisimple_normal_le_center_or_eq_top' {H : Type*} [Group H]
    (hH : CFSG.Open.IsQuasisimple H) {N : Subgroup H} (hN : N.Normal) :
    N ≤ Subgroup.center H ∨ N = ⊤ := by
  obtain ⟨hp, hs⟩ := hH
  have := hN.map (QuotientGroup.mk' (Subgroup.center H)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center H))) with h | h
  · left
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · right
    have hsup : N ⊔ Subgroup.center H = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center H)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center H, Subgroup.center H⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup H).map (QuotientGroup.mk' N) =
        (Subgroup.center H).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator H ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    exact eq_top_iff.mpr (hp ▸ hcomm)

variable [Finite X]

theorem exists_ne_one_mem_centralizer_of_pGroup {p : ℕ} [Fact p.Prime]
    {T U : Subgroup X} (hT : IsPGroup p T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set X)) (hU : U ≠ ⊥) :
    ∃ u ∈ U, u ≠ 1 ∧ u ∈ Subgroup.centralizer (T : Set X) := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h => hy1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
