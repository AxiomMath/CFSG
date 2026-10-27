module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductions

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding

theorem kFactBlockThreeOrderThree_of_inverted (hΛ : KFactBlockInvertedThree) :
    KFactBlockThreeOrderThree := by
  intro G _ _ M S L hK hA hL hX hS
  obtain ⟨a, ha, g, hg, ha3, hga⟩ := hΛ G M S L hK hA hL hX hS
  have haM : a ∈ M := hL.le ha.2
  have hgM : g ∈ M := hL.le hg.2
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hab : q ⟨a, haM⟩ ∈ blockPL M S L := ⟨⟨a, haM⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hgb : q ⟨g, hgM⟩ ∈ barM M L := ⟨⟨g, hgM⟩, Subgroup.mem_subgroupOf.mpr hg.2, rfl⟩
  have hne : q ⟨a, haM⟩ ≠ 1 := fun h1 =>
    not_mem_pCoreOf_two_of_orderOf_eq_three ha3 ((mk_pCore_two_eq_one_iff _).mp h1)
  have h3 : q ⟨a, haM⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, haM⟩ : M) ^ 3 = 1 := Subtype.ext (by simp [← ha3, pow_orderOf_eq_one])
    rw [this, map_one]
  have hinv : q ⟨g, hgM⟩ * q ⟨a, haM⟩ * (q ⟨g, hgM⟩)⁻¹ * q ⟨a, haM⟩ = 1 := by
    have e : q ⟨g, hgM⟩ * q ⟨a, haM⟩ * (q ⟨g, hgM⟩)⁻¹ * q ⟨a, haM⟩ =
        q (⟨g, hgM⟩ * ⟨a, haM⟩ * ⟨g, hgM⟩⁻¹ * ⟨a, haM⟩) := by
      simp only [map_mul, map_inv]
    rw [e, mk_pCore_two_eq_one_iff]
    simpa using hga
  refine ⟨q ⟨a, haM⟩, hab, h3, fun hc => hne ?_⟩
  have hcomm : q ⟨g, hgM⟩ * q ⟨a, haM⟩ = q ⟨a, haM⟩ * q ⟨g, hgM⟩ :=
    Subgroup.mem_centralizer_iff.mp hc _ hgb
  have h2 : q ⟨a, haM⟩ ^ 2 = 1 := by
    rw [sq]
    calc q ⟨a, haM⟩ * q ⟨a, haM⟩
        = q ⟨g, hgM⟩ * q ⟨a, haM⟩ * (q ⟨g, hgM⟩)⁻¹ * q ⟨a, haM⟩ := by
          rw [hcomm]; group
      _ = 1 := hinv
  have : q ⟨a, haM⟩ = q ⟨a, haM⟩ ^ 3 * (q ⟨a, haM⟩ ^ 2)⁻¹ := by group
  rw [this, h3, h2]
  simp

end CFSG.AGLEmbeddingD2
