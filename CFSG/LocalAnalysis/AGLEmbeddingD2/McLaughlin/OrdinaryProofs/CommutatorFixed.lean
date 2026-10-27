module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped commutatorElement

theorem le_normalizer_commutator_of_normalizes {G : Type} [Group G] {S V L : Subgroup G}
    (hSV : S ≤ Subgroup.normalizer (V : Set G)) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    S ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
  intro s hs
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSV hs)
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSL hs)
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  rw [Subgroup.map_commutator, h1, h2]

end CFSG.AGLEmbeddingD2.McLaughlin

end
