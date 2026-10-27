module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.NormalCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndSchur

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {y : G}
    (h : K.map (MulAut.conj y).toMonoidHom = K) : y ∈ normalizer (K : Set G) := by
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← h]
    exact ⟨x, hx, by simp⟩
  · rw [← h] at hx
    obtain ⟨x', hx', hx'e⟩ := hx
    have : x' = x := by simpa using hx'e
    rwa [← this]

end CFSG.EvenSporadicStandard.ThStd
