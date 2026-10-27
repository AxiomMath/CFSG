module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CTypesT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.RankThree.PartTwo.Sec21.FF79

theorem sec5m1t_layer_of_equiv {G M : Type} [Group G] [Group M] [Finite M] {H : Subgroup G}
    {Y N : Subgroup M} (ψ : ↥H ≃* ↥Y) (hNY : N ≤ Y) (hn : (N.subgroupOf Y).Normal)
    (hidx : (N.subgroupOf Y).index = 2) (hN : CFSG.IsQuasisimple ↥N) :
    Nonempty (↥(CFSG.inSubgroup CFSG.layer H) ≃* ↥N) ∧
      ∀ (x : G) (hx : x ∈ H), x ∈ CFSG.inSubgroup CFSG.layer H ↔ ((ψ ⟨x, hx⟩ : ↥Y) : M) ∈ N := by
  have hlay : Lay Y = N :=
    CFSG.AGLEmbeddingD2.Wilson.Proving.inSubgroup_layer_eq_of_index_two hNY hn hidx hN
  refine ⟨⟨(layEquiv ψ).trans (MulEquiv.subgroupCongr hlay)⟩, fun x hx => ?_⟩
  have h := mem_lay_iff ψ x
  rw [hlay] at h
  exact ⟨fun hx' => (h.mp hx').elim fun _ hz => hz, fun hxN => h.mpr ⟨hx, hxN⟩⟩

end CFSG.OddStandard.SmallF3.Omega
