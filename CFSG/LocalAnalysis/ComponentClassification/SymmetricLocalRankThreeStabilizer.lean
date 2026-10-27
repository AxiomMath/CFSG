module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalRankThreeNormalizer

public section

namespace CFSG.ComponentClassification.SymmetricLocal

open CFSG.Open CFSG.LargeEvenClassification CFSG.LargeEvenClassification.Helpers
  CFSG.ComponentClassification.LiteratureLocal

universe u

variable {G : Type u} [Group G] [Finite G]

theorem rank_three_component_stabilizer_vertices (hrank : 3 ≤ CFSG.pRank 2 G) (S : Sylow 2 G)
    {Estar : Subgroup G} (hEstar : Estar ∈ E3 G) (hEstarS : Estar ≤ S) :
    ((rankThreeClassStabilizer Estar : Set G) =
        {g | (fun E => CFSG.conjugate E g) '' rankThreeClass Estar = rankThreeClass Estar}) ∧
      (S : Subgroup G) ≤ rankThreeClassStabilizer Estar ∧
      rankThreeClass Estar = {E | E ∈ E3 G ∧ E ≤ rankThreeClassStabilizer Estar} ∧
      rankThreeClass Estar =
        (fun E : Subgroup (rankThreeClassStabilizer Estar) =>
          E.map (rankThreeClassStabilizer Estar).subtype) '' E3 (rankThreeClassStabilizer Estar) ∧
      (∀ E ∈ rankThreeClass Estar,
        Subgroup.normalizer (E : Set G) ≤ rankThreeClassStabilizer Estar) ∧
      (rankThreeClassStabilizer Estar = ⊤ ↔ Conn3 G) := by
  obtain ⟨-, hctrl⟩ := rank_three_component_normalizer_control hrank S
  obtain ⟨hcarrier, hE3S, hNS, -, -, hnotconn⟩ := hctrl Estar hEstar hEstarS
  set M := rankThreeClassStabilizer Estar
  have hSM : (S : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNS
  have hNE : ∀ E ∈ rankThreeClass Estar, Subgroup.normalizer (E : Set G) ≤ M := by
    intro E hE g hg
    refine mem_rankThreeClassStabilizer_of_mem hE ?_
    rw [conjugate_eq_of_mem_normalizer hg]
    exact hE
  have hΔM : ∀ E ∈ rankThreeClass Estar, E ≤ M := fun E hE =>
    Subgroup.le_normalizer.trans (hNE E hE)
  have hE3M : ∀ E ∈ E3 G, E ≤ M → E ∈ rankThreeClass Estar := by
    intro E hE hEM
    obtain ⟨g, hg⟩ := exists_conjugate_le_sylow (G := M) (E := E.subgroupOf M)
      (rankThree_elementary_isPGroup E hE.1).comap_subtype (S.subtype hSM)
    have hEg : CFSG.conjugate E (g : G) ≤ S := by
      intro x hx
      have hx' := (mem_conjugate_iff' E (g : G) x).mp hx
      have hxM : x ∈ M := by
        have h := M.mul_mem (M.mul_mem (M.inv_mem g.2) (hEM hx')) g.2
        simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
          mul_one] using h
      have hmem : (⟨x, hxM⟩ : M) ∈ CFSG.conjugate (E.subgroupOf M) g :=
        (mem_conjugate_iff' _ g _).mpr hx'
      have hS := hg hmem
      rw [Sylow.coe_subtype] at hS
      exact hS
    have hEgΔ : CFSG.conjugate E (g : G) ∈ rankThreeClass Estar :=
      hE3S ⟨conjugate_mem_E3 hE g, hEg⟩
    have hginv := (mem_rankThreeClassStabilizer_iff Estar ((g : G)⁻¹)).mp (M.inv_mem g.2)
    rw [← hginv]
    exact ⟨_, hEgΔ, by simp only [conjugate_conjugate', mul_inv_cancel, conjugate_one']⟩
  have hΔeq : rankThreeClass Estar = {E | E ∈ E3 G ∧ E ≤ M} := by
    ext E
    exact ⟨fun hE => ⟨hE.1, hΔM E hE⟩, fun hE => hE3M E hE.1 hE.2⟩
  refine ⟨hcarrier, hSM, hΔeq, ?_, hNE, ⟨fun hM => ?_, fun hconn => ?_⟩⟩
  · rw [hΔeq]
    ext E
    constructor
    · rintro ⟨hE, hEM⟩
      refine ⟨E.subgroupOf M, ⟨isElemAbelian_subgroupOf M hE.1, ?_⟩, ?_⟩
      · rw [rankThree_card_subgroupOf_eq E M hEM]
        exact hE.2
      · exact Subgroup.map_subgroupOf_eq_of_le hEM
    · rintro ⟨E', hE', rfl⟩
      refine ⟨⟨elementary_map E' hE'.1 M.subtype, ?_⟩, Subgroup.map_subtype_le E'⟩
      rw [Subgroup.card_map_of_injective M.subtype_injective]
      exact hE'.2
  · by_contra hconn
    exact (lt_top_iff_ne_top.mp (hnotconn hconn)) hM
  ·
    have hall : ∀ F ∈ E3 G, F ∈ rankThreeClass Estar := fun F hF =>
      ⟨hF, hconn.2 ⟨F, hF⟩ ⟨Estar, hEstar⟩⟩
    refine eq_top_iff.mpr fun g _ => ?_
    exact mem_rankThreeClassStabilizer_of_mem (hall Estar hEstar)
      (hall _ (conjugate_mem_E3 hEstar g))

end CFSG.ComponentClassification.SymmetricLocal
