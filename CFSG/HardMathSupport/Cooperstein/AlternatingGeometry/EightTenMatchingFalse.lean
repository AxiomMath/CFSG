module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenResidualSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.PairFlipTransport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSRange
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TransitiveSupport

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin

theorem eightTenNodeMatching : EightTenNodeMatching := by
  intro G _ _ X S L hX hA hL m hm e hN θ hNS hθS σ hσ1 hσ2 hle hD hN1 h8
  classical
  exfalso
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  obtain ⟨U, Δ, hU2, hUN, hUnorm, hUsign, hΔ5, hΓ, hUfix, hUtrans⟩ :=
    exists_normal_two_group_of_matching (Ω := Fin m) (by simpa using hm) σ hσ1 hσ2
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ) hle hD hN1 h8
  obtain ⟨π, hπ, hker, hAθ, hequiv, hf⟩ := hNS
  have hUr : U ≤ θ.range := by
    intro u hu
    obtain ⟨l, hl⟩ := hAθ u (mem_alternatingGroup.2 (hUsign u hu))
    exact ⟨⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩, hl⟩
  have hUS : U ≤ (S.subgroupOf (L ⊔ S)).map θ :=
    le_theta_S_of_normal_two hA' le_sup_right θ hθS _ rfl U hUN hU2 hUr
      (fun h hh _ u hu => hUnorm h hh u hu)
  have hPS : ∀ p ∈ U, ∃ l : ↥L, (l : G) ∈ S ∧ θ (Subgroup.inclusion le_sup_left l) = p := by
    intro p hp
    obtain ⟨s, hs, hsp⟩ := hUS hp
    obtain ⟨l, hl⟩ := hAθ p (mem_alternatingGroup.2 (hUsign p hp))
    refine ⟨l, ?_, hl⟩
    have h1 : θ (s⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩) = 1 := by
      rw [map_mul, map_inv, hsp, hl, inv_mul_cancel]
    have h2 := hθS _ h1
    have h3 : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    have h4 : (l : G) = (s : G) * ((s⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ : ↥(L ⊔ S)) : G) := by
      simp
    rw [h4]
    exact S.mul_mem h3 h2
  exact false_of_transitive_support hA hL hSL (by omega) ⟨π, hπ, hker, hAθ, hequiv, hf⟩ Δ hΔ5 hΓ U
    hPS hUfix hUtrans

theorem eightTenResidualOutcomes_of_three (h1 : EightTenNodeSFour)
    (h2 : EightTenNodeFourOrbit) (h3 : EightTenNodeColourFour) : EightTenResidualOutcomes :=
  eightTenResidualOutcomes_of_nodes h1 h2 h3 eightTenNodeMatching

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
