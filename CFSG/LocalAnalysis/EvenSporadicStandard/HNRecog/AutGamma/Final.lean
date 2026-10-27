module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.IndexLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.LinesAll
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.OutHS
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Perp3A
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Stab

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Monster.GMS

variable {G : Type} [Group G] {a z : G}

theorem finite_aut [Finite G] : Finite (Gamma a ≃g Gamma a) :=
  Finite.of_injective (fun σ : Gamma a ≃g Gamma a => (σ : ConjVert a → ConjVert a))
    DFunLike.coe_injective

theorem segevSection5_of_inputs [Finite G] [IsSimpleGroup G] (hF : IsF5Type a z)
    (hL : F5Local G a z) (hI : SegevInputs a z) :
    Function.Injective (gammaConj a) ∧
      (gammaConj a).range = commutator (Gamma a ≃g Gamma a) := by
  obtain ⟨hlines, hperp, hout⟩ := hI
  have hinj := gammaConj_injective hF hL
  haveI hnorm : (gammaConj a).range.Normal := normal_range_gammaConj hF hL hlines hperp
  haveI : Finite (Gamma a ≃g Gamma a) := finite_aut
  have hidx : (gammaConj a).range.index ≤ 2 := by
    refine index_le_two_of_sup_eq_top (gammaConj a).range (vertexStab a) range_sup_vertexStab ?_
      (gxEquivSubgroupOf hinj) hout
    intro σ _ hcomm
    have hc : ∀ g ∈ Gx a, σ * gammaConj a g = gammaConj a g * σ := fun g hg =>
      hcomm (gammaConj a g)
        (Subgroup.mem_inf.2 ⟨⟨g, rfl⟩, (gammaConj_mem_vertexStab_iff g).2 hg⟩)
    rcases eq_one_or_eq_gammaConj_of_centralizes hF hL hlines hperp σ hc with h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact ⟨a, rfl⟩
  refine ⟨hinj, le_antisymm ?_ (commutator_le_of_index_le_two _ hidx)⟩
  let T : Subgroup G := ⊤
  let T' : Subgroup (Gamma a ≃g Gamma a) := ⊤
  have hperf : ⁅T, T⁆ = T := by
    rw [← commutator_def]
    exact commutator_eq_top hF hL
  calc (gammaConj a).range = T.map (gammaConj a) := MonoidHom.range_eq_map _
    _ = (⁅T, T⁆).map (gammaConj a) := by rw [hperf]
    _ = ⁅T.map (gammaConj a), T.map (gammaConj a)⁆ := Subgroup.map_commutator _ _ _
    _ ≤ ⁅T', T'⁆ := Subgroup.commutator_mono le_top le_top
    _ = commutator (Gamma a ≃g Gamma a) := (commutator_def _).symm

theorem segevInputs_of_f5Local
    [Finite G] (hF : IsF5Type a z) (hL : F5Local G a z)
    (hnc : ¬ IsConj a z) : SegevInputs a z where
  lines := linesThrough_of_f5Local hF hL
  perp := perpThreeA_of_f5Local hF hL hnc
  out := by
    obtain ⟨E, hE⟩ := hF.cent_a
    exact index_range_conj_le_two hE

theorem segevSection5_of_twoHSInterface
    (hI : TwoHSInterface) :
    SegevSection5 := by
  intro G _ _ _ a z hF hL
  exact segevSection5_of_inputs hF hL
    (segevInputs_of_f5Local hF hL (not_isConj_of_isF5Type hI hF))

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
