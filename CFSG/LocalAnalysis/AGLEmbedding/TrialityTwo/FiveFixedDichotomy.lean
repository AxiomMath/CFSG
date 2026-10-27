module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.Defs
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveChevalley
import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.FiveDichotomy

public section

namespace CFSG.AGLEmbedding.TrialityTwo

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
open CFSG.ClassicalGroups.Orthogonal QuadraticMap Module Five

theorem fiveFixedDichotomy_holds : FiveFixedDichotomy := by
  intro K _ _ hK g hg
  simp only [statedDerivedSubspaceAction_apply, IsSingularPoint, ← coe_quadPlus,
    mem_singularSubspaces]
  set φ := toLinEquiv (Fin 4 ⊕ Fin 4) K g.val with hφ
  have hφQ : ∀ x, quadPlus 4 K (φ x) = quadPlus 4 K x :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.commutator_le_self _
      (Subgroup.mem_comap.mp ((statedOmega_eq_comap (coe_quadPlus 4 K)).le g.2)))
  have hg5 : g ^ 5 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hφ5 : φ ^ 5 = 1 := by
    rw [hφ, ← map_pow, ← Subgroup.coe_pow, hg5, Subgroup.coe_one, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h
    have hg1 : g = 1 :=
      Subtype.ext ((toLinEquiv (Fin 4 ⊕ Fin 4) K).injective (h.trans (map_one _).symm))
    rw [hg1, orderOf_one] at hg
    norm_num at hg
  have hV : finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hQ : ∀ x, (∀ y, polar (quadPlus 4 K) x y = 0) → x = 0 := by
    intro x hx
    funext j
    rcases j with j | j
    · rw [Pi.zero_apply, ← polar_quadPlus_single_inr 4 K x j]
      exact hx _
    · rw [Pi.zero_apply, ← polar_quadPlus_single_inl 4 K x j]
      exact hx _
  constructor
  · rintro ⟨W, ⟨hW1, -⟩, hWφ⟩ ⟨U, ⟨hU4, hUQ⟩, hUφ⟩
    have hWne : W ≠ ⊥ := by
      rintro rfl
      rw [finrank_bot] at hW1
      exact zero_ne_one hW1
    obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hWv : W = K ∙ v := (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem v W).mpr hvW)
      (by rw [finrank_span_singleton hv0, hW1])).symm
    have hφv : φ v ∈ W := by
      rw [← hWφ]
      exact Submodule.mem_map_of_mem hvW
    rw [hWv, Submodule.mem_span_singleton] at hφv
    obtain ⟨a, ha⟩ := hφv
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul, eq_comm, LinearEquiv.map_eq_zero_iff] at ha
      exact hv0 ha
    rw [eq_one_of_ne_zero hK ha0, one_smul] at ha
    exact false_of_fixed_of_solid hK hV hQ hφQ hφ5 hφ1 hv0 ha.symm hU4 hUQ fun x hx => by
      rw [← hUφ]
      exact Submodule.mem_map_of_mem hx
  · intro hno
    by_contra hfix
    apply hno
    have hfix' : ∀ c, φ c = c → quadPlus 4 K c = 0 → c = 0 := by
      intro c hc hQc
      by_contra hc0
      refine hfix ⟨K ∙ c, ⟨finrank_span_singleton hc0, fun x hx => ?_⟩, ?_⟩
      · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [QuadraticMap.map_smul, hQc, smul_zero]
      · rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, hc]
    obtain ⟨v, hv0, h0, h1, h2⟩ := exists_ne_zero_common_zero hK (by simp) (quadPlus 4 K)
      (LinearMap.BilinMap.toQuadraticMap ((polarBilin (quadPlus 4 K)).compl₂ φ.toLinearMap))
      (LinearMap.BilinMap.toQuadraticMap
        ((polarBilin (quadPlus 4 K)).compl₂ (φ ^ 2).toLinearMap))
    simp only [LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.compl₂_apply,
      polarBilin_apply_apply, LinearEquiv.coe_coe] at h1 h2
    obtain ⟨U, hU4, hUQ, hUφ⟩ := exists_solid_of_forall_fixed hK hV hφQ hφ5 hfix' hv0 h0 h1 h2
    exact ⟨U, ⟨hU4, hUQ⟩, hUφ⟩

end CFSG.AGLEmbedding.TrialityTwo
