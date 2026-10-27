module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4Basic
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion)

theorem diagramMap_conj_eq_twistHom_id {K : Type} [Field K] (g : ModGL TwistTag.E6.tag K) :
    diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ =
      twistHom TwistTag.E6 K (RingHom.id K) g := by
  rw [← conj_diagramMap_eq_twistHom]
  rfl


variable {K : Type} [Field K] [CharP K 2]

theorem perfectTwistedFusion_of_twistHom_E6 (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)
    (T : ModGL TwistTag.E6.tag K)
    (hT : ∀ β ∈ a2Roots, ∀ c : K, Commute (pinnedX TwistTag.E6.tag K β c) T ∧
      Commute (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm β) c) T)
    (α : MulAut (adjointGroup TwistTag.E6.tag K))
    (hα : ∀ g, (α g : ModGL TwistTag.E6.tag K) = T * twistHom TwistTag.E6 K σ g * T⁻¹) :
    PerfectTwistedFusion α := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set m : adjointGroup TwistTag.E6.tag K :=
    ⟨pinnedX TwistTag.E6.tag K a2Root 1, pinnedX_mem_adjointGroup _ _⟩
  have hαm : (α m : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm a2Root) (σ 1) := by
    rw [hα, twistHom_pinnedX_eq_of_charTwo h2 σ (a2Roots_isRoot a2Root_mem).1]
    rw [← ((hT a2Root a2Root_mem (σ 1)).2).eq, mul_inv_cancel_right]
  refine ⟨m, a2Gen σ a2Root 1, a2Gen_ne_one σ one_ne_zero, ?_, a2Pair σ Set.univ,
    commutator_a2Pair σ (Set.mem_univ _), a2Gen_mem_a2Pair σ a2Root_mem (Set.mem_univ _),
    fun p hp => apply_eq_self_of_mem_closure (β := α) ?_ hp⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hαm]
    exact inv_pinnedX_mul_pinnedX_eq_a2Gen σ a2Root_mem 1
  · rintro _ ⟨β, hβ, c, -, rfl⟩
    apply Subtype.ext
    rw [hα, twistHom_a2Gen σ hσσ hβ c, coe_a2Gen,
      ← (((hT β hβ c).1).mul_left (hT β hβ (σ c)).2).eq, mul_inv_cancel_right]

theorem perfectTwistedFusion_graphField_E6 (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c) :
    PerfectTwistedFusion
      (diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag σ) := by
  refine perfectTwistedFusion_of_twistHom_E6 σ.toRingHom hσσ 1
    (fun _ _ _ => ⟨Commute.one_right _, Commute.one_right _⟩) _ fun g => ?_
  rw [MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut, twistHom_apply, one_mul,
    inv_one, mul_one]

theorem perfectTwistedFusion_graph_E6 (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) :
    PerfectTwistedFusion η :=
  perfectTwistedFusion_of_twistHom_E6 (RingHom.id K) (fun _ => rfl) 1
    (fun _ _ _ => ⟨Commute.one_right _, Commute.one_right _⟩) η fun g => by
      rw [hη, diagramMap_conj_eq_twistHom_id, one_mul, inv_one, mul_one]

theorem perfectTwistedFusion_secondGraph_E6
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
    (η : MulAut (adjointGroup TwistTag.E6.tag K))
    (hη : ∀ g, (η g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) :
    PerfectTwistedFusion (MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag K) * η) :=
  perfectTwistedFusion_of_twistHom_E6 (RingHom.id K) (fun _ => rfl)
    (pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    (fun _ hβ c => commute_a2Roots_highRoot hβ c 1) _ fun g => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hη, diagramMap_conj_eq_twistHom_id]

theorem perfectTwistedFusion_field_E6 (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (hσ1 : ∃ c, σ c ≠ c) : PerfectTwistedFusion (entrywiseAdjointAut TwistTag.E6.tag σ) := by
  obtain ⟨c, hc⟩ := hσ1
  set δ := entrywiseAdjointAut TwistTag.E6.tag σ
  have hδ : ∀ (β : Fin TwistTag.E6.tag.rank → ℤ) (d : K),
      δ (a2Gen (RingHom.id K) β d) = a2Gen (RingHom.id K) β (σ d) := fun β d =>
    Subtype.ext (by rw [coe_entrywiseAdjointAut]; exact entrywise_a2Gen σ.toRingHom β d)
  have hfix : σ (c + σ c) = c + σ c := by rw [map_add, hσσ, add_comm]
  refine ⟨a2Gen (RingHom.id K) a2Root c, a2Gen (RingHom.id K) a2Root (c + σ c),
    a2Gen_ne_one _ fun h => hc (CharTwo.add_eq_zero.1 h).symm, ?_,
    a2Pair (RingHom.id K) {d | σ d = d}, commutator_a2Pair _ (map_one σ),
    a2Gen_mem_a2Pair _ a2Root_mem hfix, fun p hp => apply_eq_self_of_mem_closure (β := δ) ?_ hp⟩
  · rw [hδ, inv_mul_eq_iff_eq_mul, ← a2Gen_add _ a2Root_mem]
    congr 1
    rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
  · rintro _ ⟨β, -, d, hd, rfl⟩
    rw [hδ, show σ d = d from hd]

end CFSG.SeitzReduction.E6Pilot
