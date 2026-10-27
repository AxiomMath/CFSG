module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4Model
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.SeitzReduction.F4Pilot (PerfectTwistedFusion PerfectTwistedFusion.of_conj)
open CFSG.SeitzReduction.E6Pilot (a2Roots a2Root a2Gen a2Pair)

section Aut

variable {K : Type} [Field K] (σ : K →+* K)

theorem diagramMap_mem_normalizer (hσσ : ∀ c, σ (σ c) = c) :
    diagramMap TwistTag.E6 K ∈ normalizer (graphFixedRootGroup TwistTag.E6 K σ : Set _) := by
  have hmap := map_conj_diagramMap_graphFixedRootGroup
    (RingEquiv.ofBijective σ (Function.Involutive.bijective hσσ)) (RingHom.ext fun _ => rfl) hσσ
  have hP2 := diagramMap_E6_mul_self (K := K)
  have hPinv : (diagramMap TwistTag.E6 K)⁻¹ = diagramMap TwistTag.E6 K :=
    (eq_inv_of_mul_eq_one_left hP2).symm
  have hmem : ∀ h ∈ graphFixedRootGroup TwistTag.E6 K σ,
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹ ∈
        graphFixedRootGroup TwistTag.E6 K σ :=
    fun h hh => E6GraphLevi.conj_mem_of_map_eq hmap hh
  refine mem_normalizer_iff.2 fun h => ⟨hmem h, fun hh => ?_⟩
  have e : h = diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K * h *
      (diagramMap TwistTag.E6 K)⁻¹) * (diagramMap TwistTag.E6 K)⁻¹ := by
    rw [hPinv, ← mul_assoc, ← mul_assoc, hP2, one_mul, mul_assoc, hP2, mul_one]
  rw [e]
  exact hmem _ hh

@[expose] noncomputable def etaAut (hσσ : ∀ c, σ (σ c) = c) :
    MulAut (graphFixedRootGroup TwistTag.E6 K σ) :=
  (graphFixedRootGroup TwistTag.E6 K σ).normalizerMonoidHom
    ⟨diagramMap TwistTag.E6 K, diagramMap_mem_normalizer σ hσσ⟩

theorem coe_etaAut (hσσ : ∀ c, σ (σ c) = c) (g : graphFixedRootGroup TwistTag.E6 K σ) :
    (etaAut σ hσσ g : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ g

variable [CharP K 2]

theorem pinnedX_highRoot_one_mem :
    pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  pinnedX_mem_graphFixedRootGroup_of_fixed σ isRoot_e6HighestRoot permLattice_e6HighestRoot
    (map_one σ)

@[expose] noncomputable def xiAut (hσσ : ∀ c, σ (σ c) = c) :
    MulAut (graphFixedRootGroup TwistTag.E6 K σ) :=
  MulAut.conj (⟨_, pinnedX_highRoot_one_mem σ⟩ : graphFixedRootGroup TwistTag.E6 K σ) *
    etaAut σ hσσ

theorem coe_xiAut (hσσ : ∀ c, σ (σ c) = c) (g : graphFixedRootGroup TwistTag.E6 K σ) :
    (xiAut σ hσσ g : ModGL TwistTag.E6.tag K) =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
        (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
          (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ := by
  rw [xiAut, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_etaAut]

end Aut

section Fusion

variable {K : Type} [Field K] [CharP K 2] (σ : K →+* K)

theorem coe_a2Gen_mem (hσσ : ∀ c, σ (σ c) = c) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ a2Roots) (d : K) :
    (a2Gen σ β d : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
  twistedE6PairX_mem_graphFixedRootGroup hσσ (E6Pilot.a2Roots_isRoot hβ).1 d

theorem diagramMap_conj_a2Gen (hσσ : ∀ c, σ (σ c) = c) {β : Fin TwistTag.E6.tag.rank → ℤ}
    (hβ : β ∈ a2Roots) (d : K) :
    diagramMap TwistTag.E6 K * (a2Gen σ β d : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹ = a2Gen σ β (σ d) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [E6Pilot.diagramMap_conj_eq_twistHom_id, E6Pilot.coe_a2Gen, map_mul,
    twistHom_pinnedX_eq_of_charTwo h2 (RingHom.id K) (E6Pilot.a2Roots_isRoot hβ).1,
    twistHom_pinnedX_eq_of_charTwo h2 (RingHom.id K) (E6Pilot.a2Roots_isRoot hβ).2,
    E6Pilot.perm_perm_a2Roots hβ, RingHom.id_apply, RingHom.id_apply, E6Pilot.coe_a2Gen, hσσ]
  exact (E6Pilot.commute_a2Roots hβ hβ (σ d) d).eq.symm

end Fusion

section HR4

theorem conj_etaAut_or_xiAut_of_outer {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ), α ^ 2 = 1 →
      α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.E6 K σ →*
        MulAut (graphFixedRootGroup TwistTag.E6 K σ)).range →
      (∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
          φ * α * φ⁻¹ = etaAut σ (apply_apply_eq hK hσ)) ∨
        ∃ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
          φ * α * φ⁻¹ = xiAut σ (apply_apply_eq hK hσ)) ∧
      ∀ φ : MulAut (graphFixedRootGroup TwistTag.E6 K σ),
        φ * etaAut σ (apply_apply_eq hK hσ) * φ⁻¹ ≠ xiAut σ (apply_apply_eq hK hσ) := by
  obtain ⟨ht, η, hη, -, -, hclass, hnc, -⟩ :=
    (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ hσ
  have hηe : η = etaAut σ (apply_apply_eq hK hσ) :=
    MulEquiv.ext fun g => Subtype.ext (by rw [hη, coe_etaAut])
  have hξe : MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η =
      xiAut σ (apply_apply_eq hK hσ) := by
    rw [hηe]
    rfl
  refine ⟨fun α hα hαo => ?_, fun φ => ?_⟩
  · rcases hclass α hα (fun c h => hαo ⟨c, h.symm⟩) with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
    · exact Or.inl ⟨φ, hφ.trans hηe⟩
    · exact Or.inr ⟨φ, hφ.trans hξe⟩
  · rw [← hηe, ← hξe]
    exact hnc φ

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

end HR4

end CFSG.SeitzReduction.TwistedE6Pilot
