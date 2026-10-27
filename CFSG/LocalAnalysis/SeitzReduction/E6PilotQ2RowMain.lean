module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotQ2RowOverlap
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapCoverCT
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotSwapConjGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)
open CFSG.SeitzReduction.LinearPilot (CatSLmSporadicAt)
open CFSG.SeitzReduction.F4Pilot (F4Work)

@[expose] def E6TwoOverlapInputAll : Prop :=
  ∀ (K : Type) [Field K], E6TwoOverlapInput K

@[expose] def E6TwoFieldRowInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E6 K) (t : G), F4Work L K t 1 →
    ∀ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K → IsCyclic A → Nat.card A = 3 →
    ∀ htX : t ∈ centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G),
      NeighbourOvergroupSLFieldKind
        (QuotientGroup.mk' (oddCore
          (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))) ⟨t, htX⟩)
        (((rootLeviG e).subgroupOf
            (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))).map
          (QuotientGroup.mk' (oddCore
            (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))))) 6 1 → False

theorem e6TwoRowsInput_of_inputs (hO : E6TwoOverlapInputAll) (hF : E6TwoFieldRowInput) :
    E6TwoRowsInput := by
  intro G _ _ L K _ _ _ e t hw A hAJ hcyc hA htX hNO
  rcases fieldKind_or_swapKind_of_neighbourOvergroupSLField hNO with hk | hk
  · exact hF G L K e t hw A hAJ hcyc hA htX hk
  · exact false_of_swapRow_E6_two (hO K) hw e hAJ hA htX hk

theorem seitzExclusion_highE6_of_q2RowInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : CatSLmSporadicAt 6) (hO : E6TwoOverlapInputAll) (hF : E6TwoFieldRowInput) :
    SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_xchar_two hGLS hSpor e6SwapRowCTInput_holds e6SwapRowUniqueInput_holds
    (e6TwoRowsInput_of_inputs hO hF)

theorem e6TwoOverlapInputAll_holds : E6TwoOverlapInputAll :=
  fun _ _ => e6TwoOverlapInput_holds

theorem seitzExclusion_highE6_of_q2FieldRow (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : CatSLmSporadicAt 6) (hF : E6TwoFieldRowInput) :
    SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_q2RowInputs hGLS hSpor e6TwoOverlapInputAll_holds hF

@[expose] def E6TwoFieldRowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K] [Finite K] [CharP K 2]
    (e : L ≃* adjointGroup .E6 K) (t : G), F4Work L K t 1 →
    ∀ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K → IsCyclic A → Nat.card A = 3 →
    ∀ htX : t ∈ centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G),
      NeighbourOvergroupSLFieldKind
        (QuotientGroup.mk' (oddCore
          (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))) ⟨t, htX⟩)
        (((rootLeviG e).subgroupOf
            (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))).map
          (QuotientGroup.mk' (oddCore
            (centralizer ((A.map e.symm.toMonoidHom).map L.subtype : Set G))))) 6 1 →
      ∃ (G₀ : Subgroup G) (K₂ : Type) (_ : Field K₂), Nat.card K₂ = 4 ∧ ⁅G₀, G₀⁆ = G₀ ∧
        Odd (Nat.card (center G₀)) ∧ Nonempty (G₀ ⧸ center G₀ ≃* adjointGroup .E6 K₂) ∧
        t ∈ normalizer (G₀ : Set G) ∧
        ∀ h : G, t ∈ normalizer (CFSG.conjugate G₀ h : Set G) →
          CFSG.conjugate G₀ h ⊓ centralizer ({t} : Set G) = L → CFSG.conjugate G₀ h = G₀

theorem e6TwoFieldRowInput_of_CT (h : E6TwoFieldRowCTInput) : E6TwoFieldRowInput := by
  intro G _ _ L K _ _ _ e t hw A hAJ hcyc hA htX hk
  obtain ⟨G₀, K₂, _, hK₂, hperf, hZ, ⟨e₀⟩, htN, hstep3⟩ :=
    h G L K e t hw A hAJ hcyc hA htX hk
  have hK₂' : Nat.card K₂ = 2 ^ (2 * 1) := by rw [hK₂]; norm_num
  have := F4Pilot.finite_of_natCard_eq_two_pow hK₂'
  obtain ⟨⟨σ', -, hσ'1, -, φ, hφ⟩, -⟩ := inf_centralizer_eq_of_mem_normalizer_E6_cover
    hw.standard hw.card_eq e hw.orderOf_eq hw.inf_eq hperf hZ hK₂' e₀ htN
  have huniq : ∀ g : G, g⁻¹ * t * g ∈ normalizer (G₀ : Set G) → g ∈ normalizer (G₀ : Set G) := by
    intro g hg
    have htM := F4Pilot.mem_normalizer_conjugate_inv hg
    have hC := inf_centralizer_conjugate_eq_E6_cover hw.standard hw.card_eq e hw.orderOf_eq
      hw.inf_eq hperf hZ hK₂' e₀ g⁻¹ htM
    exact F4Pilot.mem_normalizer_of_conjugate_inv_eq (hstep3 g⁻¹ htM hC)
  have := hw.standard.simple
  exact false_of_simple_of_E6_field_quot_of_odd (f := 1) odd_one K₂ hK₂' e₀ htN hw.orderOf_eq
    ⟨σ', φ, hσ'1, hφ⟩ huniq

theorem seitzExclusion_highE6_of_q2CT (hGLS : GLS3OddLieAutComponentsInput)
    (hSpor : CatSLmSporadicAt 6) (hCT : E6TwoFieldRowCTInput) :
    SeitzExclusion (HighExceptional .E6) :=
  seitzExclusion_highE6_of_q2FieldRow hGLS hSpor (e6TwoFieldRowInput_of_CT hCT)

end CFSG.SeitzReduction.E6Pilot
