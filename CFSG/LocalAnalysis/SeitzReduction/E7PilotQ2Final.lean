module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.SeitzReduction.OmegaPilot (OmegaCatalogueClausesAt)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

section Inputs

theorem seitzExclusion_highE7_of_q2_fieldRow (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaPilot.OmegaNotOddLieInputAt 6) (hSpor : OmegaPilot.CatOmegaSporadicAt 6)
    (hF : E7TwoFieldRowInput) : SeitzExclusion (HighExceptional .E7) :=
  seitzExclusion_highE7_of_q2_inputs hGLS hXodd hSpor (fun K _ => e7TwoOverlapInput K) hF

end Inputs

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {t : G}

theorem false_of_E7_two_of_fieldRow_subgroup (hw : E7Work L K t 1) (e : L ≃* adjointGroup .E7 K)
    {G₀ : Subgroup G} {K₂ : Type} [Field K₂] (hK₂ : Nat.card K₂ = 2 ^ (2 * 1))
    (e₀ : G₀ ≃* adjointGroup .E7 K₂) (hLG : L ≤ G₀)
    (hCN : centralizer (L : Set G) ≤ normalizer (G₀ : Set G)) : False := by
  have hK2 : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have : Finite K₂ := F4Pilot.finite_of_natCard_eq_two_pow hK₂
  have : CharP K₂ 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hK₂
  have hKt := hw.inf_eq e
  have hNL : normalizer (L : Set G) ≤ normalizer (G₀ : Set G) := by
    intro n hn
    obtain ⟨l, hl⟩ := forall_mem_range_conj_of_mulEquiv_E7_two hK2 e
      (L.normalizerMonoidHom ⟨n, hn⟩)
    have hc : (l : G)⁻¹ * n ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := congrArg (fun β : MulAut L => ((β ⟨y, hy⟩ : L) : G)) hl
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.normalizerMonoidHom_apply_apply_coe] at h1
      calc y * ((l : G)⁻¹ * n) = (l : G)⁻¹ * ((l : G) * y * (l : G)⁻¹) * n := by group
        _ = (l : G)⁻¹ * (n * y * n⁻¹) * n := by rw [h1]
        _ = (l : G)⁻¹ * n * y := by group
    have hnl : n = (l : G) * ((l : G)⁻¹ * n) := by group
    rw [hnl]
    exact mul_mem (le_normalizer (hLG l.2)) (hCN hc)
  have htN : t ∈ normalizer (G₀ : Set G) := hCN hw.mem_centralizer
  have htG : t ∉ G₀ := not_mem_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀
  have htC : t ∉ centralizer (G₀ : Set G) :=
    not_mem_centralizer_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀
  have hZ := EPilot.odd_card_centralizer_of_inf_eq_zpowers hKt hLG hw.orderOf_eq htN htC
  have huniq := unique_of_step3_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀
    (eq_of_conjugate_E7_field hw.standard hw.card_eq e hw.orderOf_eq hKt hK₂ e₀ htN hNL)
  have := hw.seitz.1
  exact false_of_simple_of_E7_odd hZ hK₂ e₀ htN hw.orderOf_eq htG huniq

@[expose] def E7TwoFieldRowCTInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K : Type) [Field K]
    (e : L ≃* adjointGroup .E7 K) (t : G), E7Work L K t 1 → HR8FieldE7Two e t 1 →
    ∃ (K₂ : Type) (_ : Field K₂) (G₀ : Subgroup G), Nat.card K₂ = 2 ^ (2 * 1) ∧
      Nonempty (G₀ ≃* adjointGroup .E7 K₂) ∧ L ≤ G₀ ∧
        centralizer (L : Set G) ≤ normalizer (G₀ : Set G)

theorem e7TwoFieldRowInput_of_CT (h : E7TwoFieldRowCTInput) : E7TwoFieldRowInput := by
  intro G _ _ L K _ e t hw hF
  obtain ⟨K₂, _, G₀, hK₂, ⟨e₀⟩, hLG, hCN⟩ := h G L K e t hw hF
  exact false_of_E7_two_of_fieldRow_subgroup hw e hK₂ e₀ hLG hCN

end Endgame

end CFSG.SeitzReduction.E7Pilot
