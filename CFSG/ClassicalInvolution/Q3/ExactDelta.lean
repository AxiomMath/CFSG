module

public import CFSG.ClassicalInvolution.Q3.Exact
public import CFSG.ClassicalInvolution.Balance.BootstrapDelta

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Generic.DeltaClosure

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ (hΩ : ConjInvariant Ω)
    (hLoc : LocalLieSystems3 Ω) {K F : Subgroup G} {z : G} (hKΩ : K ∈ Ω)
    (hz : IsClassicalMember3 K z) (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hnc : ∀ f ∈ F, f ≠ 1 → f ∉ Subgroup.center G) (hΔ : deltaCore F = ⊥) :
    classicalInvolutionOddCore ↥K = ⊥ := by
  have hle : oddCoreIn K ≤ deltaCore F := by
    refine le_deltaCore fun f hf hf1 => ?_
    have hKf : K ≤ Subgroup.centralizer ({f} : Set G) :=
      hKF.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hf))
    have hKm : K ∈ centralizingMembers Ω {f} := ⟨hKΩ, hKf⟩
    have hKY : K ≤ centralizingLayer Ω {f} := le_centralizingLayer hKm
    have hLie := hLoc {f} (by
      rw [Set.singleton_subset_iff]
      exact hnc f hf hf1)
    obtain ⟨ι, -, ⟨D⟩⟩ := hLie
    have hmemΦ : (K.subgroupOf (centralizingLayer Ω {f})).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {f}))) ∈
        oddQuotientFamily (restrictFamily (centralizingMembers Ω {f})
          (centralizingLayer Ω {f})) :=
      ⟨K.subgroupOf (centralizingLayer Ω {f}), ⟨K, hKm, hKY, rfl⟩, rfl⟩
    have h24 := D.card_eq _ hmemΦ
    exact (oddCoreIn_le_of_card_image_eq hKY hz h24).trans
      (oddCoreIn_centralizingLayer_le hΩ f)
  rw [hΔ, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle

omit [Finite G] in
theorem classicalInvolutionOddCore_conjSub_eq_bot₃ {K : Subgroup G}
    (hK : classicalInvolutionOddCore ↥K = ⊥) (g : G) :
    classicalInvolutionOddCore ↥(conjSub g K) = ⊥ := by
  let e : K ≃* conjSub g K :=
    K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hO : (classicalInvolutionOddCore K).map e.toMonoidHom =
      classicalInvolutionOddCore (conjSub g K) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  rw [← hO, hK, Subgroup.map_bot]

omit [Finite G] in
theorem exactMembers3_of_conjugates {K : Subgroup G} (hK : classicalInvolutionOddCore ↥K = ⊥)
    (hall : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : ExactMembers3 Ω := by
  intro L hL
  obtain ⟨g, rfl⟩ := hall L hL
  exact classicalInvolutionOddCore_conjSub_eq_bot₃ hK g

theorem exactMembers3_of_deltaCore_eq_bot (hΩ : ConjInvariant Ω) (hLoc : LocalLieSystems3 Ω)
    {K F : Subgroup G} {z : G} (hKΩ : K ∈ Ω) (hz : IsClassicalMember3 K z)
    (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hnc : ∀ f ∈ F, f ≠ 1 → f ∉ Subgroup.center G) (hΔ : deltaCore F = ⊥)
    (hall : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) : ExactMembers3 Ω :=
  exactMembers3_of_conjugates
    (classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hΩ hLoc hKΩ hz hKF hnc hΔ) hall

theorem classicalInvolutionOddCore_eq_bot_of_four_centralizer_generated₃ {A : Subgroup G}
    (hOG : CFSG.Open.componentClassificationOddCore G = ⊥) (hne : ∃ a ∈ A, a ≠ 1)
    (hS : Bootstrap.CentralizedDelta A) (h2 : TwoBalancedWrt A)
    (hgen : (⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)) = ⊤)
    (hΩ : ConjInvariant Ω) (hLoc : LocalLieSystems3 Ω)
    {K F : Subgroup G} {z : G} (hKΩ : K ∈ Ω) (hz : IsClassicalMember3 K z)
    (hF : F ∈ signalizerFunctorEk 2 2 A) (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hnc : ∀ f ∈ F, f ≠ 1 → f ∉ Subgroup.center G) :
    classicalInvolutionOddCore ↥K = ⊥ :=
  classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hΩ hLoc hKΩ hz hKF hnc
    (Bootstrap.deltaCore_eq_bot_of_four_centralizer_generated hOG hne hS h2 hgen F hF)

end CFSG.ClassicalInvolution.Q3
