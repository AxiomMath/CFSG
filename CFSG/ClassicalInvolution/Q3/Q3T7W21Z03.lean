module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25U04

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
    CFSG.ClassicalInvolution.Asc77.AscE184Sect
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem layerAut_eq_one_iff (hc : ConjInvariant Ω) {c w : G}
    (hw : w ∈ Subgroup.centralizer ({c} : Set G)) :
    CX.actW hc c ⟨w, hw⟩ = 1 ↔
      ∀ y ∈ ExactLayer.exactLayer Ω c,
        w * y * w⁻¹ * y⁻¹ ∈ oddCoreOf (ExactLayer.exactLayer Ω c) := by
  constructor
  · intro h1 y hy
    have h2 : C25Y.layerAut (ExactLayer.exactLayer Ω c) (ExactLayer.conjSub_exactLayer hc hw)
        (QuotientGroup.mk ⟨y, hy⟩) = QuotientGroup.mk ⟨y, hy⟩ := by
      have := congrArg (fun a => a (QuotientGroup.mk ⟨y, hy⟩)) h1
      simpa [CX.actW_apply] using this
    exact (C5O.layerAut_mk_eq_iff (ExactLayer.exactLayer Ω c)
      (ExactLayer.conjSub_exactLayer hc hw) ⟨y, hy⟩).mp h2
  · intro h
    ext y
    refine QuotientGroup.induction_on y fun y => ?_
    rw [MulAut.one_apply, CX.actW_apply]
    exact (C5O.layerAut_mk_eq_iff (ExactLayer.exactLayer Ω c)
      (ExactLayer.conjSub_exactLayer hc hw) y).mpr (h y y.2)

theorem omegaNbr_map_of_commutes {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
    {N : Subgroup Y} [N.Normal] (hΛ' : HypOmegaModT (quotFamily Λ N)) (hN : Odd (Nat.card N))
    {M₁ M₂ V₁ V₂ : Subgroup Y} (hM₁ : M₁ ∈ Λ) (hM₂ : M₂ ∈ Λ) (hV₁ : IsSylow2In V₁ M₁)
    (hV₂ : IsSylow2In V₂ M₂) (hc : Commutes V₁ V₂)
    (hV₂N : V₂ ≤ Subgroup.normalizer (M₁ : Set Y)) :
    M₂.map (QuotientGroup.mk' N) ∈
      omegaNbr (quotFamily Λ N) (M₁.map (QuotientGroup.mk' N)) := by
  refine ⟨map_mem_quotFamily hM₂, (map_ne_of_commutes_sylow hΛ' hN hM₁ hV₁ hV₂ hc).symm,
    V₂.map (QuotientGroup.mk' N),
    mem_RSet_of_isSylow2In (map_mem_quotFamily hM₂) (isSylow2In_map_mk hN hV₂),
    Subgroup.map_mono hV₂.1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_normalizer_map (hV₂N hx)

theorem actW_mul_inv_mem_oddCore (hΩ : HypOmegaModT Ω) {c : G}
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {J : Subgroup G} (hJ : J ∈ ExactLayer.tqMembers Ω c)
    {v : G} (hvc : v ∈ Subgroup.centralizer ({c} : Set G))
    (hvJ : v ∈ Balance.Bootstrap.trivialOnQuot J) :
    ∀ a ∈ T7H.exactImg Ω c J,
      CX.actW hΩ.conjInvariant c ⟨v, hvc⟩ a * a⁻¹ ∈ oddCoreOf (T7H.exactImg Ω c J) := by
  intro a ha
  obtain ⟨k₀, hk₀, rfl⟩ := Subgroup.mem_map.mp ha
  have hk : (k₀ : G) ∈ ExactLayer.exactCore c J := Subgroup.mem_subgroupOf.mp hk₀
  have hvk : v * (k₀ : G) * v⁻¹ ∈ ExactLayer.exactLayer Ω c := by
    have h1 : v * (k₀ : G) * v⁻¹ ∈ conjSub v (ExactLayer.exactLayer Ω c) :=
      Generic.conj_mem_conjSub k₀.2
    rwa [ExactLayer.conjSub_exactLayer hΩ.conjInvariant hvc] at h1
  obtain ⟨n, hn, heq⟩ := S22.exists_odd_mul hΩ hc2 hJ hvc hvJ hk k₀.2 hvk
  have hact : CX.actW hΩ.conjInvariant c ⟨v, hvc⟩ (QuotientGroup.mk' _ k₀) =
      T7H.toBar Ω c (v * (k₀ : G) * v⁻¹) hvk := by
    rw [CX.actW_apply, QuotientGroup.mk'_apply, C25Y.layerAut_mk]
    rfl
  have hkbar : QuotientGroup.mk' (classicalInvolutionOddCore ↥(ExactLayer.exactLayer Ω c)) k₀ =
      T7H.toBar Ω c (k₀ : G) k₀.2 := rfl
  rw [hact, heq, hkbar, mul_inv_cancel_right]
  exact hn

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8
