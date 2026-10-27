module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.SLTwo
public import CFSG.LocalAnalysis.ComponentClassification.GS82DPrimeDefs
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Defs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

private theorem center_le_fusionZStar_aux (H : Type*) [Group H] :
    center H ≤ Open.fusionZStar H := by
  intro x hx
  show QuotientGroup.mk' _ x ∈ center _
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]

theorem isDatum_of_central {G : Type} [Group G] [Finite G] {q₀ : ℕ} {v : G} {M N : Subgroup G}
    {c : G} (hv : orderOf v = 2) (hM : Omega.IsComponentIn M (centralizer ({v} : Set G)))
    (hNM : N ≤ M) (hq : Odd q₀) (h5 : 5 ≤ q₀) (hSL : HarrisLit.IsSLTwoOver q₀ ↥N)
    (hc : orderOf c = 2) (hcN : c ∈ N) (hcM : c ∈ (center ↥M).map M.subtype) :
    GS82PumpInputs.IsDatum q₀ v M N c := by
  have hZ : c ∈ (Open.fusionZStar ↥M).map M.subtype :=
    Subgroup.map_mono (f := M.subtype) (center_le_fusionZStar_aux ↥M) hcM
  have hNc : N ≤ centralizer ({c} : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨c₀, hc₀, hc₀c⟩ := Subgroup.mem_map.mp hcM
    rw [Subgroup.subtype_apply] at hc₀c
    have hnc : (⟨n, hNM hn⟩ : ↥M) * c₀ = c₀ * ⟨n, hNM hn⟩ :=
      Subgroup.mem_center_iff.mp hc₀ ⟨n, hNM hn⟩
    have key := congrArg (fun x : ↥M => (x : G)) hnc
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc₀c] at key
    exact key
  exact ⟨hv, hM.1, CFSG.LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hM.2,
    hNM, Subgroup.isPerfect_iff.mp (isPerfect_of_isSLTwoOver h5 hSL),
    isSLTwoOver_quotient hq h5 hSL, hc, hcN, hNc, hZ⟩

end CFSG.OddStandard.SmallF3.HypA2
