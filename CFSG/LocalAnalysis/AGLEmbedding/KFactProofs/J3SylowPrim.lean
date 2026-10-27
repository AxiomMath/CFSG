module

public import CFSG.Sporadic.Bridge.TwoGen
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import Certificates.Data.CFSGNative.Bridge.SurjA
public import Mathlib

public section

namespace CFSG.AGLEmbedding.KFactProofs.J3Sylow

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Sporadic.Bridge.TwoGen.Native

theorem isCoatom_stabilizer {X Ω : Type*} [Group X] [MulAction X Ω] (ω₀ : Ω)
    (htrans : ∀ ω, ∃ g : X, g • ω₀ = ω) (hne : ∃ ω, ω ≠ ω₀)
    (S₀ : Set X) (hS₀ : ∀ g ∈ S₀, g • ω₀ = ω₀) (R : Set Ω)
    (hcover : ∀ ω, ∃ r ∈ R, ∃ h ∈ Subgroup.closure S₀, h • r = ω)
    (hreps : ∀ r ∈ R, r ≠ ω₀ → ∃ g : X, g • ω₀ = r ∧
      ∀ ω, ∃ k ∈ Subgroup.closure (S₀ ∪ {g}), k • ω₀ = ω) :
    IsCoatom (MulAction.stabilizer X ω₀) := by
  set H := MulAction.stabilizer X ω₀ with hH
  have hS : Subgroup.closure S₀ ≤ H := (Subgroup.closure_le H).2 fun g hg =>
    (MulAction.mem_stabilizer_iff).2 (hS₀ g hg)
  refine ⟨?_, fun Y hY => ?_⟩
  · intro htop
    obtain ⟨ω, hω⟩ := hne
    obtain ⟨g, hg⟩ := htrans ω
    have : g ∈ H := htop ▸ Subgroup.mem_top g
    exact hω (hg.symm.trans ((MulAction.mem_stabilizer_iff).1 this))
  · obtain ⟨y, hyY, hyH⟩ := IsConcreteLE.exists_of_lt hY
    rw [eq_top_iff]
    intro x _
    obtain ⟨r, hrR, h, hh, hhr⟩ := hcover (y • ω₀)
    have hhH : h ∈ H := hS hh
    have hrω : r ≠ ω₀ := by
      rintro rfl
      exact hyH ((MulAction.mem_stabilizer_iff).2
        (hhr.symm.trans ((MulAction.mem_stabilizer_iff).1 hhH)))
    obtain ⟨g, hgr, hK⟩ := hreps r hrR hrω
    have hgY : g ∈ Y := by
      have h1 : y⁻¹ * h * g ∈ H := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hgr, hhr, inv_smul_smul]
      have h2 : g = h⁻¹ * (y * (y⁻¹ * h * g)) := by group
      rw [h2]
      exact Y.mul_mem (Y.inv_mem (hY.le hhH)) (Y.mul_mem hyY (hY.le h1))
    have hKY : Subgroup.closure (S₀ ∪ {g}) ≤ Y := by
      rw [Subgroup.closure_le Y]
      rintro z (hz | hz)
      · exact hY.le (hS (Subgroup.subset_closure hz))
      · rw [Set.mem_singleton_iff.1 hz]; exact hgY
    obtain ⟨k, hk, hkx⟩ := hK (x • ω₀)
    have hkxH : k⁻¹ * x ∈ H := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ← hkx, inv_smul_smul]
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact Y.mul_mem (hKY hk) (hY.le hkxH)

end CFSG.AGLEmbedding.KFactProofs.J3Sylow
