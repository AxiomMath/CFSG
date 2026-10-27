module

public import CFSG.GH74.GLS.Stage2.Local.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

section Choice

variable {G : Type} [Group G] {z : G}

theorem exists_prop27_y (h : ∃ x₀ ∈ Cen z, IsNonCentralInvolution x₀) :
    ∃ x ∈ Cen z, IsNonCentralInvolution x ∧
      (Ixz z x ≠ ⊥ ∨ ∀ x' ∈ Cen z, IsNonCentralInvolution x' → Ixz z x' = ⊥) := by
  by_cases hex : ∃ x' ∈ Cen z, IsNonCentralInvolution x' ∧ Ixz z x' ≠ ⊥
  · obtain ⟨x', hx'C, hx'nc, hI⟩ := hex
    exact ⟨x', hx'C, hx'nc, Or.inl hI⟩
  · push Not at hex
    obtain ⟨x₀, hx₀C, hx₀nc⟩ := h
    exact ⟨x₀, hx₀C, hx₀nc, Or.inr hex⟩

theorem isCentralInvolution_of_isConj' {z x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
    IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

end Choice

end CFSG.GH74.GLS.Stage2.Local.Prop28
