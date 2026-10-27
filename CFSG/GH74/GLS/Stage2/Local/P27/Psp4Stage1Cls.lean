module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Part
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem isCentralInvolution_of_isConj {x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
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

theorem isConj_iff_mem_traces {P₁ P₂ : Subgroup G} {a : ℕ} {x₀ t : G}
    (hz : IsCentralInvolution z) (d : Psp4.Data S P₁ P₂ z t a) (hP : P₁ ⊔ P₂ = RC S z)
    (hx : TwoClassData G z S L₁ L₂ q x₀) (htc : IsConj z t) (hsw : Swaps z t L₁ L₂) :
    ∀ y ∈ S, y * y = 1 → y ≠ 1 →
      (IsConj z y ↔ y ∈ Psp4.Zc (P₁ ⊔ P₂) z t) ∧ (IsConj x₀ y ↔ y ∈ Psp4.Xc (P₁ ⊔ P₂) z t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro y hy hy2 hy1
  have hord : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  have hxz : ¬ IsConj z x₀ := fun h => hx.x_nonCentral (isCentralInvolution_of_isConj hz h)
  have hZ : y ∈ Psp4.Zc (P₁ ⊔ P₂) z t → IsConj z y := by
    rintro (hyz | ⟨r, -, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hyz]
    · exact htc.trans (isConj_iff.2 ⟨r, rfl⟩)
  have hX : y ∈ Psp4.Xc (P₁ ⊔ P₂) z t → IsConj x₀ y := by
    rintro (⟨hyR, -, -, hyz⟩ | ⟨r, -, rfl⟩)
    · have hyL : y ∈ LC z := by
        have : y ∈ RC S z := hP ▸ hyR
        exact this.2
      exact (hx.invol_L y hyL hord hyz).1
    · exact (hx.swap_conseq t d.t_mem htc hsw).1.trans (isConj_iff.2 ⟨r, rfl⟩)
  obtain ⟨hpart, -⟩ := d.partition y hy hy2 hy1
  refine ⟨⟨fun hc => ?_, hZ⟩, ⟨fun hc => ?_, hX⟩⟩
  · rcases hpart with h | h
    · exact h
    · exact absurd (hc.trans (hX h).symm) hxz
  · rcases hpart with h | h
    · exact absurd ((hZ h).trans hc.symm) hxz
    · exact h

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1
