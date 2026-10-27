module

public import CFSG.GH74.GLS.Stage2.Local.P34OneG

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

theorem one_isCentralInvolution_of_isConj {G : Type} [Group G] {z x : G} (hz : IsCentralInvolution z)
    (h : IsConj z x) : IsCentralInvolution x := by
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

@[expose] def NoOneClassC0' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H : Subgroup G, H ≠ ⊤ → Cen z ≤ H → C0 z k S H → barIn H (LC z) ≤ generalizedFitting (HBar H) →
      ¬ (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)

@[expose] def OneClassNoDiag : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool) (q : ℕ)
    (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1L4 G z S ε q L₁ L₂ →
    (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
      ∀ y ∈ S1 S z, y * y = 1 → y ∈ RC S z

theorem noOneClassC0'_of (hI1 : OneClassNoDiag) : NoOneClassC0' := by
  intro G _ _ z k S ctx H _ hCH hC0 hLle hone
  obtain ⟨ε, q, L₁, L₂, -, hL4, -, hpsp, hnS, -⟩ := hC0
  rcases hL4.fusion with ⟨hq4, -⟩ | ⟨-, x, hx, -⟩
  · have hmod := hL4.mod8
    have hq8 : q % 8 = 3 ∨ q % 8 = 5 := by
      cases ε <;> simp at hq4 hmod ⊢ <;> omega
    obtain ⟨y, hy, hy2, hyR⟩ := exists_inv_S1_out ctx hL4.pair hCH hLle hq8 hpsp hnS
    exact hyR (hI1 G z S ε q L₁ L₂ hL4 hone y hy hy2)
  · exact hx.x_nonCentral (one_isCentralInvolution_of_isConj ctx.central
      (hone z x ctx.orderOf_z hx.x_inv))

end CFSG.GH74.GLS.Stage2.Local.P34
