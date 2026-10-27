module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundBar
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundComp
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Closed

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem isCentralInvolution_of_isConj_sl2 {G : Type} [Group G] {z x : G} (hz : IsCentralInvolution z)
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

end CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound
open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg

theorem sl2OddCentBound_thm : SL2OddCentBound := by
  intro G _ _ z S ε q hctx hT K₁ K₂ hcp h1 h2 t htc htS htN hiff
  obtain ⟨-, L₁, L₂, hL⟩ := hT
  obtain ⟨F, iF, fF, hFq0, ⟨e0⟩⟩ := h1
  have hFq : Nat.card F = q := hFq0
  let e : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e0.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have hodd : Odd (Nat.card F) := hFq ▸ hL.pair.odd
  have h3 : 3 < Nat.card F := hFq ▸ hL.pair.gt3
  have hE : Em (Cen z) ≤ Cen z := Subgroup.map_subtype_le _
  have hK₁E : K₁ ≤ Em (Cen z) := hcp.1 ▸ le_sup_left
  have hK₁C : K₁ ≤ Cen z := hK₁E.trans hE
  have hSC : S ≤ Cen z := hctx.sylow.le
  have hcomm := hcp.2.1
  have hzord : orderOf z = 2 := hctx.central.1
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzord, pow_two] at this
  obtain ⟨c, hc⟩ := isConj_iff.1 htc
  have ht2 : t * t = 1 := by
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hto : orderOf t = 2 := by
    have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hzord
  have hmod : q % 4 = 1 ∨ q % 4 = 3 := by
    obtain ⟨k, hk⟩ := hL.pair.odd
    omega
  by_cases hf : Fused ε q
  ·
    have htK : t ∈ K₁ ⊔ K₂ := hiff.2 hf
    have hb := bound_fused e hodd h3 hcomm htK ht2
    rw [hFq] at hb
    cases ε
    · have : ¬ q % 4 = 1 := by
        unfold Fused at hf
        simp at hf
        omega
      simpa [this] using hb
    · have : q % 4 = 1 := by
        unfold Fused at hf
        simpa using hf
      simpa [this] using hb
  ·
    have hntK : t ∉ K₁ ⊔ K₂ := fun h => hf (hiff.1 h)
    by_cases hin : ∃ a ∈ K₁, ∀ k ∈ K₁, t * k * t⁻¹ = a * k * a⁻¹
    ·
      have hKL := barOf_mem_pair hL hcp e hFq
      have htLC : t ∈ LC z := inner_mem_LC hL hSC hK₁C hKL htS htN hin
      have htz : t = z := by
        by_contra hne
        rcases hL.fusion with ⟨hq4, -⟩ | ⟨hq4, x, hTC, -⟩
        · exact hf hq4
        · obtain ⟨hxt, -⟩ := hTC.invol_L t htLC hto hne
          have hxz : IsConj z x := htc.trans hxt.symm
          exact hTC.x_nonCentral (isCentralInvolution_of_isConj_sl2 hctx.central hxz)
      have hcen : ∀ k ∈ K₁, k * t = t * k := by
        intro k hk
        rw [htz]
        exact Subgroup.mem_centralizer_singleton_iff.1 (hK₁C hk)
      rw [pPrimeCoreOf_eq_bot_of_central e hodd h3 hcen]
      simp
    ·
      have hb := bound_outer e hodd h3 htN ht2 hin
      rw [hFq] at hb
      cases ε
      · have : q % 4 = 1 := by
          unfold Fused at hf
          simp at hf
          omega
        simpa [this] using hb
      · have : ¬ q % 4 = 1 := by
          unfold Fused at hf
          simp at hf
          omega
        simpa [this] using hb

end CFSG.GH74.GLS.Stage2.Final.Thm6
