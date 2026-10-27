module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Statements
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_16
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Main
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L203Final
public import CFSG.GH74.GLS.Stage2.Local.P34Final
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Closed
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk411Main

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

theorem isCentralInvolution_of_conj {G : Type} [Group G] {z x : G} (hz : IsCentralInvolution z)
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

section Symp

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem exists_sympCtx (hctx : Stage2Ctx G z k S) {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hq : Stage1PSp4 G z S q L₁ L₂) : ∃ g : G, SympCtx z S g := by
  obtain ⟨x, hx⟩ := hq.two
  obtain ⟨t, htS, htc, hsw⟩ := hx.swap_exists
  obtain ⟨c, hc⟩ := isConj_iff.1 htc
  have hzt : zc z c⁻¹ = t := by
    unfold zc
    rw [inv_inv]
    exact hc
  refine ⟨c⁻¹, ?_, ?_, ?_⟩
  · rw [hzt]; exact htS
  · refine ⟨q, L₁, L₂, hq.pair, ?_⟩
    rw [hzt]; exact hsw
  · rw [hzt]
    intro hconj
    have hxt := (hx.swap_conseq t htS htc hsw).1
    have hzx : IsConj z x := hconj.trans hxt.symm
    exact hx.x_nonCentral (isCentralInvolution_of_conj hctx.central hzx)

end Symp

section Main

theorem prop201_of_leaves
    (_L : Thm6Leaves) : Prop201 := by
  intro G _ _ z k S M h hk
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne, hnc⟩ := hcon
  have hF : Fail20 G z k S M := ⟨h, hk, hne, hnc⟩
  have h3 : Lemma20_3 := lemma20_3_thm P34.leaf_prop34_proved (fun _ _ _ _ _ _ h => h.detail.l4_two)
    (fun J _ _ _ hn hG => GHSch.ghSchreier_thm J hn hG)
  have hMC : M = Cen z := h3 G z k S M hF
  have hcl : TypeCl z k S := hF.typeCl lemma20_8_thm hMC
  have h11 : Lemma20_11 := L2011.lemma20_11_closed CFSG.GH74.Ivk411.data411Clauses_proved
  have h12' : Lemma20_12 := L2012.lemma20_12_of_11 h11
  have h13' : Lemma20_13 := L2012.lemma20_13_of_11 h11
  have h12 := h12' G z k S M hF hMC hcl
  have hpsp : ∃ q : ℕ, TypePSp4 z k S q := by
    rcases h12.1 with ⟨ε, q, hT, hnf⟩ | hp
    · exact h13' G z k S M hF hMC ⟨ε, q, hT, hnf⟩
    · exact hp
  obtain ⟨g, hg⟩ : ∃ g : G, SympCtx z S g := by
    obtain ⟨q, -, L₁, L₂, hq⟩ := hpsp
    exact exists_sympCtx h.ctx17.ctx hq
  have h14 := lemma20_14_thm h12' G z k S M hF hMC hpsp g hg
  have h15 := lemma20_15_thm h12' G z k S M hF hMC hpsp g hg h14
  have h16 := lemma20_16_thm h12' G z k S M hF hMC hpsp g hg h14 h15
  apply hne
  rw [hMC]
  exact h16

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6
