module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf9Layer
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf8Class

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open scoped commutatorElement

section Edgeless





variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y}

theorem not_mem_tq_K_of_datum (hP : PerpHypS n Y R S t)
    (hd : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃) :
    K ∉ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
      K' ∉ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) := by
  constructor
  · intro h
    exact not_mem_trivialOnQuot_of_order4 hd.hyp hd.mem hd.hK'.1 hd.hne hd.hz hd.hzK'
      (fun P' hP' => members_sylow_q8 hP K hd.mem P' hP') hd.hu₁.1 hd.hu₁.2 hd.hu₂.1 h.2
  · intro h
    refine not_mem_trivialOnQuot_of_order4 hd.hyp hd.hK'.1 hd.mem hd.hne.symm hd.hzK' hd.hz
      (fun P' hP' => members_sylow_q8 hP K' hd.hK'.1 P' hP') hd.hu₂.1 hd.hu₂.2 hd.hu₁.1 ?_
    rw [← hd.comm₁₂]
    exact h.2

theorem secImg_not_nbr_of_three (hP : PerpHypS n Y R S t)
    (hd : A7T22.Hyp22G (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃)
    (hV : ∀ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M = K ∨ M = K' ∨ M = K₃)
    {J : Subgroup Y} (hJ : J ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) :
    secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) J ∉
      omegaNbr (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂))
        (secImg (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) K₃) := by
  intro h
  have hc2 : IsPGroup 2 (Subgroup.zpowers (u₁ * u₂)) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.sq_12
  have hK₃tq := tq_of_hyp22G hd
  obtain ⟨hnK, hnK'⟩ := not_mem_tq_K_of_datum hP hd
  have hzK₃ : IsUniqueInvolution K₃ t := hd.hzK₃
  have hperp0 := kPerp_datum hP hd.hK₃.1 hzK₃
  have hperp : ∀ J₀ ∈ tqMembers3 (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂),
      J₀ ∈ KPerp (CoreAssembly.conjClass (tightCore R)) K₃ → J₀ = K₃ ∨ J₀ = K₃ := by
    intro J₀ hJ₀ hJ₀perp
    left
    rw [hperp0, twinSet_eq_of_mem_twinSet hd.hz hd.hK₃] at hJ₀perp
    rcases hV J₀ hJ₀perp with h1 | h1 | h1
    · exact absurd hJ₀ (h1 ▸ hnK)
    · exact absurd hJ₀ (h1 ▸ hnK')
    · exact h1
  have := TwinLayerGen.secNbr_eq_of_perp hd.hyp hc2 hK₃tq hJ hperp h
  exact h.2.1 this

end Edgeless

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
