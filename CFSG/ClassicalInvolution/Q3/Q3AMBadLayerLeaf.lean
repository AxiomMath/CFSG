module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadNbhd

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open scoped MatrixGroups commutatorElement

section Leaf


variable {G : Type} [Group G]

theorem mul_self_mul_of_comm' {a b : G} (h : a * b = b * a) :
    (a * b) * (a * b) = (a * a) * (b * b) := by
  calc (a * b) * (a * b) = a * (b * a) * b := by group
    _ = a * (a * b) * b := by rw [← h]
    _ = (a * a) * (b * b) := by group

theorem pspLayersSp4Leaf_proved : PspLayersSp4Leaf := by
  intro G _ _ _ Ω K J S R T W z t K' hset t₁ t₂ t₃ R₁ R₂ R₃ hax hK hJ hK'
  have hbad := hset.bad
  have hstd := hbad.std
  have hint := hset.intrinsic
  have hzz : z * z = 1 := hax.z₁_sq
  have htt : t * t = 1 := hax.z₂_sq
  have hzt : z * t = t * z := hax.z_comm
  have hs2 : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := hax.s_mul_self
  have hcz : z * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * z := hax.s_comm₁.eq
  have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
  have ht1K : t₁ ∈ K := hax.syl₁.1 hax.mem₁
  have ht2J : t₂ ∈ J := hax.syl₂.1 hax.mem₂
  have ht3K' : t₃ ∈ K' := hax.syl₃.1 hax.mem₃
  have c12 : t₁ * t₂ = t₂ * t₁ := hax.comm₁₂ t₁ hax.mem₁ t₂ hax.mem₂
  have c13 : t₁ * t₃ = t₃ * t₁ := hax.comm₁₃ t₁ hax.mem₁ t₃ hax.mem₃
  have c23 : t₂ * t₃ = t₃ * t₂ := hax.comm₂₃ t₂ hax.mem₂ t₃ hax.mem₃
  have cz2 : z * t₂ = t₂ * z := hax.comm₁₂ z hax.z_mem₁ t₂ hax.mem₂
  have cz3 : z * t₃ = t₃ * z := hax.comm₁₃ z hax.z_mem₁ t₃ hax.mem₃
  have ct1 : t₁ * t = t * t₁ := hax.comm₁₂ t₁ hax.mem₁ t hax.z_mem₂
  have ct3 : t * t₃ = t₃ * t := hax.comm₂₃ t hax.z_mem₂ t₃ hax.mem₃
  have cw1 : t₁ * (z * t) = (z * t) * t₁ := hax.comm₁₃ t₁ hax.mem₁ (z * t) hax.z_mem₃
  have cw2 : t₂ * (z * t) = (z * t) * t₂ := hax.comm₂₃ t₂ hax.mem₂ (z * t) hax.z_mem₃
  have hKJ : J ∈ omegaNbr Ω K := hstd.hJ
  have hKK' : K' ∈ omegaNbr Ω K := hset.nbrK
  have hJK' : K' ∈ omegaNbr Ω J := hset.nbrJ
  have hJK : K ∈ omegaNbr Ω J :=
    mem_omegaNbr_symm hbad hint hstd.stand.mem hKJ hstd.hz hstd.ht
  have hK'K : K ∈ omegaNbr Ω K' :=
    mem_omegaNbr_symm hbad hint hstd.stand.mem hKK' hstd.hz hax.uniq₃
  have hK'J : J ∈ omegaNbr Ω K' :=
    mem_omegaNbr_symm hbad hint hstd.hJ.1 hJK' hstd.ht hax.uniq₃
  have L1 : ∃ L : Subgroup G, IsSectionMember3
      (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L z := by
    have h2 : t₂ ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hKJ
      ⟨ht2J, Subgroup.mem_centralizer_singleton_iff.mpr cz2.symm⟩
    have h3 : t₃ ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hKK'
      ⟨ht3K', Subgroup.mem_centralizer_singleton_iff.mpr cz3.symm⟩
    have hw : t₂ * t₃ ∈ nbrLayer Ω K z := (nbrLayer Ω K z).mul_mem h2 h3
    have hww : (t₂ * t₃) * (t₂ * t₃) = z := by
      rw [mul_self_mul_of_comm' c23, hax.sq₂, hax.sq₃]
      calc t * (z * t) = (t * z) * t := by group
        _ = (z * t) * t := by rw [← hzt]
        _ = z * (t * t) := by group
        _ = z := by rw [htt]; group
    exact exists_layer_at_vertex hbad hint hstd.stand.mem hax.uniq₁ hK hw hww ht1K
      (by rw [mul_assoc]) hcz.symm hs2
  have L2 : ∃ L : Subgroup G, IsSectionMember3
      (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L t := by
    have h1 : t₁ ∈ nbrLayer Ω J t := exactCore3_le_nbrLayer hJK
      ⟨ht1K, Subgroup.mem_centralizer_singleton_iff.mpr ct1⟩
    have h3 : t₃ ∈ nbrLayer Ω J t := exactCore3_le_nbrLayer hJK'
      ⟨ht3K', Subgroup.mem_centralizer_singleton_iff.mpr ct3.symm⟩
    have hw : t₁ * t₃ ∈ nbrLayer Ω J t := (nbrLayer Ω J t).mul_mem h1 h3
    have hww : (t₁ * t₃) * (t₁ * t₃) = t := by
      rw [mul_self_mul_of_comm' c13, hax.sq₁, hax.sq₃]
      calc z * (z * t) = (z * z) * t := by group
        _ = t := by rw [hzz]; group
    have hs : t₁ * t₂ * t₃ = t₂ * (t₁ * t₃) := by
      calc t₁ * t₂ * t₃ = (t₂ * t₁) * t₃ := by rw [c12]
        _ = t₂ * (t₁ * t₃) := by group
    exact exists_layer_at_vertex hbad hint hstd.hJ.1 hax.uniq₂ hJ hw hww ht2J hs hct.symm hs2
  have L3 : ∃ L : Subgroup G, IsSectionMember3
      (Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G)) L (z * t) := by
    have h1 : t₁ ∈ nbrLayer Ω K' (z * t) := exactCore3_le_nbrLayer hK'K
      ⟨ht1K, Subgroup.mem_centralizer_singleton_iff.mpr cw1⟩
    have h2 : t₂ ∈ nbrLayer Ω K' (z * t) := exactCore3_le_nbrLayer hK'J
      ⟨ht2J, Subgroup.mem_centralizer_singleton_iff.mpr cw2⟩
    have hw : t₁ * t₂ ∈ nbrLayer Ω K' (z * t) := (nbrLayer Ω K' (z * t)).mul_mem h1 h2
    have hww : (t₁ * t₂) * (t₁ * t₂) = z * t := by
      rw [mul_self_mul_of_comm' c12, hax.sq₁, hax.sq₂]
    have hs : t₁ * t₂ * t₃ = t₃ * (t₁ * t₂) := by
      calc t₁ * t₂ * t₃ = t₁ * (t₂ * t₃) := by group
        _ = t₁ * (t₃ * t₂) := by rw [c23]
        _ = (t₁ * t₃) * t₂ := by group
        _ = (t₃ * t₁) * t₂ := by rw [c13]
        _ = t₃ * (t₁ * t₂) := by group
    have hsa : (t₁ * t₂ * t₃) * (z * t) = (z * t) * (t₁ * t₂ * t₃) := by
      calc (t₁ * t₂ * t₃) * (z * t) = ((t₁ * t₂ * t₃) * z) * t := by group
        _ = (z * (t₁ * t₂ * t₃)) * t := by rw [hcz]
        _ = z * ((t₁ * t₂ * t₃) * t) := by group
        _ = z * (t * (t₁ * t₂ * t₃)) := by rw [hct]
        _ = (z * t) * (t₁ * t₂ * t₃) := by group
    exact exists_layer_at_vertex hbad hint hset.nbrK.1 hax.uniq₃ hK' hw hww ht3K' hs hsa hs2
  obtain ⟨L₁, h₁⟩ := L1
  obtain ⟨L₂, h₂⟩ := L2
  obtain ⟨L₃, h₃⟩ := L3
  exact ⟨L₁, L₂, L₃, h₁, h₂, h₃⟩

end Leaf

end CFSG.ClassicalInvolution.Q3.Q3AM
