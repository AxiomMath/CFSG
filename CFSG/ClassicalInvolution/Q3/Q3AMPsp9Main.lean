module

public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9Nbhd
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XAut
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XLeaf
public import CFSG.ClassicalInvolution.Q3.Q3AMBadLayerLeaf

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH

section Main


section Axis

variable {G : Type} [Group G] [Finite G]

theorem pspLayers9 [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (hset : PspSetting Ω K J S R T W z t K')
    {t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}
    (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) (hK : PspNbhdL4 Ω K z) (hJ : PspNbhdL4 Ω J t) :
    ∃ L₁ L₂ : Subgroup G, Psp9Layer (nbrLayer Ω K z) (t₁ * t₂ * t₃) z L₁ ∧
      Psp9Layer (nbrLayer Ω J t) (t₁ * t₂ * t₃) t L₂ := by
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
  have hKJ : J ∈ omegaNbr Ω K := hstd.hJ
  have hKK' : K' ∈ omegaNbr Ω K := hset.nbrK
  have hJK' : K' ∈ omegaNbr Ω J := hset.nbrJ
  have hJK : K ∈ omegaNbr Ω J :=
    mem_omegaNbr_symm hbad hint hstd.stand.mem hKJ hstd.hz hstd.ht
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
  obtain ⟨L₁, hL₁⟩ := exists_layer9_pkg hbad hint hstd.stand.mem hax.uniq₁ hK hw hww ht1K
    (by rw [mul_assoc]) hcz.symm hs2
  have g1 : t₁ ∈ nbrLayer Ω J t := exactCore3_le_nbrLayer hJK
    ⟨ht1K, Subgroup.mem_centralizer_singleton_iff.mpr ct1⟩
  have g3 : t₃ ∈ nbrLayer Ω J t := exactCore3_le_nbrLayer hJK'
    ⟨ht3K', Subgroup.mem_centralizer_singleton_iff.mpr ct3.symm⟩
  have gw : t₁ * t₃ ∈ nbrLayer Ω J t := (nbrLayer Ω J t).mul_mem g1 g3
  have gww : (t₁ * t₃) * (t₁ * t₃) = t := by
    rw [mul_self_mul_of_comm' c13, hax.sq₁, hax.sq₃]
    calc z * (z * t) = (z * z) * t := by group
      _ = t := by rw [hzz]; group
  have gs : t₁ * t₂ * t₃ = t₂ * (t₁ * t₃) := by
    calc t₁ * t₂ * t₃ = (t₂ * t₁) * t₃ := by rw [c12]
      _ = t₂ * (t₁ * t₃) := by group
  obtain ⟨L₂, hL₂⟩ := exists_layer9_pkg hbad hint hstd.hJ.1 hax.uniq₂ hJ gw gww ht2J gs hct.symm hs2
  exact ⟨L₁, L₂, hL₁, hL₂⟩

end Axis

theorem pspLayersWC9_proved : PspLayersWC9 := by
  intro _ G _ _ _ Ω K J S R T W z t K' _ hset t₁ t₂ t₃ R₁ R₂ R₃ hax hK hJ _
  obtain ⟨L₁, L₂, h₁, h₂⟩ := pspLayers9 hset hax hK hJ
  have hbad := hset.bad
  have hstd := hbad.std
  have hint := hset.intrinsic
  have hKc : IsClassicalMember3 K z :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hstd.stand.mem hstd.hz
  have hD3 : ∀ {X : Subgroup G} {x a : G}, X ≤ Subgroup.normalizer (K : Set G) → x ∈ X →
      x * x = 1 → ∀ ha : a ∈ X, (⟨a, ha⟩ : X) ∈ derivedSeries X 3 →
        Odd (orderOf (a⁻¹ * x)) → x ∈ trivialOnQuot K :=
    fun hXK hx hx2 ha ha3 hodd => mem_trivialOnQuot_of_derived3 hKc hXK hx hx2 ha ha3 hodd
  have hzt : z * t = t * z := hax.z_comm
  have hct : t * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * t := hax.s_comm₂.eq
  have htY : t ∈ nbrLayer Ω K z := exactCore3_le_nbrLayer hstd.hJ
    ⟨hstd.ht.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  have hts : t ∈ Subgroup.centralizer ({t₁ * t₂ * t₃} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hct
  refine ⟨L₁, L₂, h₁.mem, h₂.mem, fun h hh hR => weakClosure_of_layer hbad hint h₁ hD3 hh hR, ?_⟩
  exact normalizesImageAt_of_layer htY hts fun g hg hgs =>
    h₁.norm g (nbrLayer_le_centralizer Ω K z hg) hgs

theorem pspVertexSLeaf9_proved : PspVertexSLeaf9 :=
  pspVertexSLeaf9_of_layersWC pspLayersWC9_proved

end Main

end CFSG.ClassicalInvolution.Q3.Q3AM
