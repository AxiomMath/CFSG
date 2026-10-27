module

public import CFSG.ClassicalInvolution.Q3.Q3AMLY5Conj
public import CFSG.ClassicalInvolution.Q3.Q3AM289Nbr

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

section Link


theorem e4linkY_proved : Q3AM.LinkLeafY := by
  intro G _ _ _ Ω K J S R T W z t h hlay s hs J' hJ' t' ht'
  have hbad : BadStd8 Ω K J S R T W z t := h.bad
  have hstd : Std8 Ω K J S R T W z t := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hK : K ∈ Ω := hstd.stand.mem
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  set Y : Subgroup G := Q3AM.nbrLayer Ω K z with hYdef
  have hYC : Y ≤ Subgroup.centralizer ({z} : Set G) := Q3AM.nbrLayer_le_centralizer Ω K z
  have hΛN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    hbad.centralizer_le_normalizer_nbrLayer hK hstd.hz
  have hzΛ : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hzt' : z * t' = t' * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hJ' ht'
  obtain ⟨J₁, hJ₁, hv₁⟩ := hs.nbr₁
  have htY : t ∈ Y := mem_nbrLayer_of_mem hstd.hJ hstd.ht.mem hzt.symm
  have hsY : s ∈ Y := mem_nbrLayer_of_mem hJ₁ hv₁.mem hs.comm_z.symm
  have ht'Y : t' ∈ Y := mem_nbrLayer_of_mem hJ' ht'.mem hzt'.symm
  have hzX : ∀ x ∈ Y, ⁅x, z⁆ ∈ oddCoreOf Y := commutator_self_mem_oddCoreOf_nbrLayer Ω K z
  have hts : t ≠ s := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  have hF : LinkModelFacts (↥Y ⧸ classicalInvolutionOddCore ↥Y) := by
    obtain ⟨D, hD | hD⟩ := Q3AM.exists_sysU_of_layerE4 hlay
    · exact linkModelFacts_of_psl D hD
    · exact linkModelFacts_of_m11 D hD
  have hB : IsElemAbelian 2 (Subgroup.closure ({z, t, s} : Set G)) :=
    T8T.isElemAbelian_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t
  have hne : z ≠ t := fun e => by
    have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
      T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
    have : IsUniqueInvolution J z := e ▸ hstd.ht
    exact hstd.hJ.2.1 (hnt K hK J ⟨hstd.hJ.1, z, hstd.hz, this⟩)
  have hBcard : Nat.card ↥(Subgroup.closure ({z, t, s} : Set G)) = 8 :=
    T8T.natCard_closure_three hz2 ht2 hs.sq hzt hs.comm_z hs.comm_t hstd.hz.ne_one
      hstd.ht.ne_one hne hs.ne_one hs.indep
  have hBN : Subgroup.closure ({z, t, s} : Set G) ≤
      Subgroup.normalizer ((oddCoreOf Y : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (Y : Set G) := by
      rcases hg with rfl | rfl | rfl
      · exact hΛN hzΛ
      · exact Subgroup.le_normalizer htY
      · exact Subgroup.le_normalizer hsY
    exact mem_normalizer_oddCore_of_mem_normalizer hgN
  have hOH : oddCoreOf Y ≤ rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)) := by
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
      Nat.prime_two (Subgroup.closure ({z, t, s} : Set G)) (oddCoreOf Y) hB
      (by norm_num [hBcard]) hBN (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
    conv_lhs => rw [← hgen]
    exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right
  have hHc : ∀ c : G, c ∈ Subgroup.closure ({z, t, s} : Set G) → c * c = 1 → c ≠ 1 → z ≠ c →
      z * c = c * z → Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ≤
        rankTwoSpan (Subgroup.closure ({z, t, s} : Set G)) := by
    intro c hcB hc2 hc1 hzc hzc'
    have hD := T7A.isElemAbelian2_closure_pair hz2 hc2 hstd.hz.ne_one hc1 hzc hzc'
    have hFB : Subgroup.closure ({z, c} : Set G) ∈
        signalizerFunctorEk 2 2 (Subgroup.closure ({z, t, s} : Set G)) := by
      refine ⟨?_, by simpa using hD.1⟩
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact hcB
    refine le_rankTwoSpan_of_le_centralizer hFB ?_
    intro g hg
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro y (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hg.1).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hg.2).symm
  have hzts : z * (t * s) = (t * s) * z := by
    calc z * (t * s) = (z * t) * s := by group
      _ = (t * z) * s := by rw [hzt]
      _ = t * (z * s) := by group
      _ = t * (s * z) := by rw [hs.comm_z]
      _ = (t * s) * z := by group
  have hts2 : (t * s) * (t * s) = 1 := by
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hs.comm_t]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs.sq, one_mul]
  have hts1 : t * s ≠ 1 := fun e => hts (by
    have h1 : s = t⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h1, inv_eq_of_mul_eq_one_right ht2])
  have hztsne : z ≠ t * s := fun e => hs.indep (by
    have h1 : s = t * z := by
      calc s = t * (t * s) := by rw [← mul_assoc, ht2, one_mul]
        _ = t * z := by rw [← e]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)))
  have hzs : z ≠ s := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  have hBts : t * s ∈ Subgroup.closure ({z, t, s} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  exact link_conj_of_modelFacts hYC hΛN hzΛ hz2 hzX htY hsY ht'Y ht2 hs.sq ht'.sq
    hstd.ht.ne_one hs.ne_one ht'.ne_one hts hzt hs.comm_z hzt' hs.comm_t hOH
    (hHc t (Subgroup.subset_closure (by simp)) ht2 hstd.ht.ne_one hne hzt)
    (hHc s (Subgroup.subset_closure (by simp)) hs.sq hs.ne_one hzs hs.comm_z)
    (hHc (t * s) hBts hts2 hts1 hztsne hzts) hF

end Link

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
