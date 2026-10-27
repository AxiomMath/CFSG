module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic

import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.GroupTheory.ABGLocalTools.PStabilityFrattini
import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
import CFSG.CGT.Timmesfeld75.Fusion

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open scoped Pointwise in
theorem oddCore_mul_normalizer_conjugacyClosure_of_le_layerCore
    {G : Type} [Group G] [Finite G]
    (T : Subgroup G) (x : G)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (N : Subgroup G)
    (hB : Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} ≤
      ((CFSG.Op_p'p 2 ↥(CFSG.pLayer ↥N 2)).map
        (CFSG.pLayer ↥N 2).subtype).map N.subtype) :
    (N : Set G) =
      ((CFSG.pPrimeCore 2 ↥N).map N.subtype : Set G) *
        ((N ⊓ Subgroup.normalizer
          (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G)) : Set G) := by
  classical
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup G := Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}
  let E : Subgroup ↥N := CFSG.pLayer ↥N 2
  let D0 : Subgroup ↥E := CFSG.Op_p'p 2 ↥E
  let Dn : Subgroup ↥N := D0.map E.subtype
  let D : Subgroup G := Dn.map N.subtype
  let R : Subgroup ↥N := CFSG.pPrimeCore 2 ↥N
  let Rg : Subgroup G := R.map N.subtype
  let Oe : Subgroup ↥N := (CFSG.pPrimeCore 2 ↥E).map E.subtype
  let Δ : Set G := {a : G | IsConj x a}
  have hBD : B ≤ D := by
    simpa [B, D, Dn, D0, E] using hB
  have hBT : B ≤ T := by
    change Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} ≤ T
    rw [Subgroup.closure_le]
    intro a ha
    exact ha.1
  have hB2 : IsPGroup 2 B := hT.isPGroup.to_le hBT
  have hDleN : D ≤ N := Subgroup.map_subtype_le Dn
  have hDnleE : Dn ≤ E := Subgroup.map_subtype_le D0
  have hBsubD2 : IsPGroup 2 (B.subgroupOf D) := hB2.comap_subtype (K := D)
  obtain ⟨S, hBS⟩ := hBsubD2.exists_le_sylow
  let U : Subgroup G := (S : Subgroup D).map D.subtype
  have hU_syl : CFSG.ABGLocalTools.IsSylowOf 2 U D := ⟨S, rfl⟩
  have hU2 : IsPGroup 2 U := hU_syl.isPGroup
  have hBU : B ≤ U := by
    calc B = (B.subgroupOf D).map D.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hBD).symm
      _ ≤ (S : Subgroup D).map D.subtype := Subgroup.map_mono hBS
  have hUleD : U ≤ D := hU_syl.le
  have hUN : U ≤ N := hUleD.trans hDleN
  let Un : Subgroup ↥N := U.subgroupOf N
  let Ue : Subgroup ↥E := Un.subgroupOf E
  have hUn_map : Un.map N.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUN
  have hUnDn : Un ≤ Dn := by
    rw [← Subgroup.map_le_map_iff_of_injective N.subtype_injective]
    simpa [hUn_map, D] using hUleD
  have hUnE : Un ≤ E := hUnDn.trans hDnleE
  have hUe_map : Ue.map E.subtype = Un := Subgroup.map_subgroupOf_eq_of_le hUnE
  have hUn_syl : CFSG.ABGLocalTools.IsSylowOf 2 Un Dn := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) (K := N)
      (A := Un) (B := Dn)).mp ?_
    simpa [hUn_map, D] using hU_syl
  have hUe_syl : CFSG.ABGLocalTools.IsSylowOf 2 Ue D0 := by
    refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 2) (K := E)
      (A := Ue) (B := D0)).mp ?_
    simpa [hUe_map, Dn] using hUn_syl
  have hUn2 : IsPGroup 2 Un := hUn_syl.isPGroup
  have hUe2 : IsPGroup 2 Ue := hUe_syl.isPGroup
  have hEchar : E.Characteristic := by
    change (CFSG.pLayer ↥N 2).Characteristic
    exact CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
      (G := ↥N) (p := 2)
  have hEnormal : E.Normal := inferInstance
  have hD0char : D0.Characteristic := by
    change (CFSG.Op_p'p 2 ↥E).Characteristic
    infer_instance
  have hDnnormal : Dn.Normal := by
    change ((CFSG.Op_p'p 2 ↥E).map E.subtype).Normal
    exact ConjAct.normal_of_characteristic_of_normal (H := E)
  have hRnormal : R.Normal := by
    change (CFSG.pPrimeCore 2 ↥N).Normal
    exact CFSG.pPrimeCore_normal
  have hOe_eq : Oe = E ⊓ R := by
    change ((CFSG.pPrimeCore 2 ↥E).map E.subtype) = E ⊓ CFSG.pPrimeCore 2 ↥N
    exact CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 2) (H := ↥N)
      (N := E) hEnormal
  have hOe_le_R : Oe ≤ R := by
    rw [hOe_eq]
    exact inf_le_right
  have hsupE : CFSG.pPrimeCore 2 ↥E ⊔ Ue = D0 :=
    (CFSG.ABGLocalTools.sup_eq_Op_p'p_iff_isSylowOf (p := 2) (H := ↥E)
      (Q := Ue) hUe2).mpr hUe_syl
  have hsupN : Oe ⊔ Un = Dn := by
    have hmap := congrArg (fun H : Subgroup ↥E => H.map E.subtype) hsupE
    rw [Subgroup.map_sup, hUe_map] at hmap
    simpa [Oe, Dn] using hmap
  have hRDn_normal : (R ⊔ Dn).Normal := Subgroup.sup_normal R Dn
  have hjoin : R ⊔ Un = R ⊔ Dn := by
    rw [← hsupN]
    rw [← sup_assoc, sup_eq_left.mpr hOe_le_R]
  have hRUn_normal : (R ⊔ Un).Normal := by
    rw [hjoin]
    exact hRDn_normal
  let Cn : Subgroup ↥N := Subgroup.normalizer (Un : Set ↥N)
  have hRUn_top : R ⊔ Cn = ⊤ :=
    CFSG.ABGLocalTools.pPrimeCore_sup_normalizer_eq_top (p := 2) (H := ↥N)
      (P := Un) hUn2 hRUn_normal
  have hTdata := (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (G := G)
    (P := T) (K := ⊤)).mp hT
  have hTidx : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hTdata.2.2
  let S0 : Sylow 2 G := hTdata.2.1.toSylow hTidx
  have hS0coe : (S0 : Subgroup G) = T := hTdata.2.1.toSylow_coe hTidx
  have hΔinv : ∀ d ∈ Δ, ∀ g : G, g * d * g⁻¹ ∈ Δ := by
    intro d hd g
    change IsConj x d at hd
    change IsConj x (g * d * g⁻¹)
    exact hd.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hSset : (S0 : Set G) ∩ Δ = {a : G | a ∈ T ∧ IsConj x a} := by
    change ((S0 : Subgroup G) : Set G) ∩ Δ = {a : G | a ∈ T ∧ IsConj x a}
    rw [hS0coe]
    rfl
  have hSU : Subgroup.closure ((S0 : Set G) ∩ Δ) ≤ U := by
    rw [hSset]
    change B ≤ U
    exact hBU
  have hclosure_eq : Subgroup.closure ((U : Set G) ∩ Δ) = B := by
    have h := CFSG.CGT.Timmesfeld75.closure_inter_eq_of_le_pGroup S0 Δ hΔinv hU2 hSU
    rw [h, hSset]
  have hNΔ : Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (((U : Set G) ∩ Δ) : Set G) := by
    intro n hn
    rw [Subgroup.mem_set_normalizer_iff]
    intro a
    constructor
    · rintro ⟨haU, haΔ⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hn a).mp haU, hΔinv a haΔ n⟩
    · rintro ⟨haU, haΔ⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hn a).mpr haU, ?_⟩
      have h := hΔinv (n * a * n⁻¹) haΔ n⁻¹
      have h' : n⁻¹ * (n * a * n⁻¹) * (n⁻¹)⁻¹ = a := by group
      rwa [h'] at h
  have hNUN : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (B : Set G) := by
    intro n hn
    have hnΔ := hNΔ hn
    have hcl := Subgroup.normalizer_le_normalizer_closure
      (((U : Set G) ∩ Δ) : Set G) hnΔ
    simpa [hclosure_eq] using hcl
  have hCn_le : Cn ≤ (Subgroup.normalizer (B : Set G)).subgroupOf N := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    have hnU : (n : G) ∈ Subgroup.normalizer (U : Set G) := by
      have hsub : (Subgroup.normalizer (U : Set G)).subgroupOf N = Cn := by
        simpa [Cn, Un] using Subgroup.subgroupOf_normalizer_eq hUN
      rw [← hsub] at hn
      exact Subgroup.mem_subgroupOf.mp hn
    exact hNUN hnU
  have hprodN : (Set.univ : Set ↥N) = (R : Set ↥N) * (Cn : Set ↥N) := by
    have hcoe : ((R ⊔ Cn : Subgroup ↥N) : Set ↥N) =
        (R : Set ↥N) * (Cn : Set ↥N) := by
      rw [Subgroup.normal_mul]
    calc (Set.univ : Set ↥N) = ((⊤ : Subgroup ↥N) : Set ↥N) := by simp
      _ = ((R ⊔ Cn : Subgroup ↥N) : Set ↥N) := by rw [hRUn_top]
      _ = (R : Set ↥N) * (Cn : Set ↥N) := hcoe
  change (N : Set G) = (Rg : Set G) *
    ((N ⊓ Subgroup.normalizer (B : Set G)) : Set G)
  ext g
  constructor
  · intro hg
    let gn : ↥N := ⟨g, hg⟩
    have hmem : gn ∈ (R : Set ↥N) * (Cn : Set ↥N) := by
      rw [← hprodN]
      exact Set.mem_univ gn
    obtain ⟨r, hr, c, hc, hrc⟩ := Set.mem_mul.mp hmem
    refine Set.mem_mul.mpr ⟨(r : G), ?_, (c : G), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem N.subtype hr
    · exact ⟨c.2, Subgroup.mem_subgroupOf.mp (hCn_le hc)⟩
    · have hval := congrArg (fun y : ↥N => (y : G)) hrc
      simpa [gn, Subgroup.coe_mul] using hval
  · rw [Set.mem_mul]
    rintro ⟨r, hr, c, hc, hrc⟩
    rw [← hrc]
    change r ∈ (R.map N.subtype : Set G) at hr
    obtain ⟨r0, hr0, rfl⟩ := Subgroup.mem_map.mp hr
    exact N.mul_mem r0.2 hc.1

end CFSG.GH74.GLS.NT44

end
