module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNSyl
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B : Subgroup G}

private theorem sec9n_priv_conj_mem_C {A B : Subgroup G} (hBA : B ≤ A) {n : G}
    (hnB : n ∈ normalizer (B : Set G)) (hnA : n ∈ normalizer (A : Set G)) {c : G}
    (hc : c ∈ centMod A B) (hcc : c ∈ centralizer (A : Set G)) :
    n * c * n⁻¹ ∈ centMod A B ⊓ centralizer (A : Set G) := by
  have hninA : n⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hnA
  constructor
  · constructor
    · exact (normalizer (B : Set G)).mul_mem
        ((normalizer (B : Set G)).mul_mem hnB hc.1) ((normalizer (B : Set G)).inv_mem hnB)
    · intro a ha
      have hu : n⁻¹ * a * n ∈ A := by
        simpa using (Subgroup.mem_normalizer_iff.mp hninA a).mp ha
      have hcu : c * (n⁻¹ * a * n) * c⁻¹ * (n⁻¹ * a * n)⁻¹ ∈ B := hc.2 _ hu
      have hmemB : n * (c * (n⁻¹ * a * n) * c⁻¹ * (n⁻¹ * a * n)⁻¹) * n⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp hnB _).mp hcu
      convert hmemB using 1
      group
  · refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have hu : n⁻¹ * a * n ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp hninA a).mp ha
    calc a * (n * c * n⁻¹) = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by
            rw [← Subgroup.mem_centralizer_iff.mp hcc (n⁻¹ * a * n) hu]
      _ = (n * c * n⁻¹) * a := by group

private theorem sec9n_priv_centMod_le_normalizer_inf {A B : Subgroup G} (hBA : B ≤ A) :
    centMod A B ≤
      normalizer ((centMod A B ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hnA : n ∈ normalizer (A : Set G) := sec9n_centMod_le_normalizer hBA hn
  refine Subgroup.mem_normalizer_iff.mpr fun c => ⟨?_, ?_⟩
  · intro hc
    exact sec9n_priv_conj_mem_C hBA hn.1 hnA hc.1 hc.2
  · intro hc
    have hni : n⁻¹ ∈ centMod A B := (centMod A B).inv_mem hn
    have hniA : n⁻¹ ∈ normalizer (A : Set G) := (normalizer (A : Set G)).inv_mem hnA
    have hconj : n⁻¹ * (n * c * n⁻¹) * (n⁻¹)⁻¹ ∈
        centMod A B ⊓ centralizer (A : Set G) :=
      sec9n_priv_conj_mem_C hBA hni.1 hniA hc.1 hc.2
    have hc' : n⁻¹ * (n * c * n⁻¹) * n = c := by group
    simpa [hc'] using hconj

theorem sec9n_oddCore_eq (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB : Asc82Sec8B)
    (hT : Asc82Tab9M) (hctx : Sec9Choice G t L S z g B t₀) :
    centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) =
      oddCoreIn (centMod (Asub9 t t₀ B) B) ⊔ Asub9 t t₀ B := by
  have hctx' : Sec9Ctx G t L S z g B t₀ := hctx.toSec9Ctx
  have hAel : CFSG.Open.IsElemAbelian 2 (Asub9 t t₀ B) := sec9n_A_elem hctx'
  have hBA : B ≤ Asub9 t t₀ B := by rw [Asub9]; exact le_sup_right
  have hAcent : Asub9 t t₀ B ≤ centralizer (Asub9 t t₀ B : Set G) := by
    haveI : IsMulCommutative (Asub9 t t₀ B) := hAel.1
    intro a ha
    exact Subgroup.mem_centralizer_iff.mpr fun a' ha' => setLike_mul_comm ha' ha
  have hAN : Asub9 t t₀ B ≤ centMod (Asub9 t t₀ B) B :=
    sec9n_le_centMod hBA (fun a ha a' ha' => CFSG.Open.IsElemAbelian.comm hAel ha ha')
  have hNA : centMod (Asub9 t t₀ B) B ≤ normalizer (Asub9 t t₀ B : Set G) :=
    sec9n_centMod_le_normalizer hBA
  have hAC : Asub9 t t₀ B ≤
      centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) :=
    le_inf hAN hAcent
  have hsyl : IsSylow2Of (Asub9 t t₀ B)
      (centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G)) :=
    sec9n_sylow_of_le (sec9n_sylow_centA h36 h68 hB hT hctx) hAC inf_le_right
  have hAd : Asub9 t t₀ B ⊔
      oddCoreIn (centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G)) =
      centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) :=
    sup_oddCoreIn_of_central_sylow hsyl
      (fun k hk z hz => Subgroup.mem_centralizer_iff.mp hk.2 z hz)
  have hnormal : ((centMod (Asub9 t t₀ B) B ⊓
      centralizer (Asub9 t t₀ B : Set G)).subgroupOf (centMod (Asub9 t t₀ B) B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
      (sec9n_priv_centMod_le_normalizer_inf hBA)
  have hOCN : oddCoreIn (centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G)) ≤
      oddCoreIn (centMod (Asub9 t t₀ B) B) :=
    oddCoreIn_le_of_normal inf_le_left hnormal
  have hPn : ((Asub9 t t₀ B).subgroupOf (centMod (Asub9 t t₀ B) B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mpr hNA
  have hcommNO := commute_of_normal_two_odd hAN
    (oddCoreIn_normal (centMod (Asub9 t t₀ B) B)).1 hPn
    (oddCoreIn_normal (centMod (Asub9 t t₀ B) B)).2
    (CFSG.Open.IsElemAbelian.isPGroup hAel)
    (odd_card_oddCoreIn (centMod (Asub9 t t₀ B) B))
  have hONA : oddCoreIn (centMod (Asub9 t t₀ B) B) ≤
      centralizer (Asub9 t t₀ B : Set G) := by
    intro o ho
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => hcommNO a ha o ho
  have hONC : oddCoreIn (centMod (Asub9 t t₀ B) B) ≤
      centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) :=
    le_inf (oddCoreIn_normal (centMod (Asub9 t t₀ B) B)).1 hONA
  apply le_antisymm
  · rw [← hAd]
    exact sup_le le_sup_right (hOCN.trans le_sup_left)
  · exact sup_le hONC hAC

end CFSG.OddStandard.SmallF3.Omega
