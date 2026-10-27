module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClassYBruhat
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7CentLevel
public import CFSG.LieType.AlgebraicGroups.ParabolicLangStep

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.E6Pilot (rootProd rootProd_injective RootCommFamily)
open CFSG.LieType.AlgebraicGroups
open CFSG.ComponentClassification.RankTwoExceptional.E7Sec8 (linConjSubgroup
  parabolicSubgroup_le_linConjSubgroup)


theorem entrywiseFrobGL_rootProd {L : Type} [Field L] [CharP L 2]
    (l : List (Fin Tag.E7.rank → ℤ)) (c : (Fin Tag.E7.rank → ℤ) → L) :
    entrywiseFrobGL .E7 L 2 1 (rootProd .E7 L l c) =
      rootProd .E7 L l (fun β => c β ^ 2) := by
  simp only [rootProd, map_list_prod, List.map_map, Function.comp_apply]
  congr 1
  refine List.map_congr_left fun β _ => ?_
  change entrywiseFrobGL .E7 L 2 1 (pinnedX .E7 L β (c β)) = pinnedX .E7 L β (c β ^ 2)
  rw [entrywiseFrobGL_pinnedX, iterateFrobenius_def]
  norm_num

theorem entrywiseFrobGL_yAS {L : Type} [Field L] [CharP L 2] :
    entrywiseFrobGL .E7 L 2 1 (yAS L) = yAS L := by
  rw [yAS, entrywiseFrobGL_rootProd]
  congr 1
  funext β
  simp


theorem yParabolic_le_linConjSubgroup {K : Type} [Field K] [CharP K 2] :
    parabolicSubgroup .E7 K yNodes ≤ linConjSubgroup K yPsi := by
  refine parabolicSubgroup_le_linConjSubgroup yPsi_check.1
    (fun _ hβ => isRoot_of_mem_yPsi hβ) yPsi_comm ?_ ?_
  · intro α hα β hβ
    exact conj_hyp_of_yLevel_nonneg (by
      have h := yLevel_pos_of_mem_parabolicRadicalRoots hα
      omega) β hβ
  · intro j hj β hβ
    have hlev : yLevel (Pi.single j 1 : Fin Tag.E7.rank → ℤ) = 0 := by
      simp only [yLevel, Pi.single_eq_of_ne (Ne.symm hj)]
    have hlev' : yLevel (-(Pi.single j 1) : Fin Tag.E7.rank → ℤ) = 0 := by
      rw [yLevel_neg, hlev, neg_zero]
    exact ⟨conj_hyp_of_yLevel_nonneg hlev.ge β hβ,
      conj_hyp_of_yLevel_nonneg hlev'.ge β hβ⟩

theorem exists_frobFixed_conj_into_yPsi {L : Type} [Field L] [CharP L 2] [PerfectRing L 2]
    [IsAlgClosed L] {x : ModGL .E7 L} (hx : x ∈ adjointGroup .E7 L)
    (hFix : entrywiseFrobGL .E7 L 2 1 (x * yAS L * x⁻¹) = x * yAS L * x⁻¹)
    {W : Set (ModGL .E7 L)} (hWF : ∀ w ∈ W, entrywiseFrobGL .E7 L 2 1 w = w)
    (hWR : ∀ w ∈ W, ∃ c : (Fin Tag.E7.rank → ℤ) → L, x⁻¹ * w * x = rootProd .E7 L yPsi c) :
    ∃ k ∈ adjointGroup .E7 L, entrywiseFrobGL .E7 L 2 1 k = k ∧
      (∃ z ∈ parabolicSubgroup .E7 L yNodes,
        k * (x * yAS L * x⁻¹) * k⁻¹ = z * yAS L * z⁻¹) ∧
      ∀ w ∈ W, ∃ c : (Fin Tag.E7.rank → ℤ) → L, (∀ β ∈ yPsi, c β ^ 2 = c β) ∧
        k * w * k⁻¹ = rootProd .E7 L yPsi c := by
  have hFix' : entrywiseFrobGL .E7 L 2 1 x * yAS L * (entrywiseFrobGL .E7 L 2 1 x)⁻¹ =
      x * yAS L * x⁻¹ := by
    rw [← hFix, map_mul, map_mul, entrywiseFrobGL_yAS, map_inv]
  have hcomm : (x⁻¹ * entrywiseFrobGL .E7 L 2 1 x) * yAS L =
      yAS L * (x⁻¹ * entrywiseFrobGL .E7 L 2 1 x) := by
    calc x⁻¹ * entrywiseFrobGL .E7 L 2 1 x * yAS L
        = x⁻¹ * (entrywiseFrobGL .E7 L 2 1 x * yAS L *
            (entrywiseFrobGL .E7 L 2 1 x)⁻¹) * entrywiseFrobGL .E7 L 2 1 x := by group
      _ = x⁻¹ * (x * yAS L * x⁻¹) * entrywiseFrobGL .E7 L 2 1 x := by rw [hFix']
      _ = yAS L * (x⁻¹ * entrywiseFrobGL .E7 L 2 1 x) := by group
  have hcP : x⁻¹ * entrywiseFrobGL .E7 L 2 1 x ∈ parabolicSubgroup .E7 L yNodes :=
    mem_parabolicSubgroup_of_commute_yAS
      (mul_mem (inv_mem hx) (entrywiseFrobGL_mem (p := 2) 1 hx)) hcomm
  have hN : x⁻¹ * (entrywiseFrobGL .E7 L 2 1 x⁻¹)⁻¹ ∈
      Subgroup.normalizer (parabolicSubgroup .E7 L yNodes : Set (ModGL .E7 L)) := by
    rw [map_inv, inv_inv]
    exact Subgroup.le_normalizer hcP
  obtain ⟨z, hzP, hzk⟩ :=
    exists_entrywiseFrobGL_fixed_mul_of_mem_normalizer_parabolic (p := 2) (τ := .E7)
      (e := 1) (by norm_num) (J := yNodes) (x := x⁻¹) (inv_mem hx) hN
  set k : ModGL .E7 L := z * x⁻¹ with hk
  have hkC : k ∈ adjointGroup .E7 L :=
    mul_mem (parabolicSubgroup_le_adjointGroup .E7 L yNodes hzP) (inv_mem hx)
  have hkFix : entrywiseFrobGL .E7 L 2 1 k = k := hzk
  refine ⟨k, hkC, hkFix, ⟨z, hzP, by rw [hk]; group⟩, ?_⟩
  intro w hw
  obtain ⟨c, hc⟩ := hWR w hw
  have hlin : z ∈ linConjSubgroup L yPsi := yParabolic_le_linConjSubgroup hzP
  obtain ⟨c', hc', -⟩ := hlin.1 c
  refine ⟨c', ?_, ?_⟩
  · have hconj : k * w * k⁻¹ = rootProd .E7 L yPsi c' := by
      calc k * w * k⁻¹ = z * (x⁻¹ * w * x) * z⁻¹ := by rw [hk]; group
        _ = z * rootProd .E7 L yPsi c * z⁻¹ := by rw [hc]
        _ = rootProd .E7 L yPsi c' := hc'
    have hkw : entrywiseFrobGL .E7 L 2 1 (k * w * k⁻¹) = k * w * k⁻¹ := by
      simp only [map_mul, map_inv, hkFix, hWF w hw]
    have hFr : entrywiseFrobGL .E7 L 2 1 (rootProd .E7 L yPsi c') =
        rootProd .E7 L yPsi c' := hconj ▸ hkw
    have heq : rootProd .E7 L yPsi (fun β => c' β ^ 2) = rootProd .E7 L yPsi c' :=
      (entrywiseFrobGL_rootProd yPsi c').symm.trans hFr
    exact rootProd_injective yPsi_nodup (fun _ hβ => pos_of_mem_yPsi hβ) heq
  · calc k * w * k⁻¹ = z * (x⁻¹ * w * x) * z⁻¹ := by rw [hk]; group
      _ = z * rootProd .E7 L yPsi c * z⁻¹ := by rw [hc]
      _ = rootProd .E7 L yPsi c' := hc'

end CFSG.SeitzReduction.E7Pilot
