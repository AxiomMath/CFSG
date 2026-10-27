module

public import CFSG.ClassicalInvolution.SmallCases.A7CoreClass
public import CFSG.ClassicalInvolution.Asc77.AscFusionR2

public section

namespace CFSG.ClassicalInvolution.A7Core

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7
  CFSG.ClassicalInvolution.Hat2A7R CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem fusion_chain_contradiction {K J : Subgroup F} {z t : F} (hK : IsClassical2A7 ⊤ K z)
    (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv4 : 4 ≤ orderOf v) (hvz : v * z = z * v)
    {κ : F} (hκK : κ ∈ K) (hκ2 : κ * κ = z) (hκn : (v * v)⁻¹ * κ * (v * v) = κ⁻¹)
    (hcomm : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ) {I : Subgroup F}
    (hI : IsClassical2A7 ⊤ I (κ * (v⁻¹ * κ * v))) : False := by
  have hJt : IsUniqueInvolution J t := isUniqueInvolution hJ
  have hz2 : z * z = 1 := hK.mul_self
  obtain ⟨hδ2, hnδ, hδvδ⟩ := AscFusion.kappa_delta_facts hz2 hvz hκ2 hκn hcomm
  set δ : F := κ * (v⁻¹ * κ * v) with hδ
  have hδt : t * δ = δ * t := by
    have htn : t ∈ Subgroup.zpowers (v * v) :=
      AscFusion.mem_zpowers_sq_of_isUniqueInvolution hJt hvJ hv2 hv4
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp htn
    exact (Commute.zpow_left (show Commute (v * v) δ from hnδ) k).eq
  have hJδ : J ≠ conjSub δ J := by
    intro h
    have h1 : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
    rw [← h, hδvδ] at h1
    have h2 : z ∈ J := by
      have := J.mul_mem (J.inv_mem hvJ) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases hJt.unique z h2 hz2 with h3 | h3
    · exact (isUniqueInvolution hK).ne_one h3
    · exact hne h3.symm
  have hcommv : v * (δ * v * δ⁻¹) = (δ * v * δ⁻¹) * v := by
    rw [hδvδ]
    calc v * (v * z) = (v * v) * z := by rw [mul_assoc]
      _ = v * (z * v) := by rw [mul_assoc, hvz]
      _ = v * z * v := by rw [mul_assoc]
  have hnz : (v * v) * z ∈ Subgroup.normalizer (I : Set F) := by
    have := diag_mem_normalizer hJ hδ2 hδt.symm hJδ hI hvJ hv2 hcommv
    rwa [hδvδ, ← mul_assoc] at this
  have hκ4 : orderOf κ = 4 :=
    AscFusion.orderOf_eq_four_of_sq_eq hz2 (isUniqueInvolution hK).ne_one hκ2
  have hκδ : κ * δ = δ * κ := by
    conv_lhs => rw [hcomm]
    rw [hδ]
    group
  have hz : z ∈ Subgroup.normalizer (I : Set F) :=
    mem_normalizer_of_commute_orderOf_four hK hI hκK hκ4 hκδ
  have hnI : v * v ∈ Subgroup.normalizer (I : Set F) := by
    have := (Subgroup.normalizer (I : Set F)).mul_mem hnz
      ((Subgroup.normalizer (I : Set F)).inv_mem hz)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this
  have htI : t ∈ Subgroup.normalizer (I : Set F) :=
    Subgroup.zpowers_le.mpr hnI (AscFusion.mem_zpowers_sq_of_isUniqueInvolution hJt hvJ hv2 hv4)
  exact hJδ (conjSub_eq_of_mem_normalizer (mem_normalizer_symm hJ hI htI)).symm

theorem core_four {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) {J : Subgroup F} {t : F}
    (hJ : IsClassical2A7 ⊤ J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J) (hv4 : orderOf v = 4)
    (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F)) :
    v ∈ Subgroup.normalizer (K : Set F) := by
  by_contra hv
  have hnt := nontrivAction hK hJ hne hvJ hv4 hvz hvK hv
  obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ := exists_kappa hK hv4 hvz hv hvK hnt
  obtain ⟨I, hI⟩ := deltaClassical hK hJ hne hvJ hv4 hvz hvK hv hκK hκ2 hcomm
  exact fusion_chain_contradiction hK hJ hne hvJ (isPGroup_zpowers_of_orderOf_four hv4)
    (by omega) hvz hκK hκ2 hκn hcomm hI

end CFSG.ClassicalInvolution.A7Core
