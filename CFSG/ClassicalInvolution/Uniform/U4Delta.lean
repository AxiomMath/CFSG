module

public import CFSG.ClassicalInvolution.Uniform.U4Action
public import CFSG.ClassicalInvolution.Asc77.AscFusionS11

public section

namespace CFSG.ClassicalInvolution.Uniform.U4

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Hat2A7
open scoped commutatorElement

variable {F : Type} [Group F] [Finite F]

theorem z_acts_nontrivially {K : Subgroup F} {z : F} (hK : Mem3 K z) {J : Subgroup F} {t : F}
    (hJ : Mem3 J t) (hne : t ≠ z) {v : F} (hvJ : v ∈ J) (hv4 : orderOf v = 4)
    (hvz : v * z = z * v) (hvK : v * v ∈ Subgroup.normalizer (K : Set F))
    (hv : v ∉ Subgroup.normalizer (K : Set F))
    (hnt : ¬ ∀ k ∈ K, ⁅v * v, k⁆ ∈ oddCoreOf K) :
    ¬ ∀ j ∈ J, ⁅z, j⁆ ∈ oddCoreOf J := by
  intro hζ
  classical
  have hJt : IsUniqueInvolution J t := hJ.isUniqueInvolution
  have hz2 : z * z = 1 := hK.mul_self
  have hvv : v * v = t := mul_self_eq_of_orderOf_four hJt hvJ hv4
  obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ := exists_kappa hK hv4 hvz hv hvK hnt
  obtain ⟨hδ2, hnδ, hδvδ⟩ := AscFusion.kappa_delta_facts hz2 hvz hκ2 hκn hcomm
  set δ : F := κ * (v⁻¹ * κ * v) with hδ
  have hδt : t * δ = δ * t := by rw [← hvv]; exact hnδ
  have hδt' : δ * t * δ⁻¹ = t := by
    calc δ * t * δ⁻¹ = (t * δ) * δ⁻¹ := by rw [← hδt]
      _ = t := by group
  have hδJ : J ≠ conjSub δ J := by
    intro h
    have h1 : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
    rw [← h, hδvδ] at h1
    have h2 : z ∈ J := by
      have := J.mul_mem (J.inv_mem hvJ) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases hJt.unique z h2 hz2 with h3 | h3
    · exact (hK.isUniqueInvolution).ne_one h3
    · exact hne h3.symm
  have hJ' : Mem3 (conjSub δ J) t := by
    have := hJ.conj δ
    rwa [hδt'] at this
  have hy : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
  have hcomy : ∀ j ∈ J, ⁅δ * v * δ⁻¹, j⁆ ∈ oddCoreOf J :=
    hJ.commutator_mem_of_twin hJ' hδJ hy
  have hvc : ∀ j ∈ J, ⁅v⁻¹, j⁆ ∈ oddCoreOf J := by
    intro j hj
    have h1 := hζ j hj
    have h2 : v⁻¹ * ⁅δ * v * δ⁻¹, j⁆ * v ∈ oddCoreOf J := by
      have := mem_normalizer_oddCoreOf_of_mem_normalizer
        ((Subgroup.normalizer (J : Set F)).inv_mem (Subgroup.le_normalizer hvJ)) (hcomy j hj)
      simpa using this
    have e : ⁅v⁻¹, j⁆ = (v⁻¹ * ⁅δ * v * δ⁻¹, j⁆ * v)⁻¹ * ⁅z, j⁆ := by
      have hz : z = v⁻¹ * (δ * v * δ⁻¹) := by
        rw [hδvδ]
        group
      rw [hz]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (oddCoreOf J).mul_mem ((oddCoreOf J).inv_mem h2) h1
  have hvi : v⁻¹ * v⁻¹ = t := by
    rw [← mul_inv_rev, hvv]
    exact inv_eq_of_mul_eq_one_right hJ.mul_self
  exact hJ.not_forall_comm_of_sq_eq (J.inv_mem hvJ) hvi hvc

end CFSG.ClassicalInvolution.Uniform.U4
