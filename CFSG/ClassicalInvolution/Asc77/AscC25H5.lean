module

public import CFSG.ClassicalInvolution.Asc77.AscC25V34
public import CFSG.ClassicalInvolution.Asc77.AscC25V40

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25H

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77.C25V
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem nuG_z_eq_one (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) :
    nuG hp hq e z = 1 := by
  refine (nuG_eq_one_iff hp hq e (Subgroup.le_normalizer h.hz.mem)).mpr (fun l hl => ?_)
  have : ⁅z, l⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (h.hz.commute_of_mem hl)
  rw [this]
  exact Subgroup.one_mem _

theorem exists_k_nuG (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f)) {a n : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (hnK : n ∈ Subgroup.normalizer (K : Set G))
    (hn'K : t' * n * t' ∈ Subgroup.normalizer (K : Set G))
    (hδa : diagGamma (nuG hp hq e a) = 1)
    (hδ : diagGamma (nuG hp hq e n) = diagGamma (nuG hp hq e (t' * n * t')))
    (hχ : SemidirectProduct.rightHom (nuG hp hq e n) =
      SemidirectProduct.rightHom (nuG hp hq e (t' * n * t')) *
        SemidirectProduct.rightHom (nuG hp hq e a)) :
    ∃ k ∈ K, nuG hp hq e k = nuG hp hq e ((t' * n * t') * (a * z) * n⁻¹) := by
  classical
  have hzK : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer h.hz.mem
  have hazN : a * z ∈ Subgroup.normalizer (K : Set G) := Subgroup.mul_mem _ haK hzK
  have hmN : (t' * n * t') * (a * z) * n⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK)
  have hνm : nuG hp hq e ((t' * n * t') * (a * z) * n⁻¹) =
      nuG hp hq e (t' * n * t') * nuG hp hq e a * (nuG hp hq e n)⁻¹ := by
    rw [nuG_mul hp hq e (Subgroup.mul_mem _ hn'K hazN) (Subgroup.inv_mem _ hnK),
      nuG_mul hp hq e hn'K hazN, nuG_mul hp hq e haK hzK, nuG_inv hp hq e hnK,
      nuG_z_eq_one h hp hq e, mul_one]
  have hδm : diagChar hp hq e ⟨_, hmN⟩ = 1 := by
    rw [diagChar_eq_diagGamma_nuG hp hq e hmN, hνm, map_mul, map_mul, map_inv, hδa, mul_one, ← hδ,
      mul_inv_cancel]
  have hχm : fieldChar hp hq e ⟨_, hmN⟩ = 1 := by
    rw [fieldChar_eq_rightHom_nuG hp hq e hmN, hνm, map_mul, map_mul, map_inv, hχ]
    exact mul_inv_cancel _
  obtain ⟨k, hkK, hk⟩ := exists_mem_K_nuG_eq_inr hp hq e hmN hδm
  rw [hχm, map_one] at hk
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hkK
  have h1 : nuG hp hq e (k⁻¹ * ((t' * n * t') * (a * z) * n⁻¹)) =
      (nuG hp hq e k)⁻¹ * nuG hp hq e ((t' * n * t') * (a * z) * n⁻¹) := by
    rw [nuG_mul hp hq e (Subgroup.inv_mem _ hkN) hmN, nuG_inv hp hq e hkN]
  rw [h1] at hk
  exact ⟨k, hkK, inv_mul_eq_one.mp hk⟩

end Main

end CFSG.ClassicalInvolution.Asc77.C25H
