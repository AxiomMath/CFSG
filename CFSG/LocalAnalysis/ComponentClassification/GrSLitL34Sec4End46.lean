module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Tools46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal
public import Certificates.Certificate2022
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4DiagMem
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46F
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddOrbitWitness

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem isSylowTwoIn_of_le_oddIn_sup {S N M : Subgroup X} (hS : IsSylowTwoIn S N) (hNM : N ≤ M)
    (hMO : M ≤ oddIn M ⊔ N) : IsSylowTwoIn S M := by
  have hSN : S ≤ N := hS.1
  refine isSylowTwoIn_of_not_dvd (hSN.trans hNM) (isPGroup_of_isSylowTwoIn hS) ?_
  rw [← relIndex_mul_relIndex S N M hSN hNM]
  have h1 := not_two_dvd_relIndex_of_isSylowTwoIn hS
  have hO : Odd (Nat.card (oddIn M)) := odd_card_map_pPrimeCore M
  have hMeq : M = N ⊔ oddIn M :=
    le_antisymm (hMO.trans (by rw [sup_comm])) (sup_le hNM (map_subtype_le _))
  have e1 := relIndex_mul_card (H := N) (K := M)
  rw [inf_eq_left.mpr hNM] at e1
  have e2 := card_sup_mul_inf_eq_mul_of_normalizes (hNM.trans (self_le_normalizer_oddIn M))
  rw [← hMeq, ← e1] at e2
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have e3 : N.relIndex M * Nat.card ↥(N ⊓ oddIn M) = Nat.card (oddIn M) := by
    apply Nat.eq_of_mul_eq_mul_left hNpos
    calc Nat.card N * (N.relIndex M * Nat.card ↥(N ⊓ oddIn M))
        = N.relIndex M * Nat.card N * Nat.card ↥(N ⊓ oddIn M) := by ring
      _ = Nat.card N * Nat.card (oddIn M) := e2
  have h2 : ¬ 2 ∣ N.relIndex M := fun h =>
    (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (h.trans (Dvd.intro _ e3)))
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem normal_oddIn_sup_of_le {J M : Subgroup X} (hJM : J ≤ M)
    (hNM : normalizer (J : Set X) ≤ M) (hMO : M ≤ oddIn M ⊔ normalizer (J : Set X)) :
    ((oddIn M ⊔ J).subgroupOf M).Normal := by
  have hle : oddIn M ⊔ J ≤ M := sup_le (map_subtype_le _) hJM
  rw [normal_subgroupOf_iff_le_normalizer hle]
  refine hMO.trans (sup_le ?_ ?_)
  · intro o ho
    rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj o).injective).ge
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      change o * y * o⁻¹ ∈ _
      exact mem_sup_left (conj_mem_oddIn (map_subtype_le _ ho) hy)
    · rintro _ ⟨j, hj, rfl⟩
      change o * j * o⁻¹ ∈ _
      rw [show o * j * o⁻¹ = (o * (j * o⁻¹ * j⁻¹)) * j by group]
      exact mul_mem (mem_sup_left (mul_mem ho (conj_mem_oddIn (hJM hj) (inv_mem ho))))
        (mem_sup_right hj)
  · intro n hn
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (self_le_normalizer_oddIn M (hNM hn)),
      mem_normalizer_iff_map_conj_eq.mp hn]

theorem mem_zStarIn_oddIn_sup {J M : Subgroup X} (hJM : J ≤ M) (hOJ : oddIn J ≤ oddIn M)
    {b : X} (hbM : b ∈ M) (hb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ zStarIn J) :
    ∀ j ∈ oddIn M ⊔ J, j⁻¹ * b⁻¹ * j * b ∈ zStarIn (oddIn M ⊔ J) := by
  have hJ₁M : oddIn M ⊔ J ≤ M := sup_le (map_subtype_le _) hJM
  have hOJ₁ : oddIn M ≤ oddIn (oddIn M ⊔ J) := fun o ho =>
    GrS5.inf_oddIn_le_oddIn hJ₁M (mem_inf.mpr ⟨ho, mem_sup_left ho⟩)
  have hzJ₁ : zStarIn (oddIn M ⊔ J) = (oddIn M ⊔ J) ⊓ coreActionKernel (oddIn M ⊔ J) :=
    GSThmB.map_fusionZStar_eq _
  have hzJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hJN : J ≤ normalizer ((oddIn M : Subgroup X) : Set X) :=
    hJM.trans (self_le_normalizer_oddIn M)
  have hset : ((oddIn M ⊔ J : Subgroup X) : Set X) = (J : Set X) * (oddIn M : Set X) := by
    rw [sup_comm]
    exact coe_mul_of_left_le_normalizer_right _ _ hJN
  have hOZ : oddIn (oddIn M ⊔ J) ≤ zStarIn (oddIn M ⊔ J) := by
    rw [hzJ₁]
    intro o ho
    refine mem_inf.mpr ⟨map_subtype_le _ ho, mem_coreActionKernel.mpr
      ⟨le_normalizer (map_subtype_le _ ho), fun j hj => ?_⟩⟩
    rw [show j⁻¹ * o⁻¹ * j * o = (j⁻¹ * o⁻¹ * j⁻¹⁻¹) * o by group]
    exact mul_mem (conj_mem_oddIn (inv_mem hj) (inv_mem ho)) ho
  have hZZ : zStarIn J ≤ zStarIn (oddIn M ⊔ J) := by
    intro z hz
    rw [hzJ] at hz
    obtain ⟨hzJ', hzK⟩ := mem_inf.mp hz
    rw [hzJ₁]
    refine mem_inf.mpr ⟨mem_sup_right hzJ', mem_coreActionKernel.mpr
      ⟨le_normalizer (mem_sup_right hzJ'), fun j₁ hj₁ => ?_⟩⟩
    have hj₁' : j₁ ∈ (J : Set X) * (oddIn M : Set X) := hset ▸ hj₁
    obtain ⟨j, hj, o, ho, rfl⟩ := hj₁'
    beta_reduce
    have hc : j⁻¹ * z⁻¹ * j * z ∈ oddIn J := (mem_coreActionKernel.mp hzK).2 j hj
    have hzM : z ∈ M := hJM hzJ'
    rw [show (j * o)⁻¹ * z⁻¹ * (j * o) * z =
      (o⁻¹ * (j⁻¹ * z⁻¹ * j * z) * o⁻¹⁻¹) * (o⁻¹ * (z⁻¹ * o * z⁻¹⁻¹)) by group]
    exact hOJ₁ (mul_mem (conj_mem_oddIn (inv_mem (map_subtype_le _ ho)) (hOJ hc))
      (mul_mem (inv_mem ho) (conj_mem_oddIn (inv_mem hzM) ho)))
  intro j₁ hj₁
  have hj₁' : j₁ ∈ (J : Set X) * (oddIn M : Set X) := hset ▸ hj₁
  obtain ⟨j, hj, o, ho, rfl⟩ := hj₁'
  beta_reduce
  have hoJ₁ : o ∈ oddIn M ⊔ J := mem_sup_left ho
  rw [show (j * o)⁻¹ * b⁻¹ * (j * o) * b =
    (o⁻¹ * (j⁻¹ * b⁻¹ * j * b) * o⁻¹⁻¹) * (o⁻¹ * (b⁻¹ * o * b⁻¹⁻¹)) by group]
  refine mul_mem ?_ (hOZ (hOJ₁ (mul_mem (inv_mem ho) (conj_mem_oddIn (inv_mem hbM) ho))))
  have hz := hZZ (hb j hj)
  rw [hzJ₁] at hz ⊢
  obtain ⟨hz1, hz2⟩ := mem_inf.mp hz
  exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hoJ₁) hz1) (inv_mem (inv_mem hoJ₁)),
    conj_mem_coreActionKernel (le_normalizer (inv_mem hoJ₁)) hz2⟩

end CFSG.ComponentClassification.GrSLit.GrS4

