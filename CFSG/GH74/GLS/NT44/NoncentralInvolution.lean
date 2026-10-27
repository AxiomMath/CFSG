module

public import CFSG.GH74.GLS.C3.Layer1.Defs

import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma53
import CFSG.GH74.GLS.Stage1.Thm4.Alt51Q1
import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic

namespace CFSG.GH74.GLS.NT44

set_option autoImplicit false

public section

theorem exists_involution_mem_sylow_not_mem_zStar_of_isL34Quotient
    {G : Type} [Group G] [Finite G]
    (K P : Subgroup G)
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P K)
    (hL34 : CFSG.GH74.GLS.IsL34Quotient (CFSG.GH74.GLS.kBar K)) :
    ∃ u : G, u ∈ P ∧ orderOf u = 2 ∧ u ∉ CFSG.GH74.GLS.zStar K := by
  obtain ⟨e⟩ :=
    CFSG.ComponentClassification.GrSLit.nonempty_quotient_center_equiv_fusionZStar ↥K
  have htype :
      CFSG.ComponentClassification.GrSLit.IsL34Type (↥K ⧸ CFSG.Open.fusionZStar ↥K) :=
    CFSG.Blueprint.LieModel.of_mulEquiv e hL34
  obtain ⟨w, hwK, hw2, hwZ⟩ :=
    CFSG.ComponentClassification.GrSLit.GrS5.exists_involution_not_mem_zStarIn
      (G := G) (L := K) htype
  have hwz : w ∉ CFSG.GH74.GLS.zStar K := by
    intro hwmem
    apply hwZ
    rw [CFSG.ComponentClassification.GrSLit.zStarIn, Subgroup.mem_map]
    refine ⟨⟨w, hwK⟩, ?_, rfl⟩
    rw [CFSG.ComponentClassification.Sol78.fusionZStar_eq_comap]
    have hhat :=
      (CFSG.GH74.GLS.Stage1.Thm4.Alt51.mem_zStar_iff_hat_mem_center
        (K := K) ⟨w, hwK⟩).1 hwmem
    have hhat' : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨w, hwK⟩ ∈
        Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K) := hhat
    change QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨w, hwK⟩ ∈
      Subgroup.center (↥K ⧸ pPrimeCore 2 ↥K)
    exact hhat'
  have hwne : w ≠ 1 := by
    intro hw1
    rw [hw1] at hwz
    exact hwz (CFSG.GH74.GLS.zStar K).one_mem
  have hworder : orderOf w = 2 := by
    refine orderOf_eq_prime ?_ hwne
    simpa [pow_two] using hw2
  obtain ⟨c, hcK, hcwP⟩ :=
    CFSG.GH74.GLS.Bg.Pu5.exists_conj_mem_of_isSylowOf' (K := K) (T := P) hP hwK
      ⟨1, by simpa using hworder⟩
  refine ⟨c * w * c⁻¹, hcwP, ?_, ?_⟩
  · rw [CFSG.GH74.GLS.Bg.Pu5.orderOf_conj_eq' c w, hworder]
  · intro hu
    have hcinv : c⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.le_normalizer (K.inv_mem hcK)
    have hconj :=
      CFSG.GH74.GLS.Stage1.Thm4.Alt51.zStar_conj (K := K) (s := c⁻¹) hcinv hu
    have heq : c⁻¹ * (c * w * c⁻¹) * (c⁻¹)⁻¹ = w := by group
    rw [heq] at hconj
    exact hwz hconj

end

end CFSG.GH74.GLS.NT44
