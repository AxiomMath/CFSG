module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSuz

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.SuzOuter

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.SuzOddCore CFSG.SeitzReduction.SporadicRefine
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

section Suz


noncomputable def centM_conj_equiv {c : Equiv.Perm (Fin 1782)} (hc : c ∈ suzT)
    (t : Equiv.Perm (Fin 1782)) :
    ↥(centM t) ≃* ↥(centM (c * t * c⁻¹)) := by
  have hn : c ∈ Subgroup.normalizer (suzM : Set (Equiv.Perm (Fin 1782))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => suzT_conj_mem_suzM hc hm, fun hm => ?_⟩
    have := suzT_conj_mem_suzM (suzT.inv_mem hc) hm
    rwa [show c⁻¹ * (c * m * c⁻¹) * c⁻¹⁻¹ = m by group] at this
  have e1 : centM t = suzM ⊓ centralizer {t} := inf_comm _ _
  have e2 : centM (c * t * c⁻¹) = suzM ⊓ centralizer {c * t * c⁻¹} := inf_comm _ _
  exact ((MulEquiv.subgroupCongr e1).trans (Sporadic.FischerOddCore.fi22CP_conj_equiv hn t)).trans
    (MulEquiv.subgroupCongr e2.symm)

theorem suz_outer_fixedSubgroup_equiv {S : Type} [Group S] (e : S ≃* NativeSporadic.Suz)
    {σ : MulAut S} (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) :
    Nonempty (fixedSubgroup σ ≃* ↥(centM (suzInv 2))) ∨
      Nonempty (fixedSubgroup σ ≃* ↥(centM (suzInv 3))) := by
  set θ : S ≃* suzM := e.trans suzEquivM
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hβ2 := Sporadic.FischerOddCore.congr_mul_self θ σ hσ2
  have hβout : MulAut.congr θ σ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner suzM :=
    fun h => hout ((Sporadic.FischerOddCore.congr_mem_inner_iff θ σ).1 h)
  obtain ⟨t, ht⟩ := suzConjT_bijective.2 (MulAut.congr θ σ)
  have ht2 : t * t = 1 := suzConjT_bijective.1 (by rw [map_mul, ht, hβ2, map_one])
  have htM : (t : Equiv.Perm (Fin 1782)) ∉ suzM := by
    intro h
    apply hβout
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner, ← suzConjT_map_suzM, ← ht]
    exact ⟨t, Subgroup.mem_subgroupOf.2 h, rfl⟩
  have ht1 : (t : Equiv.Perm (Fin 1782)) ≠ 1 := fun h => htM (h ▸ suzM.one_mem)
  have hto : orderOf (t : Equiv.Perm (Fin 1782)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, ht2, Subgroup.coe_one]) ht1
  obtain ⟨i, ⟨hi, c, hc, hct⟩, -⟩ := suzT_involution_class t.2 hto
  obtain ⟨-, -, -, -, -, h0, h1, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    CTUC_Suz_four_exact_involution_centralizers
  have hequiv : Nonempty (fixedSubgroup σ ≃* ↥(centM (suzInv i))) := by
    refine ⟨(MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub σ)).trans
      ((Sporadic.FischerOddCore.fixSubCongr θ σ).trans ?_)⟩
    rw [← ht]
    refine (fixSubSuzConjTEquiv t).trans ?_
    rw [← hct]
    exact (centM_conj_equiv hc (suzInv i)).symm
  interval_cases i
  · exact absurd (hct ▸ suzT_conj_mem_suzM hc h0) htM
  · exact absurd (hct ▸ suzT_conj_mem_suzM hc h1) htM
  · exact .inl hequiv
  · exact .inr hequiv

end Suz

end CFSG.EvenSporadicStandard.SuzOuter
