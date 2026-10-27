module

public import CFSG.LocalAnalysis.EvenBN.Tits.Thm49EModel
public import Certificates.Data.Thm49ECore

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Thm49E

open Subgroup Certificates.Thm49E CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.EvenBN.Tits.Model

theorem tau_inA_mem {l : Equiv.Perm (Fin 1755)}
    (hl : IsLong l) (hc : l * titsZ = titsZ * l) :
    tauH * inA l ∈ MH ∧ tauH * inA l ∈ GammaH := by
  have hzA : titsZ ∈ titsA := titsD_le_titsA titsZ_mem_titsD
  have hlA : l ∈ titsA := by
    obtain ⟨d, hd, rfl⟩ := hl
    exact mul_mem (mul_mem (titsD_le_titsA hd) hzA) (inv_mem (titsD_le_titsA hd))
  refine ⟨Or.inr ⟨l, hl, hc, rfl⟩, ?_⟩
  simp only [GammaH, Am, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  refine ⟨⟨Subgroup.mem_top _, ?_⟩, ?_⟩
  · simpa [tauH, inA] using hlA
  · refine Prod.ext (by simp [tauH, inA]) ?_
    simpa [tauH, inA] using hc.symm

theorem tau_mem_GammaH : tauH ∈ GammaH := by
  simp only [GammaH, Am, Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  refine ⟨⟨Subgroup.mem_top _, ?_⟩, ?_⟩
  · simpa [tauH] using (one_mem titsA)
  · exact Prod.ext (by simp [tauH, inA]) (by simp [tauH, inA])

end CFSG.LocalAnalysis.EvenBN.Tits.Thm49E
