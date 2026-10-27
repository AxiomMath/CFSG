module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ComponentClassification.GSThmB

theorem phiB_class4
    {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (h4 : vecWeight v = 4) :
    ∃ c ∈ QP45.originalSubgroup, c * Certificates.P43Twin.tA () * c⁻¹ = phiB v := by
  have hs := b0Check_parts.2.2.2.2.2.2
  simp only [Certificates.OmegaB0.classChk, Bool.and_eq_true, List.all_eq_true] at hs
  have hs4 := (hs v (mem_allVecs v)).1
  have e1 : decide (∑ i, v i = 0) = true := decide_eq_true hv
  have e2 : decide ((Finset.univ.filter fun i : Fin 5 => v i ≠ 0).card = 4) = true :=
    decide_eq_true h4
  simp only [e1, e2, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq] at hs4
  obtain ⟨c, hc, hce⟩ := hs4
  exact ⟨c, (mem_elemsT QP45 QP45_ok c).1 hc, hce⟩

theorem phiB_class2
    {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) (h2 : vecWeight v = 2) :
    ∃ c ∈ QP45.originalSubgroup, c * Certificates.P43Twin.tB () * c⁻¹ = phiB v := by
  have hs := b0Check_parts.2.2.2.2.2.2
  simp only [Certificates.OmegaB0.classChk, Bool.and_eq_true, List.all_eq_true] at hs
  have hs2 := (hs v (mem_allVecs v)).2
  have e1 : decide (∑ i, v i = 0) = true := decide_eq_true hv
  have e2 : decide ((Finset.univ.filter fun i : Fin 5 => v i ≠ 0).card = 2) = true :=
    decide_eq_true h2
  simp only [e1, e2, Bool.and_self, Bool.not_true, Bool.false_or, List.any_eq_true,
    decide_eq_true_eq] at hs2
  obtain ⟨c, hc, hce⟩ := hs2
  exact ⟨c, (mem_elemsT QP45 QP45_ok c).1 hc, hce⟩

end CFSG.OddStandard.SmallF3.Omega
