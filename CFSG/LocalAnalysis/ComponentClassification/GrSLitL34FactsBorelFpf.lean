
module


public import Certificates.Certificate22204
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

theorem borelFpf
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ B0) (hsT : s ∉ T0) {k : ℕ} (hk : k ∈ [4, 8, 12]) :
    s * wordPerm (tg k) ≠ wordPerm (tg k) * s := by
  have h := Certificates.certificate22204
  simp only [borelOK, allBelow_eq_true, Bool.or_eq_true] at h
  obtain ⟨i, hi, hrep⟩ := enumerates_B0.exists_pos hs
  rcases h i hi with hf | hall
  · exact absurd (mem_of_found_enum enumerates_T0 hrep hf) hsT
  · intro hc
    rw [List.all_eq_true] at hall
    have h1 := hall k hk
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at h1
    exact h1 (((hrep.comp (tabRep_tgT k)).eq_iff ((tabRep_tgT k).comp hrep)).2 hc)

end CFSG.ComponentClassification.GrSLit.L34Facts
