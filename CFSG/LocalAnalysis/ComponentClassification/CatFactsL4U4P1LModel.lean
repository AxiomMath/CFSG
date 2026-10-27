module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1LAut
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1AutModel

public section

namespace CFSG.ComponentClassification.HarrisLit.P1.L43

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.Th.Native

@[expose] noncomputable def l43Model : AutModel (projectiveSL 4 (ZMod 3)) 80 where
  π := pi
  inj := pi_injective
  cent _ hc := eq_one_of_commute_pi hc
  ext α := by
    obtain ⟨A, ε, hε, rfl⟩ := exists_aut_form α
    exact ⟨perm80 A * swap80 ^ ε, perm_induces A hε⟩

theorem l43_cos (α : MulAut (projectiveSL 4 (ZMod 3))) :
    l43Model.T α ∈ pi.range ∨ (∃ R ∈ l43Runs, l43Model.T α * (tp 80 R.u)⁻¹ ∈ pi.range) ∨
      (∃ u ∈ ([] : List Table), l43Model.T α * (tp 80 u)⁻¹ ∈ pi.range) := by
  obtain ⟨A, ε, hε, rfl⟩ := exists_aut_form α
  rw [← l43Model.eq_T (perm_induces A hε)]
  rcases det_cases A with hA | hA
  · interval_cases ε
    · exact Or.inl (by rw [pow_zero, mul_one]; exact perm80_mem_range hA)
    · refine Or.inr (Or.inl ⟨runuS, by simp only [l43Runs, List.mem_cons, true_or, or_true], ?_⟩)
      rw [show runuS.u = uS from rfl, tp_uS, pow_one, mul_inv_cancel_right]
      exact perm80_mem_range hA
  · have hB := perm80_mem_range (det_mul_dGL_inv hA)
    rw [map_mul, map_inv] at hB
    interval_cases ε
    · refine Or.inr (Or.inl ⟨runuD, by simp only [l43Runs, List.mem_cons, true_or], ?_⟩)
      rw [show runuD.u = uD from rfl, tp_uD, pow_zero, mul_one]
      exact hB
    · refine Or.inr (Or.inl ⟨runuDS, by simp only [l43Runs, List.mem_cons, true_or, or_true],
        ?_⟩)
      rw [show runuDS.u = uDS from rfl, tp_uDS, pow_one]
      have h1 : perm80 A * swap80 * (perm80 dGL * swap80)⁻¹ = perm80 A * (perm80 dGL)⁻¹ := by
        group
      rw [h1]
      exact hB

end CFSG.ComponentClassification.HarrisLit.P1.L43
