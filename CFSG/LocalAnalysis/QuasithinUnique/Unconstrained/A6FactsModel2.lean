module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore2

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

theorem centralizer_le_P0_of_central {a : P10} (ha : a ∈ P0) (hne : a ≠ 1)
    (hc : ∀ p ∈ P0, a * p = p * a) {c : P10} (hcA : c ∈ A6Models.autA6)
    (hca : c * a = a * c) : c ∈ P0 := by
  have hall := Core.p0_cent_aut
  rw [List.all_eq_true] at hall
  have h1 := hall (code a) ((mem_P0_iff a).1 ha)
  have hcent : (Core.p0Lit.all fun p => Core.cmul (code a) p == Core.cmul p (code a)) = true := by
    rw [List.all_eq_true]
    intro p hp
    obtain ⟨p', hp', rfl⟩ := exists_P0_of_code hp
    rw [beq_iff_eq, ← code_mul, ← code_mul, hc p' hp']
  have hne' : (code a == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro h
    exact hne (code_injective h)
  rw [hcent, hne'] at h1
  simp only [Bool.not_true, Bool.false_or, Bool.or_false] at h1
  rw [List.all_eq_true] at h1
  have h2 := h1 (code c) (code_mem_autL hcA)
  have hcomm : (Core.cmul (code c) (code a) == Core.cmul (code a) (code c)) = true := by
    rw [beq_iff_eq, ← code_mul, ← code_mul, hca]
  rw [hcomm] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  exact (mem_P0_iff c).2 (List.contains_iff_mem.mp h2)

end CFSG.QuasithinUnique.A6Facts
