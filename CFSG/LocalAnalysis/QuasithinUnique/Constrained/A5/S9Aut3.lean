module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6ThreeCore

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3 Subgroup Equiv

theorem aut_inner_of_pow_three {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6))
    (γ : MulAut K) (hγ : ∀ k, γ (γ (γ k)) = k) : ∃ k₀ : K, ∀ a : K, γ a = k₀ * a * k₀⁻¹ := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e₀.trans ψ.symm
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ γ
  have hb3 : b ^ 3 = 1 := by
    have hc : b ^ 3 ∈ A6Models.autA6 := A6Models.autA6.pow_mem hbA 3
    refine centralizer_psl29 hc fun x hx => ?_
    rw [pow_three']
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1 := hb k
    have h2 := hb (γ k)
    have h3 := hb (γ (γ k))
    rw [hγ k] at h3
    rw [h2, h1, hk] at h3
    calc b * b * b * x = (b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹) * (b * b * b) := by group
      _ = x * (b * b * b) := by rw [← h3]
  have hbpsl : b ∈ A6Models.psl29 := by
    have hchk := aut_three_check
    rw [List.all_eq_true] at hchk
    have h1 := hchk _ (code_mem_autL hbA)
    have hc3 : (Core.cpow (code b) 3 != Core.cid) = false := by
      rw [← code_pow, hb3, code_one]; simp
    rw [hc3, Bool.false_or, List.contains_iff_mem] at h1
    exact (mem_psl29_iff _).mpr h1
  refine ⟨φ.symm ⟨b, hbpsl⟩, fun a => ?_⟩
  apply φ.injective
  apply Subtype.ext
  rw [hb a]
  simp

end CFSG.QuasithinUnique.A5
