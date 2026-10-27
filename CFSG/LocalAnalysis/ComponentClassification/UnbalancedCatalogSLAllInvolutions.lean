module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLSemilinearInvolution
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSULinearRadical

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

open EvenLinearSL

theorem even_linear_all_involution_centralizer_exceptions {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = 2 ^ f)
    {H : Subgroup (MulAut (projectiveSL n K))} (hH : inner (projectiveSL n K) ≤ H)
    {a : MulAut (projectiveSL n K)} (ha : orderOf a = 2)
    (hne : CFSG.oddCore ↥(H ⊓ centralizer {a}) ≠ ⊥) :
    ((n = 3 ∧ Nat.card K = 2) ∨ (n = 3 ∧ Nat.card K = 4)) ∧ a ∉ semilinearAutGroup n K := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have haE : a ∉ semilinearAutGroup n K := fun h =>
    hne (even_linear_semilinear_involution_full_centralizer_odd_core hn hf hK hH h ha)
  refine ⟨?_, haE⟩
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hn
  obtain ⟨A, σ, ε, hε, rfl⟩ := hform a
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · exfalso
    apply haE
    rw [pow_zero, mul_one]
    exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A))
      (fieldAut_mem_semilinearAutGroup σ)
  rw [pow_one] at ha hne
  by_cases hσ : σ = 1
  ·
    subst hσ
    rw [map_one, mul_one] at ha hne
    have ha2 : (conjAut n K A * dualAut n K) ^ 2 = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one _
    obtain ⟨-, ⟨H₀, C, -, hα, hC⟩, -⟩ :=
      UnitaryHigher.even_linear_pure_graph_involution_normal_forms hf hK hn A ha2
    set g := conjAut n K H₀ with hg
    set β := conjAut n K C * dualAut n K with hβ
    rw [hα] at hne
    have hne' : CFSG.oddCore ↥(H.map (MulAut.conj g⁻¹).toMonoidHom ⊓ centralizer {β}) ≠ ⊥ :=
      fun h => hne (EvenCatalog.oddCore_eq_bot_of_mulEquiv
        (EvenCatalog.centralizerConjEquivMap H g β).symm h)
    have hinnH' : inner (projectiveSL n K) ≤ H.map (MulAut.conj g⁻¹).toMonoidHom :=
      EvenCatalog.inner_le_map_conj hH g
    have hC' : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
        ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = UnitaryHigher.blockSwapJ n r := by
      rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
      · exact Or.inl h1
      · exact Or.inr ⟨r, hr, hJ⟩
    obtain ⟨-, -, -, -, -, -, hcan⟩ :=
      even_linear_canonical_graph_symplectic_centralizers hf hK hn C hC'
    rcases hC with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
    · rcases Nat.even_or_odd n with ⟨r, hr⟩ | hodd
      ·
        exfalso
        have hC1 : C = 1 := Units.ext h1
        have hβδ : β = dualAut n K := by rw [hβ, hC1, map_one, one_mul]
        rw [hβδ] at hne'
        have hrad := (even_linear_nonalternating_graph_radical hf hK (show n = 2 * r by omega)
          (by omega) ⟨0, by omega⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.2
        exact hne' (hrad _ hinnH')
      ·
        by_contra hexc
        have hq : ¬(n = 3 ∧ Nat.card K = 2 ∧ (C : Matrix (Fin n) (Fin n) K) = 1) := by
          rintro ⟨h3, h2, -⟩
          exact hexc (Or.inl ⟨h3, h2⟩)
        exact hne' ((hcan (Or.inr ⟨h1, hodd⟩)).2 _ hinnH' hq)
    ·
      exfalso
      have hq : ¬(n = 3 ∧ Nat.card K = 2 ∧ (C : Matrix (Fin n) (Fin n) K) = 1) := by
        rintro ⟨h3, -, -⟩
        omega
      exact hne' ((hcan (Or.inl ⟨r, hr, hJ⟩)).2 _ hinnH' hq)
  ·
    right
    exact (even_linear_graph_field_involution_odd_core_exception hn hf hK hH A hσ ha).2 hne

end CFSG.ComponentClassification.UnbalancedCatalog
