module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryInner
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.RankThree.SteinbergR3ECAFieldFixedLayerQuotient

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.RankThree.FieldFixedLayer
  (linear_unitary_odd_prime_field_fixed_group_solvable_layer_quotient)

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem perfectInLayer_primeFormFieldHom (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    PerfectInLayer (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) :=
  perfectInLayer_of_isSolvable_layer_quotient _
    ((linear_unitary_odd_prime_field_fixed_group_solvable_layer_quotient
      hp hp2 hn).2 ℓ f K h σ hσ)

theorem perfectInLayer_primeFormP (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (β : MulAut (primeFormP h (idGram K n))) (hβ : β ^ p = 1) : PerfectInLayer β := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, hker1, -, -, -, -, hkerD, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  by_cases hσ : primeFormFieldFactor h hC hn hq β = 1
  ·
    have hβD : β ∈ (primeFormFieldFactor h hC hn hq).ker := hσ
    rw [hkerD, primeFormD, MonoidHom.mem_range] at hβD
    obtain ⟨A, rfl⟩ := hβD
    have h1 : primeFormPsi h hC ⟨A ^ p, 1⟩ = 1 := by
      rw [primeFormPsi_apply, map_pow, hβ, map_one, one_mul]
    obtain ⟨-, c, -, hc⟩ := (hker1 _).1 h1
    exact perfectInLayer_primeFormConjHom h hp hpℓ A (by rwa [SubgroupClass.coe_pow] at hc)
  ·
    have : Fact p.Prime := ⟨hp⟩
    have hne : β ≠ 1 := fun h1 => hσ (by rw [h1, map_one])
    have hord : orderOf β = p := orderOf_eq_prime hβ hne
    have hσp : orderOf (primeFormFieldFactor h hC hn hq β) = p :=
      orderOf_eq_prime (by rw [← map_pow, hβ, map_one]) hσ
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq hp hp2 hpℓ β
        hord _ rfl hσp
    have hβeq : β = primeFormConjHom h _ M *
        primeFormFieldHom h isPrimeFormGram_one (primeFormFieldFactor h hC hn hq β) *
        (primeFormConjHom h _ M)⁻¹ := by
      rw [← hM]
      group
    rw [hβeq]
    exact perfectInLayer_conj _ _ (perfectInLayer_primeFormFieldHom h hn hp hp2 _ hσp)

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
