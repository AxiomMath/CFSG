module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.FieldLayer
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.HardMathSupport.Lang.Coordinator
open scoped commutatorElement

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem exists_psu_model {X : Type} [Group X] {n p f : ℕ} (hadm : StatedLieAdmissible .PSU n p f)
    (hm : LieModel X .PSU n p f) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData p f K),
      Nonempty (X ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := (lieModel_classical_iff (by decide)).mp hm
  have h : UnitaryFieldData p f K := ⟨hadm.1, hadm.2.1, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n) (K := K))
  exact ⟨K, inferInstance, h, ⟨(e0.trans (unitaryPSUEquiv h (by have := hadm.2.2.1; omega)).symm).trans
    eP.symm⟩⟩

theorem exists_conj_fieldAut_of_factor_ne_one (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    {ψ : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))} (hψ3 : ψ ^ 3 = 1)
    (hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq ψ ≠ 1) :
    ∃ (σ : K ≃+* K) (u : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      orderOf σ = 3 ∧
        ψ = u * primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ * u⁻¹ := by
  have hψ1 : ψ ≠ 1 := fun h1 => hσ1 (by rw [h1, map_one])
  have hψord : orderOf ψ = 3 := orderOf_eq_prime hψ3 hψ1
  set σ := primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq ψ with hσdef
  have hσp : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, hψ3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσp hσ1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    unitary_prime_semilinear_field_descent' h hn hq Nat.prime_three (by decide) ψ hψord σ rfl hσord
  refine ⟨σ, primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M, hσord, ?_⟩
  rw [← hM]
  group

theorem famOK_psu (hO : LieOrderFormulasInput) (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) (hdiv : ¬ 3 ∣ Nat.gcd n (ℓ ^ f + 1)) :
    FamOK (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro ψ hψ3 hninn
  have hσ1 : primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq ψ ≠ 1 := by
    intro hσ1
    have hD : ψ ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor h (isPrimeFormGram_one (n := n)) hn hq]
      exact hσ1
    exact hninn (mem_inner_of_mem_primeFormD h hn hq Nat.prime_three hdiv hD hψ3)
  obtain ⟨σ, u, hσord, hu⟩ := exists_conj_fieldAut_of_factor_ne_one h hn hq hψ3 hσ1
  exact ⟨u, _, hu, noL2Layer_fieldAut_psu hO h hn hσord⟩

end CFSG.HardMathSupport.Dickson.Sec6.I923
