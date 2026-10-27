module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Red
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Syl
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K]

theorem primeFormConjHom_scalar (h : UnitaryFieldData p f K) {n : ℕ} (C : Matrix (Fin n) (Fin n) K)
    (A : primeFormUnitary h C) (c0 : Kˣ)
    (hA : (A : GL (Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n) c0) :
    primeFormConjHom h C A = 1 := by
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g => ?_
  rw [primeFormConjHom_mk]
  show _ = (g : primeFormP h C)
  congr 1
  apply Subtype.ext
  change (A : GL (Fin n) K) * g * (A : GL (Fin n) K)⁻¹ = g
  have hcen : Matrix.GeneralLinearGroup.scalar (Fin n) c0 ∈ Subgroup.center (GL (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c0, rfl⟩
  have hc := Subgroup.mem_center_iff.1 hcen (g : GL (Fin n) K)
  rw [hA, ← hc, mul_inv_cancel_right]

theorem not_hasElemSection3_four_primeFormP [Finite K] (h : UnitaryFieldData p f K)
    (hq2 : ¬ p ^ f = 2) (hq3 : p ^ f % 3 = 2)
    (P : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))))
    (hP : IsPGroup 3 P) : ¬ HasElemSection3 P 4 := by
  have hq : ¬ (3 = 3 ∧ p ^ f = 2) := fun h' => hq2 h'.2
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h (isPrimeFormGram_one (n := 3) (K := K))
      (by norm_num) hq
  set F := primeFormFieldFactor h (isPrimeFormGram_one (n := 3) (K := K)) (by norm_num) hq
  have hcycK : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hcyc : ∀ H ≤ P, ∃ x ∈ H, ∀ y ∈ H, ∃ k : ℤ, x ^ k * y⁻¹ ∈
      primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro H hHP
    obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := ↥(H.map F))
    obtain ⟨x, hxH, hx⟩ := gen.2
    refine ⟨x, hxH, fun y hy => ?_⟩
    have hmem : (⟨F y, Subgroup.mem_map_of_mem F hy⟩ : ↥(H.map F)) ∈ Subgroup.zpowers gen :=
      hgen _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hk' : (F x) ^ k = F y := by
      have := congrArg (fun z : ↥(H.map F) => (z : K ≃+* K)) hk
      simp only [Subgroup.coe_zpow] at this
      rw [← this]
      simp only [← hx]
    have : F (x ^ k * y⁻¹) = 1 := by rw [map_mul, map_inv, map_zpow, hk', mul_inv_cancel]
    exact ⟨k, hFker ▸ this⟩
  refine not_hasElemSection3_four_of_reduction (primeFormD h _) P hcyc ?_
  intro H0 N0 hH0P hH0D hN0 hcomm hcube
  have hK : Nat.card K % 3 = 1 := by
    rw [h.card_eq_sq, Nat.pow_mod, hq3]
  refine relIndex_le_nine_of_hom hK (primeFormUnitary h _) (primeFormConjHom h _) ?_ hH0D
    (hP.to_le hH0P) hN0 hcomm hcube
  rintro g ⟨c0, hc0⟩
  exact primeFormConjHom_scalar h _ g c0 hc0

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
