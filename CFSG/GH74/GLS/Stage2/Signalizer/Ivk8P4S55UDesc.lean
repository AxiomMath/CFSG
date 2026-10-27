module

public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
import all CFSG.RankThree.SteinbergR3EUnitaryFieldDescent

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.UnitaryDescent
open CFSG.LieType.Steinberg (exists_conjTr_mul_mul_eq_one)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.LieType.Universal.Unitary (conjTr)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem unitary_prime_descent_char (h : UnitaryFieldData ℓ f K) {n : ℕ}
    (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (ha : orderOf a = p) (σ : K ≃+* K)
    (hσa : primeFormFieldFactor h isPrimeFormGram_one hn hq a = σ) (hσ : orderOf σ = p) :
    p ∣ f ∧ Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / p)) ^ 2 ∧
      (∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ (f / p))) ∧
      (∀ x : K, h.norm x = 1 → σ (normσ σ p x) = normσ σ p x ∧
        normσ σ p x ^ (ℓ ^ (f / p) + 1) = 1) ∧
      (∀ y : K, σ y = y → y ^ (ℓ ^ (f / p) + 1) = 1 →
        ∃ x : K, h.norm x = 1 ∧ normσ σ p x = y) ∧
      ∃ M : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ * a *
            primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M =
          primeFormFieldHom h isPrimeFormGram_one σ :=
  CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent_core h hn hq hp hp2 a ha σ hσa
    hσ

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
