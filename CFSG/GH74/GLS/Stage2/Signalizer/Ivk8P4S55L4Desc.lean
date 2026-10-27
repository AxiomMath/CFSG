module

public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
import all CFSG.RankThree.SteinbergR3ELinearFieldDescent

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.UnitaryDescent CFSG.RankThree.LinearDescent
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {K : Type} [Field K] {n : ℕ}

theorem linear_prime_descent_char {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hn : 3 ≤ n)
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime)
    {a : MulAut (projectiveSL n K)} (haE : a ∈ semilinearAutGroup n K)
    (haD : a ∉ linearAutGroup n K) (hap : orderOf a = p) :
    p ∣ f ∧ ∃ σ : K ≃+* K, orderOf σ = p ∧
      (∃ h ∈ linearAutGroup n K, a = h * fieldAut n K σ * h⁻¹) ∧
        Nat.card (semilinearFixedSubfield σ) = ℓ ^ (f / p) :=
  linear_prime_semilinear_field_descent_core hℓ hf hn hK hp a haE haD hap

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
