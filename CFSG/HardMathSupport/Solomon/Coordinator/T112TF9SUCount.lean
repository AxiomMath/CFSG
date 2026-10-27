module

public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_fieldFactor_ne_one [Finite K] (h : UnitaryFieldData p f K)
    (hq : ¬(3 = 3 ∧ p ^ f = 2)) (hpK : 3 ∣ Nat.card Kˣ)
    (H : Subgroup (MulAut (U3T h))) (hH : CFSG.Open.IsElemAbelian 3 H) (h27 : Nat.card H = 27) :
    ∃ α ∈ H, primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq α ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC (le_refl 3) hq
  let ρ := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hker' : ∀ A : U3U h, ρ A = 1 ↔ (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
    exact u3_conj_eq_one_iff h A
  have hHρ : H ≤ ρ.range := fun α hα => by
    have : α ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hker, MonoidHom.mem_ker]
      exact hcon α hα
    exact this
  have := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel Nat.prime_three
    (by norm_num) hpK (by norm_num) (U3U h) ρ hker' H hHρ hH
  rw [h27] at this
  norm_num at this

end CFSG.HardMathSupport.Solomon.Coordinator
