module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1010Lin
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyCover3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique.Setup.Family
  CFSG.GH74.GLS.Stage2.Bender.Thm1

variable {p f : ℕ} {K : Type} [Field K]

instance finite_mulAut_U3T (h : UnitaryFieldData p f K) [Finite K] : Finite (MulAut (U3T h)) :=
  have : Finite (GL (Fin 3) K) := inferInstance
  Finite.of_injective (fun α : MulAut (U3T h) => (α : U3T h → U3T h))
    fun _ _ hαβ => MulEquiv.ext (congrFun hαβ)

open CFSG.HardMathSupport.Timmesfeld.LinearRank in
theorem pRank_mulAut_primeFormP_le_two (h : UnitaryFieldData p f K) [Finite K] (hq2 : 2 < p ^ f)
    (hq : p ^ f % 9 = 2 ∨ p ^ f % 9 = 5) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (U3T h))) ≤ 2 := by
  have hq3 : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩; omega
  have h3f : ¬ 3 ∣ f := by
    rintro ⟨m, rfl⟩
    have := cube_mod_nine (p ^ m)
    rw [← pow_mul, mul_comm] at this
    omega
  have hC : IsPrimeFormGram (1 : GL (Fin 3) K) := UnitaryHigher.isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC (le_refl 3) hq3
  have hring := card_ringAut_and_isCyclic h.prime K h.card
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) ?_
  intro H _ hH
  let Θ := primeFormFieldFactor h hC (le_refl 3) hq3
  have hHD : ∀ α ∈ H, α ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro α hα
    rw [← hker, MonoidHom.mem_ker]
    have hα3 : Θ α ^ 3 = 1 := by rw [← map_pow, hH.2 α hα, map_one]
    have hdvd : orderOf (Θ α) ∣ 2 * f := by
      rw [← hring.1]
      exact orderOf_dvd_natCard _
    have hd3 : orderOf (Θ α) ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
    have hcop : Nat.Coprime (orderOf (Θ α)) 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h1 | h3
      · rw [h1]; exact Nat.coprime_one_left 3
      · exfalso
        have : 3 ∣ 2 * f := h3 ▸ hdvd
        rcases (Nat.Prime.dvd_mul Nat.prime_three).1 this with h | h
        · omega
        · exact h3f h
    have h1 : orderOf (Θ α) = 1 := by
      have := Nat.eq_one_of_dvd_coprimes hcop.symm.symm (dvd_refl _) hd3
      exact this
    exact orderOf_eq_one_iff.1 h1
  have hpK : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    have hsq : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [mul_comm, pow_mul]
    have h3 : p ^ f % 3 = 2 := by omega
    have h4 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h3]
    rw [hsq]
    omega
  let ρ := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hker' : ∀ A : U3U h, ρ A = 1 ↔ (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
    exact u3_conj_eq_one_iff h A
  have hHρ : H ≤ ρ.range := fun α hα => hHD α hα
  have := CFSG.HardMathSupport.Timmesfeld.LinearRank.card_le_of_scalar_kernel Nat.prime_three
    (by norm_num) hpK (by norm_num) (U3U h) ρ hker' H hHρ hH
  convert this using 1

end CFSG.HardMathSupport.Solomon.Coordinator
