module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUInner
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddClPSUBar

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (nonempty_mulEquiv_primeFormP_of_lieModel')
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

theorem u42_psu_concrete {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 f K) (hn : 3 ≤ n)
    (σ : MulAut (primeFormP h (idGram K n))) (hσ : orderOf σ = 2)
    {J : Subgroup ↥(fixedSubgroup σ)} (hJ : U42Hyp σ J) :
    n = 4 ∧ f = 1 ∧ ∃ (A : ↥(primeFormUnitary h (idGram K n))) (φ : K ≃+* K),
      (∀ x, φ x = h.bar x) ∧
      σ = primeFormPsi h (isPrimeFormGram_one : IsPrimeFormGram (1 : GL (Fin n) K)) ⟨A, φ⟩ ∧
      ∃ g : ↥(primeFormUnitary h (idGram K n)),
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = -1 ∧
        σ * primeFormConjHom h (idGram K n) g = primeFormConjHom h (idGram K n) g * σ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hq : ¬(n = 3 ∧ 3 ^ f = 2) := fun h3 => by
    have := h3.2
    have h4 : 3 ≤ 3 ^ f := Nat.le_self_pow (by have := h.one_le; omega) 3
    omega
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq σ
  have hff : primeFormFieldFactor h hC hn hq σ = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one σ
    rw [hσ] at h1
    rw [h1, map_one]
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · exfalso
    have hAσ : σ = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    subst hAσ
    exact u42_psu_inner h hn A hσ hJ
  · subst hAφ
    obtain ⟨hn4, hf1, g, hdet, hcomm⟩ := u42_psu_bar h hn A φ hφ hσ hJ
    exact ⟨hn4, hf1, A, φ, hφ, rfl, g, hdet, hcomm⟩

theorem oddU42Shape_PSU : OddU42ShapePSU := by
  intro S _ _ n f hadm hm σ J hσ hJ
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  haveI := h.finite
  obtain ⟨hn4, hf1, -⟩ := u42_psu_concrete h hn (MulAut.congr ψ σ)
    ((u42OrderOf_congr ψ σ).trans hσ) (hJ.congr ψ σ J)
  exact ⟨hn4, hf1⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
