module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSU

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

@[expose] def OddFivePSUInnerInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] (f : ℕ) (h : UnitaryFieldData 5 f K),
    StatedLieAdmissible .PSU n 5 f →
    ∀ A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      orderOf (primeFormConjHom h _ A) = 2 →
      FiveA5Group (fixedSubgroup (primeFormConjHom h _ A)) → n = 3 ∧ f = 1

@[expose] def OddFivePSUGraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] (f : ℕ) (h : UnitaryFieldData 5 f K),
    StatedLieAdmissible .PSU n 5 f →
    ∀ (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (φ : K ≃+* K),
      (∀ x, φ x = h.bar x) → orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 →
      FiveA5Group (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)) → n = 3 ∧ f = 1

theorem oddFiveSL2ListFamilyInput_PSU_of_classes (hinner : OddFivePSUInnerInput)
    (hgraph : OddFivePSUGraphInput) : OddFiveSL2ListFamilyInput .PSU := by
  intro J _ _ hJ hna n f hadm hm α hτ
  have hF := fiveA5Group_of_catSL2Hyp hτ
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := CatLeafProof.nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 5 ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hτ.1
  have hFβ := hF.congr ψ
  suffices hnf : n = 3 ∧ f = 1 by
    obtain ⟨rfl, rfl⟩ := hnf
    exact Or.inr (Or.inr (Or.inl hm))
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC hn hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  rcases UnitaryHigher.ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    exact hinner n K f h hadm A (hAα ▸ hβ) (hFβ.of_eq hAα)
  · exact hgraph n K f h hadm A φ hφ (hAφ ▸ hβ) (hFβ.of_eq hAφ.symm)

end CFSG.SeitzReduction.RankOne
