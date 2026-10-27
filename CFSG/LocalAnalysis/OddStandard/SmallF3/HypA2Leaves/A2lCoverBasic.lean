module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.FStarFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.QuotAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Inputs

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Subgroup CFSG.Blueprint CFSG.ComponentClassification
open CFSG.OddStandard.SmallF3.HypA2 (TypU CentralDatum IsFStar FStarSimple)
open scoped MatrixGroups

@[expose] def a2lNegOne (F : Type) [Field F] : SL(2, F) :=
  ⟨-1, by simp [Matrix.det_neg]⟩

theorem a2lNegOne_sq (F : Type) [Field F] : a2lNegOne F ^ 2 = 1 := by
  refine Subtype.ext ?_
  change ((-1 : Matrix (Fin 2) (Fin 2) F)) ^ 2 = 1
  rw [neg_one_sq]

theorem a2lNegOne_ne_one (F : Type) [Field F] (h : ringChar F ≠ 2) : a2lNegOne F ≠ 1 := by
  intro h1
  have h2 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  simp only [a2lNegOne, Matrix.SpecialLinearGroup.coe_one] at h2
  exact Ring.neg_one_ne_one_of_char_ne_two h (by simpa using h2)

theorem a2l_centralDatum_of_embedding {K : Type} [Group K] {F : Type} [Field F] [Fintype F]
    {q₀ : ℕ} (hodd : Odd q₀) (h5 : 5 ≤ q₀) (hF : Fintype.card F = q₀)
    (φ : SL(2, F) →* K) (hφ : Function.Injective φ) (hz : φ (a2lNegOne F) ∈ center K)
    (hTU : TypU K) : CentralDatum K := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    have h1 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.1 h
    rw [hF] at h1
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_iff.2 h1)
  refine ⟨q₀, φ.range, φ (a2lNegOne F), hodd, h5, ?_, hz, ⟨_, rfl⟩, ?_, hTU⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, a2lNegOne_sq, map_one]
    · intro h1
      exact a2lNegOne_ne_one F hchar (hφ (by rw [h1, map_one]))
  · exact ⟨F, inferInstance, inferInstance, hF, ⟨(MonoidHom.ofInjective hφ).symm⟩⟩

theorem a2l_isFStar_of_two_u43 {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) (hc : Nat.card (center K) = 2)
    (hm : LieModel (K ⧸ center K) .PSU 4 3 1) : IsFStar K := by
  have hO : pPrimeCore 2 K = ⊥ := HypA2.pPrimeCore_eq_bot_of_isQuasisimple hq hZ
  let e : K ⧸ pPrimeCore 2 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hcen : (center (K ⧸ pPrimeCore 2 K)).map e.toMonoidHom = center K :=
    Subgroup.map_center_eq e
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))))
  · have h1 := Subgroup.card_map_of_injective (K := center (K ⧸ pPrimeCore 2 K))
      (f := e.toMonoidHom) e.injective
    rw [hcen] at h1
    exact h1.symm.trans hc
  · exact LieModel.of_mulEquiv (QuotientGroup.congr _ _ e hcen).symm hm

theorem a2l_typU_of_not_inChev2 {K : Type} [Group K] [Finite K] (hq : IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) (hS : FStarSimple (K ⧸ center K))
    (hI : ¬ GH74.GLS.InChev2 (K ⧸ center K)) : TypU K := by
  have hO : pPrimeCore 2 K = ⊥ := HypA2.pPrimeCore_eq_bot_of_isQuasisimple hq hZ
  have hZs : Open.fusionZStar K = center K := HypA2.fusionZStar_eq_center_of_pPrimeCore_eq_bot hO
  let e : K ⧸ Open.fusionZStar K ≃* K ⧸ center K := QuotientGroup.quotientMulEquivOfEq hZs
  refine Or.inr (Or.inl ⟨3, Nat.prime_three, by norm_num, ?_, ?_⟩)
  · exact (HypA2.isSimpleChevalleyOver_congr 3 e).2
      (HypA2.isSimpleChevalleyOver_three_of_fStarSimple hS)
  · rw [HypA2.inChev2_congr e]
    exact hI

private theorem false_of_card {S : Type} [Group S]
    (hC : Nat.card S ∈ ({60, 168, 6048} : Finset ℕ) ∨ LieModel S .PSL 2 3 2 ∨
      LieModel S .PSp 2 3 1) {c : ℕ} (hc : Nat.card S = c)
    (hne : c ∉ ({60, 168, 6048, 360, 25920} : Finset ℕ)) : False := by
  rcases hC with h | h | h
  · exact hne (by rw [← hc]; simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢; omega)
  · have h1 := GH74.card_of_lieModel_PSL (G := S) (n := 2) (p := 3) (f := 2) (by norm_num) h
    have h2 : Nat.card S = 360 := by rw [h1]; decide
    exact hne (by rw [← hc, h2]; decide)
  · have h1 := GH74.card_of_lieModel_PSp (G := S) (n := 2) (p := 3) (f := 1) (by norm_num)
      (by norm_num) h
    have h2 : Nat.card S = 25920 := by rw [h1]; decide
    exact hne (by rw [← hc, h2]; decide)

theorem a2l_not_inChev2_psl43 (hC : HypA2.ChevOddInChev2) {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSL 4 3 1) : ¬ GH74.GLS.InChev2 S := fun hI =>
  false_of_card (hC S 3 Nat.prime_three (by norm_num) ⟨.PSL, 4, 1, h⟩ hI)
    (c := Open.ordA (4 - 1) (3 ^ 1))
    (GH74.card_of_lieModel_PSL (G := S) (n := 4) (p := 3) (f := 1) (by norm_num) h) (by decide)

theorem a2l_not_inChev2_psu43 (hC : HypA2.ChevOddInChev2) {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSU 4 3 1) : ¬ GH74.GLS.InChev2 S := fun hI =>
  false_of_card (hC S 3 Nat.prime_three (by norm_num) ⟨.PSU, 4, 1, h⟩ hI)
    (c := Open.ordTwistedA (4 - 1) (3 ^ 1))
    (GH74.card_of_lieModel_PSU (G := S) (n := 4) (p := 3) (f := 1) (by norm_num) (by norm_num) h)
    (by decide)

end CFSG.OddStandard.SmallF3.HypA2Leaves
