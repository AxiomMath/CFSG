module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentDS81OddOrth
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaOdd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePOmegaEven
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.DS81

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.O
open CFSG.Blueprint

theorem oddDichotomyFamily_POmegaOdd : OddDichotomyFamily .POmegaOdd := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  obtain ⟨⟨hp', hf, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
    (regular_coordinateQuadOdd n K h2 hn).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  set θ := (coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
  refine solvableOrComponent_of_mulEquiv θ τ (orth_dichotomy hK hp hKc (by omega) hR (θ τ) ?_)
  rw [MulEquiv.orderOf_eq]
  exact hτ

theorem oddDichotomyFamily_POmegaPlus : OddDichotomyFamily .POmegaPlus := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  obtain ⟨⟨hp', hf, hn⟩, K, _, _, hKc, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K)
    (regular_coordinateQuadPlus n K (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadPlus n K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  set θ := (coordinatePlusWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
  refine solvableOrComponent_of_mulEquiv θ τ (orth_dichotomy hK hp hKc (by omega) hR (θ τ) ?_)
  rw [MulEquiv.orderOf_eq]
  exact hτ

theorem oddDichotomyFamily_POmegaMinus : OddDichotomyFamily .POmegaMinus := by
  intro X _ _ n p f hp hp2 hadm hm τ hτ
  obtain ⟨⟨hp', hf, hn⟩, K, _, _, hKc, b, c, hirr, ⟨e⟩⟩ := hm.statedClassicalModel (by decide)
  have : Fintype K := Fintype.ofFinite K
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn1 : 1 ≤ n := by omega
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n K hn1 b c)
    (regular_coordinateQuadMinus n K b c hn hirr).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadMinus n K hn1 b c v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  set θ := (coordinateMinusWitnessEquiv K hn1 b c e).trans (oTransport 1 1 hS₁) with hθ
  refine solvableOrComponent_of_mulEquiv θ τ (orth_dichotomy hK hp hKc (by omega) hR (θ τ) ?_)
  rw [MulEquiv.orderOf_eq]
  exact hτ

end CFSG.ComponentClassification.CatFC.DS81
