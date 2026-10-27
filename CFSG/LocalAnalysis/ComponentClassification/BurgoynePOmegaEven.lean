module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Blueprint

theorem burgoynePropA_POmegaPlus (X : Type) [Group X] [Finite X] (hX : IsM4 X) {n p f : ℕ}
    (hp2 : p ≠ 2) (hn5 : 5 ≤ n)
    (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaPlus n p f) (t : X)
    (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinatePlus hmod K hKc e
    have hsurj₀ := oSurj_coordinatePlus hmod K hKc hn5 e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K)
      (regular_coordinateQuadPlus n K (by omega)).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadPlus n K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    have hsurj := hsurj₀.transport 1 1 hS₁
    set θ := (coordinatePlusWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
    obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
    by_cases hσ : g.val.right = 1
    · exact inner_even_propAConclusion hK hp hKc (by omega) hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hY hYO
    · exact field_propAConclusion hK (by omega) hp hf hKc hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hY hYO
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

theorem burgoynePropA_POmegaMinus (X : Type) [Group X] [Finite X] (hX : IsM4 X) {n p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaMinus n p f) (t : X)
    (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hn⟩, K, _, _, hKc, b, c, hirr, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hn1 : 1 ≤ n := by omega
    have hker₀ := oKer_coordinateMinus hmod K hKc b c hirr e
    have hsurj₀ := oSurj_coordinateMinus hmod K hKc b c hirr e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadMinus n K hn1 b c)
      (regular_coordinateQuadMinus n K b c hn hirr).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadMinus n K hn1 b c v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    have hsurj := hsurj₀.transport 1 1 hS₁
    set θ := (coordinateMinusWitnessEquiv K hn1 b c e).trans (oTransport 1 1 hS₁) with hθ
    obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
    by_cases hσ : g.val.right = 1
    · exact inner_even_propAConclusion hK hp hKc hn hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hY hYO
    · exact field_propAConclusion hK (by omega) hp hf hKc hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hY hYO
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.O
