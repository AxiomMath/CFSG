module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOOddMain
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.O

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.Blueprint

theorem burgoynePropA_POmegaOdd (X : Type) [Group X] [Finite X] (hX : IsM4 X) {n p f : ℕ}
    (hp2 : p ≠ 2) (hL : LieModel (GeneralizedFitting.subgroup X) .POmegaOdd n p f) (t : X)
    (ht : orderOf t = 2) (Y : Subgroup X) (hY : Y ≠ ⊥) (hYO : Y ≤ oddCentralizerCore t) :
    PropAConclusion X t Y := by
  obtain ⟨hsimple, hnab, -, -, -⟩ := hX
  rcases hL with ⟨-, hc⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  · have hmod := hc
    obtain ⟨⟨hp, hf, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hc
    have : Fintype K := Fintype.ofFinite K
    have : Fact p.Prime := ⟨hp⟩
    have : CharP K p := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
    have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have hker₀ := oKer_coordinateOdd hmod K hKc e
    have hsurj₀ := oSurj_coordinateOdd hmod K hKc e
    obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadOdd n K)
      (regular_coordinateQuadOdd n K h2 hn).1
    have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n + 1)) K) : Matrix _ _ K) *ᵥ v) =
        ((1 : Kˣ) : K) * coordinateQuadOdd n K v := by
      intro v
      rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
    have hker := hker₀.transport 1 1 hS₁
    have hsurj := hsurj₀.transport 1 1 hS₁
    set θ := (coordinateOddWitnessEquiv K e).trans (oTransport 1 1 hS₁) with hθ
    obtain ⟨g, hg⟩ := hsurj (socleAction θ t)
    by_cases hσ : g.val.right = 1
    · exact inner_odd_propAConclusion hK (by omega) ⟨n, rfl⟩ hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hY hYO
    · exact field_propAConclusion hK (by omega) hp hf hKc hR hker hsimple hnab θ
        (hsurj.surjX θ t) ht hσ hg hY hYO
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)

end CFSG.ComponentClassification.Burgoyne.O
