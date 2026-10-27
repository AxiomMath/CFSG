module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOEvenInner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOddFam
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFormEven

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O

theorem oddLieCoreFamilyInput_pomegaMinus : OddLieCoreFamilyInput .POmegaMinus := by
  intro S _ _ _ hna n p f hp hp2 hadm hm hL2 i hi Ro hRodd hRi hRc
  have hcl : StatedClassicalModel S .POmegaMinus n p f := by
    rcases hm with ⟨-, h⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    · exact h
    all_goals exact absurd htag (by decide)
  have hmod := hcl
  obtain ⟨⟨hp', hf, hn⟩, K, _, _, hKc, b, c, hirr, ⟨e⟩⟩ := hcl
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
  have hZ := center_eq_bot_of_simple hna
  have hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))) :=
    ClO.conj_injective_of_mulEquiv θ (conj_injective hZ)
  refine commute_of_congr θ (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  obtain ⟨g, hg⟩ := hsurj (MulAut.congr θ i)
  have hi' : orderOf (oκ _ g) = 2 := by
    rw [← hg, MulEquiv.orderOf_eq]
    exact hi
  rw [hg] at hR'i hR'c
  by_cases hσ : g.val.right = 1
  · exact ClO.commute_inner_even hK hp hKc hn hR hker hsurj hinj hσ hi' hR'odd hR'i hR'c
  · exact ClO.commute_field hK (by omega) hp hf hKc hR hker hsurj hinj hσ hi' hR'odd hR'i hR'c

theorem ClO.commute_pomegaPlus_five (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n)
    (hm : LieModel S .POmegaPlus n p f) (i : MulAut S) (hi : orderOf i = 2)
    (Ro : Subgroup (MulAut S)) (hRodd : Odd (Nat.card Ro)) (hRi : ∀ r ∈ Ro, r * i = i * r)
    (hRc : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ Ro,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have hcl : StatedClassicalModel S .POmegaPlus n p f := by
    rcases hm with ⟨-, h⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    · exact h
    all_goals exact absurd htag (by decide)
  have hmod := hcl
  obtain ⟨⟨hp', hf, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hcl
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
  have hZ := center_eq_bot_of_simple hna
  have hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))) :=
    ClO.conj_injective_of_mulEquiv θ (conj_injective hZ)
  refine commute_of_congr θ (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  obtain ⟨g, hg⟩ := hsurj (MulAut.congr θ i)
  have hi' : orderOf (oκ _ g) = 2 := by
    rw [← hg, MulEquiv.orderOf_eq]
    exact hi
  rw [hg] at hR'i hR'c
  by_cases hσ : g.val.right = 1
  · exact ClO.commute_inner_even hK hp hKc (by omega) hR hker hsurj hinj hσ hi' hR'odd hR'i hR'c
  · exact ClO.commute_field hK (by omega) hp hf hKc hR hker hsurj hinj hσ hi' hR'odd hR'i hR'c

end CFSG.ComponentClassification.Foote5.OddLieCore
