module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOOddInner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneOFieldNF

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation (sq_val)
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O
open CFSG.ComponentClassification.Burgoyne.PSL (diagGL coe_diagGL OrthNF)

variable {K : Type} [Field K] {d : ℕ}

theorem ClO.commute_field [Finite K] (hK : ringChar K ≠ 2) (hd5 : 5 ≤ d) {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hKc : Nat.card K = ℓ ^ e) {R : GL (Fin d) K}
    (hR : (R : Matrix (Fin d) (Fin d) K)ᵀ = R) (hker : OKer (oQ R)) (hsurj : OSurj (oQ R))
    (hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))))
    {g : similarityPairs (oQ R)} (hg1 : g.val.right ≠ 1) (hi : orderOf (oκ _ g) = 2)
    {Ro : Subgroup (MulAut (StatedProj (matrixDerived (oQ R))))} (hRodd : Odd (Nat.card Ro))
    (hRi : ∀ y ∈ Ro, y * oκ _ g = oκ _ g * y)
    (hRc : ∀ s, oκ _ g s = s → Odd (orderOf s) → ∀ y ∈ Ro,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hℓ2 : ℓ ≠ 2 := by rw [← ringChar.eq K ℓ]; exact hK
  have hgg : oκ (oQ R) (g * g) = 1 := by
    rw [map_mul, ← pow_two, ← hi, pow_orderOf_eq_one]
  obtain ⟨hσ2', c, hc⟩ := hker _ hgg
  have hσ2 : g.val.right ^ 2 = 1 := by rw [← (sq_val _ g).2]; exact hσ2'
  have hc' : g.val.left * glFieldAut (Fin d) K g.val.right g.val.left =
      GeneralLinearGroup.scalar (Fin d) c := by rw [← (sq_val _ g).1, hc]
  obtain ⟨e', hu, hσ⟩ := exists_unitaryFieldData_of_involution hℓ he hKc hσ2 hg1
  obtain ⟨wF, hwF, S, ν, hS, heq⟩ := exists_field_transport hu hℓ2 h2 (by omega) hR hσ hc'
  have hcg : MulAut.congr (oTransport S ν hS) (oκ _ g) = oκ _ (barPair hu h2 hwF.1) := by
    rw [oTransport_kappa, heq]
  refine commute_of_congr (oTransport S ν hS) (fun R' hR'odd hR'i hR'c => ?_) hRodd hRi hRc
  rw [hcg] at hR'i hR'c
  have h1 := ClO.field_eq_one hu hℓ2 h2 hd5 hwF (hker.transport S ν hS)
    (ClO.conj_injective_of_mulEquiv (oTransport S ν hS) hinj) hR'odd hR'i hR'c
    (fun y _ => (hsurj.transport S ν hS) y)
  intro r₁ h₁ r₂ h₂
  rw [h1 r₁ h₁, h1 r₂ h₂]

theorem oddLieCoreFamilyInput_pomegaOdd : OddLieCoreFamilyInput .POmegaOdd := by
  intro S _ _ _ hna n p f hp hp2 hadm hm hL2 i hi Ro hRodd hRi hRc
  have hcl : StatedClassicalModel S .POmegaOdd n p f := by
    rcases hm with ⟨-, h⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
    · exact h
    all_goals exact absurd htag (by decide)
  have hmod := hcl
  obtain ⟨⟨hp', hf, hn, -⟩, K, _, _, hKc, ⟨e⟩⟩ := hcl
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
  · exact ClO.commute_inner_odd hK (by omega) ⟨n, rfl⟩ hR hker hsurj hinj hσ hi' hR'odd hR'i
      hR'c
  · exact ClO.commute_field hK (by omega) hp hf hKc hR hker hsurj hinj hσ hi' hR'odd hR'i hR'c

end CFSG.ComponentClassification.Foote5.OddLieCore
