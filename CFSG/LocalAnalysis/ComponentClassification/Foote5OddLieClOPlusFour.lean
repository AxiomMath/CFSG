module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClD4T2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOMem2
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClOEvenFam

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.O

theorem ClO.commute_pomegaPlus_four (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : LieModel S .POmegaPlus 4 p f) (i : MulAut S) (hi : orderOf i = 2)
    (Ro : Subgroup (MulAut S)) (hRodd : Odd (Nat.card Ro)) (hRi : ∀ r ∈ Ro, r * i = i * r)
    (hRc : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ Ro,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ Ro) :
    ∀ r₁ ∈ Ro, ∀ r₂ ∈ Ro, r₁ * r₂ = r₂ * r₁ := by
  have hcl : StatedClassicalModel S .POmegaPlus 4 p f := by
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
  set θ₀ := coordinatePlusWitnessEquiv K e with hθ₀
  have hZ := center_eq_bot_of_simple hna
  have hi₀ : MulAut.congr θ₀ i * MulAut.congr θ₀ i = 1 := by
    have hpi := pow_orderOf_eq_one i
    rw [hi, pow_two] at hpi
    rw [← map_mul, hpi, map_one]
  obtain ⟨β, hβ⟩ :=
    (CatalogueBOrthogonalInvolutionConjugacy.plus_four_conjugacy (K := K)).1 _ hi₀
  set α := β⁻¹ with hα
  have hαt : α * MulAut.congr θ₀ i * α⁻¹ ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K) := by
    rwa [hα, inv_inv]
  have hfam := coordinate_plus_family_eq_matrixImage hmod K hKc e
  have hsemi : ∀ γ ∈ projectivePointFamilyAut (coordinateQuadPlus 4 K),
      ∃ g : similarityPairs (coordinateQuadPlus 4 K), γ = oκ _ g := by
    intro γ hγ
    rw [hfam] at hγ
    obtain ⟨g, hg⟩ := hγ
    exact ⟨g, hg.symm⟩
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus 4 K)
    (regular_coordinateQuadPlus 4 K (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * 4)) K) : Matrix _ _ K) *ᵥ v) =
      ((1 : Kˣ) : K) * coordinateQuadPlus 4 K v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker := hker₀.transport 1 1 hS₁
  have hinj : Function.Injective (MulAut.conj : StatedProj (matrixDerived (oQ R)) →*
      MulAut (StatedProj (matrixDerived (oQ R)))) :=
    ClO.conj_injective_of_mulEquiv ((θ₀.trans α).trans (oTransport 1 1 hS₁)) (conj_injective hZ)
  refine commute_of_congr (θ₀.trans α) (fun R₁ hR₁odd hR₁i hR₁c => ?_) hRodd hRi hRc
  have ht : MulAut.congr (θ₀.trans α) i = α * MulAut.congr θ₀ i * α⁻¹ := by
    ext x
    rfl
  rw [ht] at hR₁i hR₁c
  have hto : orderOf (α * MulAut.congr θ₀ i * α⁻¹) = 2 := by
    rw [← ht, MulEquiv.orderOf_eq]
    exact hi
  have hR₁F := ClO.d4_preserves K hK _ hto hαt R₁ hR₁odd hR₁i hR₁c
  obtain ⟨g₁, hg₁⟩ := hsemi _ hαt
  rw [hg₁] at hR₁i hR₁c hto
  refine ClO.commute_of_transport_mem 1 1 hS₁ hR₁odd hR₁i hR₁c (fun y hy => hsemi y (hR₁F hy))
    (fun R' hR'odd hR'i hR'c hR's => ?_)
  have hi' : orderOf (oκ _ (transPair 1 1 hS₁ g₁)) = 2 := by
    rw [← oTransport_kappa, MulEquiv.orderOf_eq]
    exact hto
  by_cases hσ : (transPair 1 1 hS₁ g₁).val.right = 1
  · exact ClO.commute_inner_even_mem hK hp hKc le_rfl hR hker hinj hσ hi' hR'odd hR'i hR'c hR's
  · exact ClO.commute_field_mem hK (by omega) hp hf hKc hR hker hinj hσ hi' hR'odd hR'i hR'c hR's

theorem oddLieCoreFamilyInput_pomegaPlus : OddLieCoreFamilyInput .POmegaPlus := by
  intro S _ _ _ hna n p f hp hp2 hadm hm hL2 i hi Ro hRodd hRi hRc
  have hn : 4 ≤ n := hadm.2.2
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · obtain rfl : n = 4 := by omega
    exact ClO.commute_pomegaPlus_four S hna hp hp2 hm i hi Ro hRodd hRi hRc
  · exact ClO.commute_pomegaPlus_five S hna hp hp2 h5 hm i hi Ro hRodd hRi hRc

end CFSG.ComponentClassification.Foote5.OddLieCore
