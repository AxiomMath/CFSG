module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57N
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LConfig
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDAut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDX

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.Burgoyne.O CFSG.ComponentClassification.Burgoyne.Proj
open scoped MatrixGroups

open P58b3L in
theorem harris82Lemma58bThreeRowAt_POmegaPlus_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    P58b3.Harris82Lemma58bThreeRowAt .POmegaPlus n 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ L₂ K hL₁ _ hz₁L _ _ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := P58b3.setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have hc2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₁, hz₁K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₁)
  have ht2 := P58b.orderOf_mk_eq_two (K := ↥K) (z := ⟨z₂, hz₂K⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz₂)
  have hcZ := mk_mem_center hKc.1 hz₁K
  have hcQ₁ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
      ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
  have ha := oddAutInner_of_POmegaPlus_three hX hn hmX
  have hQ₁ := P58b3.lemma57_fourGroup_map_of_aut hz₂ hL₁ hKc.1 hO₁ hN hz₂K hz₁K ha
  rcases hmX with ⟨-, hcm⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  have hcm' := hcm
  obtain ⟨-, K₀, _, _, hK₀c, ⟨e⟩⟩ := hcm'
  have hK3 : Nat.card K₀ = 3 := by rw [hK₀c, pow_one]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K₀ := Fintype.ofFinite K₀
  have : CharP K₀ 3 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hK : ringChar K₀ ≠ 2 := by rw [ringChar.eq K₀ 3]; norm_num
  have h2 : (2 : K₀) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨R, hR, hRQ⟩ := exists_gram h2 (coordinateQuadPlus n K₀)
    (regular_coordinateQuadPlus n K₀ (by omega)).1
  have hS₁ : ∀ v, oQ R (((1 : GL (Fin (2 * n)) K₀) : Matrix _ _ K₀) *ᵥ v) =
      ((1 : K₀ˣ) : K₀) * coordinateQuadPlus n K₀ v := by
    intro v
    rw [Units.val_one, one_mulVec, Units.val_one, one_mul, hRQ]
  have hker : OKer (oQ R) := OKer.transport 1 1 hS₁ (oKer_coordinatePlus hcm K₀ hK₀c e)
  exact false_of_typeD_three hO hK3 hn hR hker
    ((coordinatePlusWitnessEquiv K₀ e).trans (oTransport 1 1 hS₁)) hcZ hc2 ht2 hz₂Z hQ₁ hcQ₁

end CFSG.ComponentClassification.HarrisLit.T1
