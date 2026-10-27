module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42OddExcDiv
public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem gomi_quadField_false
    {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = (p ^ e) ^ 2)
    (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup τ F)}
    {g : adjointGroup τ F} {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) = (g : ModGL τ F) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ F) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1)
    (hdvd : Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ∣ 51840) :
    False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hF, ← pow_mul, mul_comm])
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hF δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))).map
      (adjointGroup τ F).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ F) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ F) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ≃*
      ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  have hcard : Nat.card ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) =
      Nat.card ↥(entrywiseFixedGroup τ δ) := Nat.card_congr (e₁.trans e₂).toEquiv
  obtain ⟨-, hinj, -, hJΓ, -, -, -, -⟩ := Chevalley_coordinate_field_fixed_structure τ F hF2 δ
  have h1 : Nat.card ↥(fixedFieldImage τ δ) ∣ Nat.card ↥(entrywiseFixedGroup τ δ) :=
    Subgroup.card_dvd_of_le hJΓ
  have h2 : Nat.card ↥(fixedFieldImage τ δ) = Nat.card ↥(adjointGroup τ (fixSubfield δ)) :=
    Subgroup.card_map_of_injective hinj
  have h3 := gomi_adjointGroup_pow_five_dvd (F := fixSubfield δ) hτ
  rw [← h2] at h3
  have h4 : Nat.card ↥(fixSubfield δ) ^ 5 ∣ 51840 := by
    refine h3.trans (h1.trans ?_)
    rw [← hcard]
    exact hdvd
  have hk2 : ringChar (fixSubfield δ) ≠ 2 := ringChar_fixSubfield_ne_two hF2 δ
  have : Fintype ↥(fixSubfield δ) := Fintype.ofFinite _
  have hkodd : Odd (Nat.card ↥(fixSubfield δ)) := by
    rw [← Nat.not_even_iff_odd, Nat.card_eq_fintype_card]
    exact fun h => hk2 (FiniteField.even_card_iff_char_two.2 (Nat.even_iff.1 h))
  exact gomi_not_pow_five_dvd hkodd Finite.one_lt_card h4

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
