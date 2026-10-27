module

public import CFSG.GF2Type.Smith1979.W4FiveOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Five

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S5 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Lbar_le_normalizer_of_isComponentOf_w4 (hsw : ¬ Nonempty (SwapData S g))
    {Z : Subgroup S.O} (hZ : IsComponentOf Z S.Mbar) :
    S.Lbar g ≤ normalizer (Z : Set S.O) := by
  intro t ht
  refine S4.mem_normalizer_of_map_conj_eq ?_
  by_contra hne
  exact hsw ⟨⟨Z, t, hZ, ht, hne⟩⟩

theorem Mbar0_le_normalizer_of_isComponentOf_w4 (hsw : ¬ Nonempty (SwapData S g))
    {Z : Subgroup S.O} (hZ : IsComponentOf Z S.Mbar) : Mbar0 S g ≤ normalizer (Z : Set S.O) := by
  rw [Mbar0_le_normalizer_iff]
  intro h l hl
  have hhM : (S.ρ h)⁻¹ ∈ S.Mbar := S.Mbar.inv_mem ⟨h, rfl⟩
  have hl' : (S.ρ h)⁻¹ * l * S.ρ h ∈ S.Lbar g := (mem_Lbar_mul_iff S h g).mp hl
  have hN := mem_normalizer_iff.mp
    (Lbar_le_normalizer_of_isComponentOf_w4 hsw (isComponentOf_map_conj hZ hhM) hl')
  rw [mem_normalizer_iff]
  intro y
  have := hN ((S.ρ h)⁻¹ * y * S.ρ h)
  rw [mem_map_conj_iff, mem_map_conj_iff, inv_inv] at this
  have e1 : S.ρ h * ((S.ρ h)⁻¹ * y * S.ρ h) * (S.ρ h)⁻¹ = y := by group
  have e2 : S.ρ h * ((S.ρ h)⁻¹ * l * S.ρ h * ((S.ρ h)⁻¹ * y * S.ρ h) *
      ((S.ρ h)⁻¹ * l * S.ρ h)⁻¹) * (S.ρ h)⁻¹ = l * y * l⁻¹ := by group
  rwa [e1, e2] at this

theorem timmesfeld_5_2_w4_of_no_swap (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4)
    (hsw : ¬ Nonempty (SwapData S g)) :
    timmesfeldLayer S.Mbar = ⊥ ∨ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) := by
  refine timmesfeldLayer_eq_bot_or_isQuasisimple fun A B hA hB => ?_
  have hA' := isComponentOf_map_subtype hA
  have hB' := isComponentOf_map_subtype hB
  exact map_injective S.Mbar.subtype_injective (timmesfeld_5_1_w4 hCE hIrr H hNo C Q hw hA' hB'
    (Mbar0_le_normalizer_of_isComponentOf_w4 hsw hA')
    (Mbar0_le_normalizer_of_isComponentOf_w4 hsw hB'))

theorem timmesfeld_5_2_w4 (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hw : S.width = 4) :
    timmesfeldLayer S.Mbar = ⊥ ∨ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) ∨
      Nonempty (SwapData S g) := by
  by_cases hsw : Nonempty (SwapData S g)
  · exact Or.inr (Or.inr hsw)
  · rcases timmesfeld_5_2_w4_of_no_swap hCE hIrr H hNo C Q hw hsw with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end CFSG.GF2Type.Smith1979.W4Five
