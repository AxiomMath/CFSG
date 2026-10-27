module

public import CFSG.LargeExtraspecial.S5OneE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Mbar0_le_normalizer_iff {X : Subgroup S.O} :
    Mbar0 S g ≤ normalizer (X : Set S.O) ↔
      ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X : Set S.O) :=
  iSup_le_iff

theorem timmesfeld_5_1 (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    {X₁ X₂ : Subgroup S.O} (h₁ : IsComponentOf X₁ S.Mbar) (h₂ : IsComponentOf X₂ S.Mbar)
    (hN₁ : Mbar0 S g ≤ normalizer (X₁ : Set S.O))
    (hN₂ : Mbar0 S g ≤ normalizer (X₂ : Set S.O)) : X₁ = X₂ := by
  rw [Mbar0_le_normalizer_iff] at hN₁ hN₂
  by_contra hne
  obtain ⟨⟨t, ht⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Lbar_inf_ne_bot hIrr H C h₁ hN₁)
  obtain ⟨⟨τ, hτ⟩, hτ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Lbar_inf_ne_bot hIrr H C h₂ hN₂)
  exact PairData.false ⟨X₁, X₂, t, τ, h₁, h₂, hN₁, hN₂, hne, (mem_inf.mp ht).1,
    (mem_inf.mp ht).2, fun h => ht1 (Subtype.ext h), (mem_inf.mp hτ).1, (mem_inf.mp hτ).2,
    fun h => hτ1 (Subtype.ext h)⟩ hCE hIrr H hNo C Q hn

theorem Lbar_le_normalizer_of_isComponentOf (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (Q : Hyp45Q H C) (hn : 4 < S.width) {Z : Subgroup S.O} (hZ : IsComponentOf Z S.Mbar) :
    S.Lbar g ≤ normalizer (Z : Set S.O) := by
  intro t ht
  refine S4.mem_normalizer_of_map_conj_eq ?_
  by_contra hne
  exact SwapData.false ⟨Z, t, hZ, ht, hne⟩ H hNo C Q hn

theorem Mbar0_le_normalizer_of_isComponentOf (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width) {Z : Subgroup S.O}
    (hZ : IsComponentOf Z S.Mbar) : Mbar0 S g ≤ normalizer (Z : Set S.O) := by
  rw [Mbar0_le_normalizer_iff]
  intro h l hl
  have hhM : (S.ρ h)⁻¹ ∈ S.Mbar := S.Mbar.inv_mem ⟨h, rfl⟩
  have hl' : (S.ρ h)⁻¹ * l * S.ρ h ∈ S.Lbar g := (mem_Lbar_mul_iff S h g).mp hl
  have hN := mem_normalizer_iff.mp
    (Lbar_le_normalizer_of_isComponentOf H hNo C Q hn (isComponentOf_map_conj hZ hhM) hl')
  rw [mem_normalizer_iff]
  intro y
  have := hN ((S.ρ h)⁻¹ * y * S.ρ h)
  rw [mem_map_conj_iff, mem_map_conj_iff, inv_inv] at this
  have e1 : S.ρ h * ((S.ρ h)⁻¹ * y * S.ρ h) * (S.ρ h)⁻¹ = y := by group
  have e2 : S.ρ h * ((S.ρ h)⁻¹ * l * S.ρ h * ((S.ρ h)⁻¹ * y * S.ρ h) *
      ((S.ρ h)⁻¹ * l * S.ρ h)⁻¹) * (S.ρ h)⁻¹ = l * y * l⁻¹ := by group
  rwa [e1, e2] at this

theorem isComponentOf_map_subtype {A : Subgroup S.Mbar} (hA : IsComponentOf A ⊤) :
    IsComponentOf (A.map S.Mbar.subtype) S.Mbar := by
  refine (isComponentOf_iff_subgroupOf (map_subtype_le A)).mpr ?_
  have e : (A.map S.Mbar.subtype).subgroupOf S.Mbar = A :=
    comap_map_eq_self_of_injective S.Mbar.subtype_injective A
  rw [e]
  exact hA

theorem timmesfeld_5_2 (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width) :
    timmesfeldLayer S.Mbar = ⊥ ∨ CFSG.Open.IsQuasisimple (timmesfeldLayer S.Mbar) := by
  refine timmesfeldLayer_eq_bot_or_isQuasisimple fun A B hA hB => ?_
  have hA' := isComponentOf_map_subtype hA
  have hB' := isComponentOf_map_subtype hB
  exact map_injective S.Mbar.subtype_injective (timmesfeld_5_1 hCE hIrr H hNo C Q hn hA' hB'
    (Mbar0_le_normalizer_of_isComponentOf H hNo C Q hn hA')
    (Mbar0_le_normalizer_of_isComponentOf H hNo C Q hn hB'))

end CFSG.LargeExtraspecial.S5
