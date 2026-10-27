module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.TypUVert
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem typU_of_vertical_in (hI : Phase1Inputs) {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : SectionRank.IsKGroupCat ↥H) {M T : Subgroup G} {x w : G}
    (hMH : M ≤ H) (hM : IsPComponent 2 (M.subgroupOf H)) (hx : orderOf x = 2) (hxH : x ∈ H)
    (hxM : x ∈ normalizer (M : Set G)) (hTM : T ≤ M)
    (hT : HarrisLit.IsTwoComponentIn T (H ⊓ centralizer ({x} : Set G))) (hTU : TypU ↥T)
    (hw : orderOf w = 2) (hwT : w ∈ T) (hwZ : w ∈ (Open.fusionZStar ↥M).map M.subtype) :
    TypU ↥M := by
  have hTH : T ≤ H := hT.1.trans inf_le_left
  have hwM : w ∈ M := hTM hwT
  have hwH : w ∈ H := hMH hwM
  have hT₁ : HarrisLit.IsTwoComponentIn (T.subgroupOf H)
      (centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H)) :=
    HarrisLit.T1.isTwoComponentIn_subgroupOf_inf hxH hT
  have hT₁pc : IsPComponent 2
      ((T.subgroupOf H).subgroupOf (centralizer ({(⟨x, hxH⟩ : ↥H)} : Set ↥H))) :=
    (HarrisLit.isTwoComponentIn_iff hT₁.1).mp hT₁
  have hTU₁ : TypU ↥(T.subgroupOf H) :=
    coreInvariant_typU ↥T ↥(T.subgroupOf H)
      ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hTH).symm
        (CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hTH).symm)⟩ hTU
  have hxN : (⟨x, hxH⟩ : ↥H) ∈
      normalizer ((M.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hcoe : ((⟨x, hxH⟩ * y * ⟨x, hxH⟩⁻¹ : ↥H) : G) = x * (y : G) * x⁻¹ := by simp
    rw [hcoe]
    exact Subgroup.mem_normalizer_iff.mp hxM (y : G)
  have hw₁Z : (⟨w, hwH⟩ : ↥H) ∈
      (Open.fusionZStar ↥(M.subgroupOf H)).map (M.subgroupOf H).subtype := by
    have hwZM : (⟨w, hwM⟩ : ↥M) ∈ Open.fusionZStar ↥M := by
      obtain ⟨m, hm, hmw⟩ := hwZ
      have hm' : m = ⟨w, hwM⟩ := Subtype.ext hmw
      rwa [← hm']
    let eM : ↥(M.subgroupOf H) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMH
    have hsame : eM (⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwM⟩ : ↥(M.subgroupOf H)) =
        (⟨w, hwM⟩ : ↥M) := by
      apply Subtype.ext
      rfl
    have hway : eM (⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwM⟩ : ↥(M.subgroupOf H)) ∈
        (Open.fusionZStar ↥(M.subgroupOf H)).map eM.toMonoidHom := by
      rw [FooteLit.fusionZStar_map_mulEquiv eM, hsame]
      exact hwZM
    have hwZM₁ : (⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwM⟩ : ↥(M.subgroupOf H)) ∈
        Open.fusionZStar ↥(M.subgroupOf H) :=
      (Subgroup.mem_map_iff_mem (f := eM.toMonoidHom) eM.injective).mp hway
    exact Subgroup.mem_map.mpr
      ⟨⟨⟨w, hwH⟩, Subgroup.mem_subgroupOf.mpr hwM⟩, hwZM₁, rfl⟩
  have hres : TypU ↥(M.subgroupOf H) :=
    (verticalCentral_typU hI) ↥H hH (M.subgroupOf H) hM
      (⟨x, hxH⟩ : ↥H) (by rw [Subgroup.orderOf_mk]; exact hx) hxN
      (T.subgroupOf H) (Subgroup.subgroupOf_mono H hTM) hT₁.1 hT₁pc hTU₁
      (⟨w, hwH⟩ : ↥H) (by rw [Subgroup.orderOf_mk]; exact hw)
      (Subgroup.mem_subgroupOf.mpr hwT) hw₁Z
  exact coreInvariant_typU ↥(M.subgroupOf H) ↥M
    ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hMH)
      (CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hMH))⟩ hres

end CFSG.OddStandard.SmallF3.HypA2
