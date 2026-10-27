module

public import CFSG.GF2Type.Smith1979W3.Reducible
public import CFSG.LargeExtraspecial.DW3CaseIISplit
public import CFSG.LargeExtraspecial.DWNormalFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.ComponentClassification
open Subgroup Module

@[expose] def DW3NoNondeg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 3 →
    NotWeaklyClosed S →
      ∀ W : Submodule (ZMod 2) S.Qt, DW.IsMbarInvariant S W → W ≠ ⊥ → W ≠ ⊤ →
        ¬ IsCompl W (DW.perp S W)

@[expose] def DW3NoTS2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 3 →
    NotWeaklyClosed S →
      ∀ W : Submodule (ZMod 2) S.Qt, DW.IsMbarInvariant S W →
        Module.finrank (ZMod 2) W = 2 → (∀ w ∈ W, S.q w = 0) → False

@[expose] def DW3CaseIINonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G), S.width = 3 →
    NotWeaklyClosed S →
      ∀ A : Subgroup G, IsElementaryAbelian 2 A → DW.MaxEA S A →
        S.M ≤ normalizer (A : Set G) → DW.IsMinimalInvariant S (S.clSub A) →
          (∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ ∈ A) →
            (∀ B : Submodule (ZMod 2) S.Qt, DW.IsMbarInvariant S B → (∀ b ∈ B, S.q b = 0) →
              ¬ IsCompl (S.clSub A) B) → False

theorem dwSplitWidthThree_of (h1 : DW3NoNondeg) (h2 : DW3NoTS2) (h6 : DW3CaseIINonsplit) :
    DWSplitWidthThree := by
  intro G _ _ _ S hw hnwc hred
  obtain ⟨W, hmin, htop, hnorm, hc | ⟨-, hq, hEA⟩⟩ :=
    DW.reduction_of_simple (S := S) (by omega : 2 ≤ S.width) hred
  · exact (h1 G S hw hnwc W hmin.2.1 hmin.1 htop hc).elim
  · have hpos : 0 < finrank (ZMod 2) W := by
      rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      exact hmin.1
    have hle : finrank (ZMod 2) W ≤ S.width :=
      DW.W4.finrank_le_width_of_ts hq
    have hcases : finrank (ZMod 2) W = 1 ∨ finrank (ZMod 2) W = 2 ∨
        finrank (ZMod 2) W = 3 := by omega
    rcases hcases with h1W | h2W | h3W
    ·
      have hcardW : Nat.card W = 2 := by
        rw [S.card_submodule, h1W]
        norm_num
      have hcard : Nat.card (S.clPre W) = 4 := by
        rw [S.card_clPre, hcardW]
      have hz : S.z ∈ S.clPre W := S.z_mem_clPre W
      have hTM : S.clPre W ≤ S.M := (S.clPre_le_QG W).trans S.QG_le_M
      exact (DW.not_normal_order_four_of_simple (S := S) (by omega : 2 ≤ S.width)
        hTM hnorm hcard hz).elim
    · exact (h2 G S hw hnwc W hmin.2.1 h2W hq).elim
    ·
      let A : Subgroup G := S.clPre W
      have hAel : IsElementaryAbelian 2 A := hEA
      have hAcard : Nat.card A = 2 ^ (S.width + 1) := by
        rw [S.card_clPre, S.card_submodule, h3W]
        change 2 * 2 ^ 3 = 2 ^ (S.width + 1)
        rw [hw]
        norm_num
      have hAmax : DW.MaxEA S A := ⟨S.clPre_le_QG W, hAcard⟩
      have hAM : S.M ≤ normalizer (A : Set G) := by
        intro m hm
        rw [mem_normalizer_iff]
        intro x
        refine ⟨fun hx => hnorm m hm x hx, fun hx => ?_⟩
        have := hnorm (m⁻¹) (S.M.inv_mem hm) (m * x * m⁻¹) hx
        rwa [show m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ = x by group] at this
      have hminA : DW.IsMinimalInvariant S (S.clSub A) := by
        simpa [A, S.clSub_clPre] using hmin
      by_cases hI : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ∉ A
      · obtain ⟨g, hxQ, hxA⟩ := hI
        exact DW.MaxEA.exists_split_of_not_mem (S := S) (A := A) hAmax hAM hxQ hxA hw
      · push Not at hI
        by_cases hsplit : ∃ B : Submodule (ZMod 2) S.Qt,
            DW.IsMbarInvariant S B ∧ (∀ b ∈ B, S.q b = 0) ∧ IsCompl (S.clSub A) B
        · obtain ⟨B, hBinv, hBq, hAB⟩ := hsplit
          obtain ⟨g, hgQ, hgne⟩ := hnwc
          exact DW.MaxEA.exists_split_of_isCompl (S := S) (A := A) hAmax hw hBinv hBq hAB
            (hI g hgQ) hgne
        · push Not at hsplit
          exact (h6 G S hw hnwc A hAel hAmax hAM hminA hI hsplit).elim

end CFSG.GF2Type.Smith1979W3
