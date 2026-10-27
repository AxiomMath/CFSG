module

public import CFSG.ClassicalInvolution.WeakCT.SpModel
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
public import CFSG.ClassicalInvolution.WeakCT.StandardPair

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Timmesfeld.LevisExtras
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair longBlock
  shortBlock longBlock_eq_of_eq_x shortBlock_eq_of_eq_x)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

section Blocks

variable {F : Type} [Field F]

theorem spBlock_one_eq_longBlock : spBlock F 1 = longBlock F 2 1 :=
  longBlock_eq_of_eq_x (k := 1) (by decide) _
    (fun c => by rw [← tv01_eq_sl2Upper]; exact spBlock_upper 1 c)
    (fun c => by rw [← tv10_eq_sl2Lower]; exact spBlock_lower 1 c)

theorem spBlock_zero_eq_shortBlock : spBlock F 0 = shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1) :=
  shortBlock_eq_of_eq_x (k := 0) (by decide) _
    (fun c => by rw [← tv01_eq_sl2Upper]; exact spBlock_upper 0 c)
    (fun c => by rw [← tv10_eq_sl2Lower]; exact spBlock_lower 0 c)

end Blocks

section Normalize

variable {F : Type} [Field F] {X : Type} [Group X]

theorem pair_normalize_sp {W U V : Subgroup X} (h : SymplecticBlockStandardPair F W U V) :
    ∃ θ : StatedSp 2 F →* X, θ.range = W ∧ θ.ker ≤ Subgroup.center (StatedSp 2 F) ∧
      Function.Injective (θ.comp (spBlock F 1)) ∧ Function.Injective (θ.comp (spBlock F 0)) ∧
      (θ.comp (spBlock F 1)).range = U ∧ (θ.comp (spBlock F 0)).range = V := by
  obtain ⟨θ, c, hrange, hker, hinj1, hinj0, hU, hV⟩ := h
  rw [← spBlock_one_eq_longBlock] at hinj1 hU
  rw [← spBlock_zero_eq_shortBlock] at hinj0 hV
  refine ⟨θ.comp (MulAut.conj c⁻¹).toMonoidHom, ?_, ker_comp_mulEquiv_le_center hker _, hinj1,
    hinj0, ?_, ?_⟩
  · rw [range_comp_mulEquiv, hrange]
  · rw [MonoidHom.range_comp, ← Subgroup.map_map]
    exact hU
  · rw [MonoidHom.range_comp, ← Subgroup.map_map]
    exact hV

end Normalize

end CFSG.ClassicalInvolution.WeakCT
