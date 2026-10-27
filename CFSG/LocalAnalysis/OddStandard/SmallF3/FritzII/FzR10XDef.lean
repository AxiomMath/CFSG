module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzR10XChk

public section

namespace CFSG.OddStandard.SmallF3.FritzII

variable {G : Type} [Group G] {t x1 x2 : G}

@[expose] def fzxElt (t x1 x2 : G) (v : FzXW) : G :=
  t ^ v.1.val * x1 ^ v.2.1.val * x2 ^ v.2.2.val

structure FzXBasis (t x1 x2 : G) (W : Subgroup G) : Prop where
  mem : ∀ v, fzxElt t x1 x2 v ∈ W
  surj : ∀ w ∈ W, ∃ v, fzxElt t x1 x2 v = w
  inj : Function.Injective (fzxElt t x1 x2)
  add : ∀ v v', fzxElt t x1 x2 (v + v') = fzxElt t x1 x2 v * fzxElt t x1 x2 v'

theorem fzxElt_zero : fzxElt t x1 x2 0 = 1 := by
  simp [fzxElt]

theorem fzxElt_t : fzxElt t x1 x2 (1, 0, 0) = t := by
  have h : (1 : ZMod 2).val = 1 := rfl
  simp [fzxElt, h]

theorem fzxElt_x1 : fzxElt t x1 x2 (0, 1, 0) = x1 := by
  have h : (1 : ZMod 4).val = 1 := rfl
  simp [fzxElt, h]

theorem fzxElt_x2 : fzxElt t x1 x2 (0, 0, 1) = x2 := by
  have h : (1 : ZMod 4).val = 1 := rfl
  simp [fzxElt, h]

end CFSG.OddStandard.SmallF3.FritzII
