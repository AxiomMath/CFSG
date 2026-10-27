module

public import CFSG.LieType.Steinberg.CentralExt.SpinSevenThree
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessClassical

variable {X : Type} [Group X]

theorem pomegaOdd_three_three_row
    (hmodel : CFSG.Models.LieModel X .POmegaOdd 3 3 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        generic .POmegaOdd 3 3 1 × exceptional .POmegaOdd 3 3 1) := by
  obtain ⟨-, hcl | ⟨-, d, hd, -⟩⟩ := hmodel
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcl
    refine of_mulEquiv e (of_mulEquiv_target ?_
      (SpinOddClosed.pomegaOdd_three_three_hopfMultiplier (hK.trans (by norm_num))))
    exact (MulEquiv.prodCongr MulEquiv.prodUnique.symm MulEquiv.prodUnique.symm).trans
      (toGenEx (t := .POmegaOdd) (n := 3) (p := 3) (f := 1) (a₁ := 2) (a₂ := 1) (b₁ := 3)
        (b₂ := 1) (by simp [genericOrders]) rfl)
  · exfalso
    cases h : d.1 <;> rw [h] at hd <;> simp [CFSG.Models.NamesTag] at hd

end CFSG.LieType.Steinberg.CentralExt.GriessClassical
