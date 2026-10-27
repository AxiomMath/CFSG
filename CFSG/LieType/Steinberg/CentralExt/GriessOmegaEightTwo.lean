module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Multiplier
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem pomegaPlus_four_two_row
    {X : Type} [Group X]
    (hmodel : CFSG.Models.LieModel X .POmegaPlus 4 2 1) :
    commutator X = ⊤ ∧ Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
      generic .POmegaPlus 4 2 1 × exceptional .POmegaPlus 4 2 1) := by
  obtain ⟨-, hcl | ⟨h0, -⟩⟩ := hmodel
  · obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT (Or.inl ⟨by decide, hcl⟩)
    have := CFSG.EvenSmallLie.OmegaEight.Cover.isPerfect_omegaT
    obtain ⟨eM⟩ := CFSG.EvenSmallLie.OmegaEight.Cover.nonempty_griessHopfMultiplier_mulEquiv
    let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
    exact of_mulEquiv e ⟨Group.IsPerfect.commutator_eq_top, ⟨eM.trans
      (MulEquiv.uniqueProd.symm.trans (toGenEx (t := .POmegaPlus) (n := 4) (p := 2) (f := 1)
        (a₁ := 1) (a₂ := 1) (b₁ := 2) (b₂ := 2) (by decide) rfl))⟩⟩
  · exact absurd h0 (by norm_num)

end CFSG.LieType.Steinberg.CentralExt.GriessClassical
