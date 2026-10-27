module

public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.LieType.Multipliers.U42
public import CFSG.LieType.Multipliers.U43
public import CFSG.LieType.Multipliers.U62
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUnique
public import CFSG.Blueprint.SourceClassicalTransport
import CFSG.Models.Blueprint

public section

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier

namespace CFSG.LieType.Steinberg.CentralExt.GriessClassical

variable {X : Type} [Group X]

theorem blueprint_lieModel_psu {n p f : ℕ} (h : CFSG.Models.LieModel X .PSU n p f) :
    CFSG.Blueprint.LieModel X .PSU n p f :=
  CFSG.Models.LieModel.toBlueprint (by decide) h

theorem psu_four_two_row
    (hmodel : CFSG.Models.LieModel X .PSU 4 2 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSU 4 2 1 × exceptional .PSU 4 2 1) := by
  obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two X
    (blueprint_lieModel_psu hmodel)
  let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
  exact ⟨hX, ⟨e.trans ((MulEquiv.prodUnique.symm.trans MulEquiv.uniqueProd.symm).trans
    (toGenEx (t := .PSU) (n := 4) (p := 2) (f := 1) (a₁ := 1) (a₂ := 1) (b₁ := 2) (b₂ := 1)
      (by decide) rfl))⟩⟩

theorem psu_four_three_row
    (hmodel : CFSG.Models.LieModel X .PSU 4 3 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSU 4 3 1 × exceptional .PSU 4 3 1) := by
  obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U43.multiplier_PSU_four_three X
    (blueprint_lieModel_psu hmodel)
  exact ⟨hX, ⟨e.trans (((MulEquiv.prodMultiplicative _ _).trans
    (MulEquiv.prodCongr MulEquiv.prodUnique.symm (MulEquiv.prodMultiplicative _ _))).trans
    (toGenEx (t := .PSU) (n := 4) (p := 3) (f := 1) (a₁ := 4) (a₂ := 1) (b₁ := 3) (b₂ := 3)
      (by decide) rfl))⟩⟩

theorem psu_six_two_row
    (hmodel : CFSG.Models.LieModel X .PSU 6 2 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSU 6 2 1 × exceptional .PSU 6 2 1) := by
  obtain ⟨hX, ⟨e⟩⟩ := CFSG.LieType.Multipliers.U62.multiplier_PSU_six_two X
    (blueprint_lieModel_psu hmodel)
  exact ⟨hX, ⟨e.trans (((MulEquiv.prodMultiplicative _ _).trans
    (MulEquiv.prodCongr MulEquiv.prodUnique.symm (MulEquiv.prodMultiplicative _ _))).trans
    (toGenEx (t := .PSU) (n := 6) (p := 2) (f := 1) (a₁ := 3) (a₂ := 1) (b₁ := 2) (b₂ := 2)
      (by decide) rfl))⟩⟩

theorem psp_four_three_row
    (hmodel : CFSG.Models.LieModel X .PSp 2 3 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSp 2 3 1 × exceptional .PSp 2 3 1) := by
  obtain ⟨-, hcl | ⟨-, d, hd, -⟩⟩ := hmodel
  · have hF : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
      rw [GaloisField.card 2 2 (by norm_num)]
      norm_num
    have hYcl : StatedClassicalModel (StatedProj (StatedSU 4 (2 ^ 1) (GaloisField 2 2))) .PSU 4 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, GaloisField 2 2, inferInstance,
        inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
    obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl
      (CFSG.GH74.Exceptional.statedClassicalModel_PSp_two_three_of_PSU_four_two hYcl)
    refine of_mulEquiv e (of_mulEquiv_target ((padOne _).trans
      (toGenEx (t := .PSp) (n := 2) (p := 3) (f := 1) (a₁ := 2) (a₂ := 1) (b₁ := 1) (b₂ := 1)
        rfl (by decide))) (CFSG.LieType.Multipliers.U42.multiplier_PSU_four_two _ ?_))
    exact Or.inl ⟨by decide, hYcl⟩
  · exfalso
    cases h : d.1 <;> rw [h] at hd <;> simp [CFSG.Models.NamesTag] at hd

theorem blueprint_lieModel_psp {n p f : ℕ} (h : CFSG.Models.LieModel X .PSp n p f) :
    CFSG.Blueprint.LieModel X .PSp n p f :=
  CFSG.Models.LieModel.toBlueprint (by decide) h

theorem psp_three_two_row
    (hmodel : CFSG.Models.LieModel X .PSp 3 2 1) :
    commutator X = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃* generic .PSp 3 2 1 × exceptional .PSp 3 2 1) := by
  obtain ⟨hX, ⟨e⟩⟩ := CFSG.EvenSmallLie.SympSix.multiplier_PSp_three_two_one X
    (blueprint_lieModel_psp hmodel)
  let _ : Unique (Multiplicative (ZMod 1) × Multiplicative (ZMod 1)) := Unique.mk' _
  exact ⟨hX, ⟨e.trans ((MulEquiv.prodUnique.symm.trans MulEquiv.uniqueProd.symm).trans
    (toGenEx (t := .PSp) (n := 3) (p := 2) (f := 1) (a₁ := 1) (a₂ := 1) (b₁ := 2) (b₂ := 1)
      (by decide) rfl))⟩⟩

end CFSG.LieType.Steinberg.CentralExt.GriessClassical
