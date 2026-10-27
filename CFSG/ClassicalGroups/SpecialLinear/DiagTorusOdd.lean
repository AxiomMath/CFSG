module

public import CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank
import all CFSG.ClassicalGroups.SpecialLinear.DiagonalTorusRank

public section

namespace CFSG

open CFSG.ClassicalGroups.SpecialLinear
open Matrix

theorem not_two_dvd_card_diagTorus {n : Nat} {F : Type} [Field F] [Finite F] [CharP F 2] :
    ¬ 2 ∣ Nat.card (diagTorus n F) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hinj : Function.Injective (diagSLHom n F) := by
    intro d e hde
    apply Subtype.ext
    funext i
    apply Units.ext
    have h := congrArg (fun g : SpecialLinearGroup (Fin n) F =>
      (g : Matrix (Fin n) (Fin n) F) i i) hde
    simpa [coe_diagSLHom] using h
  have hprod (d : Fin n → Fˣ) : (prodHom n F) d = ∏ i, d i := by
    rw [prodHom.eq_1]
    rfl
  have hdiag : diagTorus n F = (diagSLHom n F).range := by
    ext g
    rw [mem_diagTorus_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨d, hd, hg⟩
      refine ⟨⟨d, MonoidHom.mem_ker.mpr (by simpa [hprod] using hd)⟩, ?_⟩
      ext i j
      simp [coe_diagSLHom, hg]
    · rintro ⟨d, rfl⟩
      exact ⟨(d : Fin n → Fˣ), by simpa [hprod] using MonoidHom.mem_ker.mp d.2,
        coe_diagSLHom n F d⟩
  have hcard : Nat.card (diagTorus n F) = Nat.card ((prodHom n F).ker) := by
    rw [hdiag]
    exact Nat.card_congr (Equiv.ofInjective (diagSLHom n F) hinj).symm
  have hdvd : Nat.card (diagTorus n F) ∣ Nat.card (Fin n → Fˣ) := by
    rw [hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hEvenF : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card, even_iff_two_dvd]
    exact (CharP.cast_eq_zero_iff F 2 (Fintype.card F)).mp (Nat.cast_card_eq_zero F)
  have hOddUnits : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd Nat.card_pos hEvenF odd_one
  have hOddPi : Odd (Nat.card (Fin n → Fˣ)) := by
    rw [Nat.card_fun, Nat.card_fin]
    exact hOddUnits.pow
  exact (hOddPi.of_dvd_nat hdvd).not_two_dvd_nat

end CFSG

end
