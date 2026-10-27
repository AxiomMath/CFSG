module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAutModel

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] (h : UnitaryFieldData 2 1 F)

theorem sixProj_eq_one_iff (g : sixS h) :
    sixProj h g = 1 ↔
      ∃ c : Fˣ, (g : GL (Fin 6) F) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  rw [sixProj_apply, QuotientGroup.eq_one_iff, mem_sixScalars_iff]

theorem sixProj_ne_one_of_apply {g : sixS h} {a b : Fin 6} (hab : a ≠ b)
    (hg : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) a b ≠ 0) : sixProj h g ≠ 1 := by
  rw [Ne, sixProj_eq_one_iff]
  rintro ⟨c, hc⟩
  apply hg
  rw [hc, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ hab]

theorem nMat_apply_inl_inr (B : Matrix (Fin 3) (Fin 3) F) (i j : Fin 3) :
    nMat B (sixEquiv (Sum.inl i)) (sixEquiv (Sum.inr j)) = B i j := by
  simp [nMat, reindex_apply]

theorem omega_ne_zero {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ≠ 0 := by
  rintro rfl
  simp at hω

include h in
theorem omega_pow_three {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 :=
  pow_three_eq_one h (omega_ne_zero hω)

end CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoAut
