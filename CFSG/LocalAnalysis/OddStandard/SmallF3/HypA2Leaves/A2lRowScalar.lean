module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open Matrix
open CFSG.Open (StatedScalars)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem a2l_scalar_of_mk_eq_one {x : H}
    (hx : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x = 1) :
    ∃ c : K, ((x : GL ι K) : Matrix ι ι K) = Matrix.scalar ι c := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
    MonoidHom.mem_range] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, by rw [← hc, GeneralLinearGroup.coe_scalar]⟩

theorem a2l_eq_one_of_mk_eq_one {x : H}
    (hx : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x = 1) {a : ι}
    (ha : ((x : GL ι K) : Matrix ι ι K) a a = 1) : x = 1 := by
  obtain ⟨c, hc⟩ := a2l_scalar_of_mk_eq_one hx
  rw [hc, Matrix.scalar_apply, diagonal_apply_eq] at ha
  apply Subtype.ext
  apply Units.ext
  rw [hc, ha]
  change Matrix.scalar ι (1 : K) = 1
  exact map_one _

theorem a2l_two_eq_zero_of_mk_eq_one {x : H}
    (hx : QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H) x = 1) {a b : ι}
    (ha : ((x : GL ι K) : Matrix ι ι K) a a = -1) (hb : ((x : GL ι K) : Matrix ι ι K) b b = 1) :
    (2 : K) = 0 := by
  obtain ⟨c, hc⟩ := a2l_scalar_of_mk_eq_one hx
  rw [hc, Matrix.scalar_apply, diagonal_apply_eq] at ha hb
  linear_combination ha - hb

end CFSG.OddStandard.SmallF3.HypA2Leaves
