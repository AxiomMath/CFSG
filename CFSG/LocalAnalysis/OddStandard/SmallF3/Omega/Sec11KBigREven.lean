module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11KBigC
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cA
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaGroup

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem s900_oTwoRes_even [Finite G] {X P : Subgroup G} (hP : IsSylow2Of P X)
    (hXP : oddCoreIn X ⊔ P ≠ X) : 2 ∣ Nat.card (oTwoRes X) := by
  by_contra h2
  have hodd : Odd (Nat.card (oTwoRes X)) :=
    Nat.not_even_iff_odd.mp fun he => h2 (even_iff_two_dvd.mp he)
  have hle : oTwoRes X ≤ oddCoreIn X :=
    sec11KB_le_oddCore (sec11c_oTwoRes_le X)
      (fun x hx y hy =>
        sec11c_conj_mem_oTwoRes (fun z hz => X.mul_mem (X.mul_mem hx hz) (X.inv_mem hx)) hy)
      hodd
  have hq : IsPGroup 2 (↥X ⧸ CFSG.oddCore ↥X) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨a, m, hm, hx⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨a, ?_⟩
    have hdvd : 2 ^ a ∣ orderOf x := ⟨m, hx⟩
    have horder : orderOf (x ^ 2 ^ a) = m := by
      rw [orderOf_pow_of_dvd (pow_pos (by norm_num) a).ne' hdvd, hx,
        Nat.mul_div_cancel_left m (pow_pos (by norm_num) a)]
    have hmemX : ((x ^ 2 ^ a : ↥X) : G) ∈ oTwoRes X :=
      sec11c_mem_oTwoRes (x ^ 2 ^ a).2 (by rw [Subgroup.orderOf_coe, horder]; exact hm)
    have hmemO : ((x ^ 2 ^ a : ↥X) : G) ∈ (CFSG.oddCore ↥X).map X.subtype := hle hmemX
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hmemO
    have hy_eq : y = x ^ 2 ^ a := X.subtype_injective hyx
    rw [hy_eq] at hy
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hy
  obtain ⟨S, hS⟩ := hP.exists_sylow
  have hsup : (S : Subgroup ↥X) ⊔ CFSG.oddCore ↥X = ⊤ :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta.sylow_sup_normal_eq_top
      (CFSG.oddCore ↥X) hq S
  have hmap : P ⊔ oddCoreIn X = X := by
    have h := congrArg (Subgroup.map X.subtype) hsup
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype, hS] at h
    exact h
  exact hXP (by rw [sup_comm]; exact hmap)

end CFSG.OddStandard.SmallF3.Omega
