module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PE8Lift

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X] {t z : G} {T : Subgroup G}
  {π : ↥(centralizer ({z} : Set G)) →* X}

theorem sec5pe8_fix (hyp : Sec5OPHyp t z T π) {L : Subgroup G} {k : G}
    (hk : k ∈ centralizer ({z} : Set G)) (hkL : k ∈ L)
    (hLA : ∀ w ∈ sec5op_Y t z, w * t = t * w → Nat.Coprime (orderOf w) 6 →
      w ∈ centralizer (L : Set G))
    (c : Sec5GBar (sec5op_Tb z T π)) (hc : Nat.Coprime (orderOf c) 6)
    (hct : c * sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ =
      sec5op_cls hyp ⟨t, sec5op_t_mem_Y t z⟩ * c) :
    sec5op_rho z T π ⟨k, hk⟩ c = c := by
  obtain ⟨y, hy, hyt, hy6, hcy⟩ := sec5pe8_lift_coprime hyp c hc hct
  have hyc : y ∈ centralizer (L : Set G) := hLA y hy hyt hy6
  have hcomm : k * y = y * k := (Subgroup.mem_centralizer_iff.mp hyc) k hkL
  rw [← hcy, sec5op_rho_cls hyp hk ⟨y, hy⟩]
  congr 1
  apply Subtype.ext
  show k * y * k⁻¹ = y
  rw [hcomm]
  group

end CFSG.OddStandard.SmallF3.Omega
