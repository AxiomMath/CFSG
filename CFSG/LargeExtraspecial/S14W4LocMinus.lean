module

public import CFSG.LargeExtraspecial.S14W4LocAct
public import CFSG.LargeExtraspecial.S14W4LocNine
public import CFSG.LargeExtraspecial.O62Nine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}

theorem exists_orderOf_nine (hQ : T.Q ≤ π.ker) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 6) {q : QuadraticForm (ZMod 2) V}
    (hq : q.polarBilin.Nondegenerate) (hR : (R.subgroupOf T.M).map π = omegaGroup q hq)
    (hm : ¬ O62.IsPlus q) : ∃ x : T.Mbar, orderOf x = 9 := by
  obtain ⟨y, hyΩ, hy9⟩ := O62.exists_orderOf_eq_nine hV hq hm
  obtain ⟨r, -, rfl⟩ := Subgroup.mem_map.mp (hR.ge hyΩ)
  have hdvd : orderOf (π r) ∣ orderOf (⟨T.ρ r, ρ_mem_Mbar r⟩ : T.Mbar) := by
    rw [← πbar_ρ hQ r]
    exact orderOf_map_dvd _ _
  rw [hy9] at hdvd
  exact exists_orderOf_eq_nine_of_dvd (orderOf_pos _).ne' hdvd

end CFSG.LargeExtraspecial.S14.W4Loc
