module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BSwC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FTwoPart

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43 Subgroup

theorem sw_core {Λ : Type} [Group Λ] [Finite Λ] {τ : Λ →* X₀} (hτ : SwCentralTwo τ)
    (hone : X0OneClass) (hx : orderOf xElt = 2) (hF : SwFinite) (hO : SwOddCent)
    {A₁ A₂ : Subgroup Λ} {z : Λ} (S : SwSetup A₁ A₂ z) :
    ∃ c ∈ centralizer ({z} : Set Λ), CFSG.conjugate A₁ c = A₂ := by
  classical
  have hz1 : τ z ≠ 1 := sw_core_tau_ne_one hτ S
  obtain ⟨x, o, hx', ho', hzxo, ⟨n, hn⟩, hodd⟩ := sec4F_two_part z
  have ho_eq : o = 1 := by
    by_contra ho1
    exact sw_core_noninvol hτ hone hx hO S ho' hodd ho1
  have hzx : z * z = 1 := by
    apply S.sq_of_two_power (Subgroup.mem_zpowers z) (n := n)
    rw [hzxo, ho_eq, mul_one]
    exact hn
  have hz_ne : z ≠ 1 := fun h => hz1 (by rw [h, map_one])
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime
    · rwa [pow_two]
    · exact hz_ne
  exact sw_core_invol hτ hone hx hF S hz2 hz1

end CFSG.OddStandard.SmallF3.Omega
