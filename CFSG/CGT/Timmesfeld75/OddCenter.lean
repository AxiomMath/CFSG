module

public import CFSG.CGT.Timmesfeld75.SolvableCentral
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

theorem odd_card_center {K : Type*} [Group K] [Finite K]
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    Odd (Nat.card (Subgroup.center K)) := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center K) := even_iff_two_dvd.1 hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 2 h2
  have hz' : orderOf (z : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
  have hle : Subgroup.zpowers (z : K) ≤ Subgroup.center K := by
    rw [Subgroup.zpowers_le]; exact z.2
  have hn := Subgroup.normal_of_le_center hle
  have hp : IsPGroup 2 (Subgroup.zpowers (z : K)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz']; norm_num)
  have h1 := hO2 _ hn hp
  have : (z : K) ∈ Subgroup.zpowers (z : K) := Subgroup.mem_zpowers _
  rw [h1, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hz'
  exact absurd hz' (by norm_num)

theorem solvable_radical_bot_quotient {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsWC T) (h4 : 4 ≤ Nat.card T) (hK : Subgroup.normalClosure (T : Set K) = ⊤)
    (hO2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∀ R : Subgroup (K ⧸ Subgroup.center K), R.Normal → Group.IsSolvable R → R = ⊥ := by
  refine solvable_normal_bot_of_pSubgroups_central fun p hp P hPn hPp n hn => ?_
  by_cases hp2 : p = 2
  · subst hp2
    have := hO2 P hPn hPp
    rw [this, Subgroup.mem_bot] at hn
    rw [hn]
    exact Subgroup.one_mem _
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := hPp.exists_card_eq
    have hodd : Odd (Nat.card P) := by
      rw [hm]
      exact (hp.odd_of_ne_two hp2).pow
    have hPK : P ≤ Subgroup.normalClosure (T : Set K) := by rw [hK]; exact le_top
    have hNn : ∀ k ∈ Subgroup.normalClosure (T : Set K), ∀ n ∈ P, k * n * k⁻¹ ∈ P :=
      fun k _ n hn => hPn.conj_mem n hn k
    refine Subgroup.mem_center_iff.2 fun k => ?_
    have hkK : k ∈ Subgroup.normalClosure (T : Set K) := by rw [hK]; trivial
    exact (oddCore_le_center hT h4 P hPK hNn hodd n hn k hkK).symm

end CFSG.CGT.Timmesfeld75
