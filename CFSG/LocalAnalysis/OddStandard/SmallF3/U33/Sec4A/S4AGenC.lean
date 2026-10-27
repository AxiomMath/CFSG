module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isPGroup_of_odd_relIndex {H S Q : Subgroup G} (hSQ : S ≤ Q) (hQH : Q ≤ H)
    (hQ : IsPGroup 2 Q) (hS : ¬ 2 ∣ S.relIndex H) : Q = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmul : S.relIndex Q * Q.relIndex H = S.relIndex H :=
    Subgroup.relIndex_mul_relIndex S Q H hSQ hQH
  have hdvd : S.relIndex Q ∣ S.relIndex H := ⟨Q.relIndex H, hmul.symm⟩
  have hQ' : IsPGroup 2 ↥Q := hQ
  obtain ⟨n, hn⟩ := hQ'.index (S.subgroupOf Q)
  have hn0 : n = 0 := by
    by_contra hne
    apply hS
    have h2 : 2 ∣ S.relIndex Q := by
      rw [Subgroup.relIndex, hn]
      exact dvd_pow_self 2 hne
    exact h2.trans hdvd
  have hidx : (S.subgroupOf Q).index = 1 := by rw [hn, hn0, pow_zero]
  have htop : S.subgroupOf Q = ⊤ := Subgroup.index_eq_one.mp hidx
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hSQ

theorem not_two_dvd_relIndex_map_conj {H S : Subgroup G} (g : G) (hS : ¬ 2 ∣ S.relIndex H) :
    ¬ 2 ∣ (S.map (MulAut.conj g).toMonoidHom).relIndex (H.map (MulAut.conj g).toMonoidHom) := by
  rw [Subgroup.relIndex_map_map_of_injective S H (MulAut.conj g).injective]
  exact hS

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
