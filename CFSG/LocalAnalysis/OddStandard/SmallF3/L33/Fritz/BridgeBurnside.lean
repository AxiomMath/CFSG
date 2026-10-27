module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.OddStandard.SmallF3.L33

theorem exists_normal_odd_complement {C : Type} [Group C] [Finite C]
    (heven : Even (Nat.card C)) (hcyc : ∀ S : Sylow 2 C, IsCyclic (S : Subgroup C)) :
    ∃ N : Subgroup C, N.Normal ∧ Odd (Nat.card N) ∧ ∀ c : C, Odd (orderOf c) → c ∈ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card C).minFac = 2 :=
    (Nat.minFac_eq_two_iff (Nat.card C)).mpr (even_iff_two_dvd.mp heven)
  let S : Sylow 2 C := default
  have hS : IsCyclic (S : Subgroup C) := hcyc S
  have hn : Subgroup.normalizer (S : Set C) ≤ Subgroup.centralizer (S : Set C) :=
    IsCyclic.normalizer_le_centralizer (P := S) hmin hS
  let τ : C →* S := MonoidHom.transferSylow S hn
  refine ⟨τ.ker, τ.normal_ker, ?_, ?_⟩
  · refine Nat.not_even_iff_odd.mp fun hE => ?_
    exact MonoidHom.not_dvd_card_ker_transferSylow S hn (even_iff_two_dvd.mp hE)
  · intro c hc
    have hcop : (orderOf (τ c)).Coprime (orderOf c) :=
      S.isPGroup'.orderOf_coprime (Nat.coprime_two_left.mpr hc) (τ c)
    have h1 : orderOf (τ c) = 1 :=
      Nat.Coprime.eq_one_of_dvd hcop (orderOf_map_dvd τ c)
    exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1)

end CFSG.OddStandard.SmallF3.L33
