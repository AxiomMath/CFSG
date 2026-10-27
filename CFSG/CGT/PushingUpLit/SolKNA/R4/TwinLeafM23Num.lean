module

public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open Subgroup

theorem m23_perfect_card_dvd_42_subsingleton {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (h : Nat.card H ∣ 42) : Subsingleton H := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 7 H))
  haveI : Finite (Sylow 7 H) := Sylow.finite_of_finiteIndex P
  have hn : Nat.card (Sylow 7 H) ∣ 42 :=
    (Sylow.card_dvd_index P).trans ((Subgroup.index_dvd_card _).trans h)
  have hn1 : Nat.card (Sylow 7 H) = 1 := by
    have hmod := card_sylow_modEq_one 7 H
    unfold Nat.ModEq at hmod
    have hle : Nat.card (Sylow 7 H) ≤ 42 := Nat.le_of_dvd (by norm_num) hn
    generalize Nat.card (Sylow 7 H) = k at hn hmod hle ⊢
    interval_cases k <;> omega
  haveI : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.1 hn1).1
  haveI : P.toSubgroup.Normal := Sylow.normal_of_subsingleton P
  haveI : Group.IsNilpotent P.toSubgroup := IsPGroup.isNilpotent P.isPGroup'
  have hidx : P.toSubgroup.index ∣ 42 := (Subgroup.index_dvd_card _).trans h
  have hidx7 : ¬ 7 ∣ P.toSubgroup.index := Sylow.not_dvd_index P
  have hcop : Nat.Coprime P.toSubgroup.index 7 :=
    (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hidx7)
  have h6 : P.toSubgroup.index ∣ 6 :=
    Nat.Coprime.dvd_of_dvd_mul_right hcop (by simpa using hidx)
  have hquot : Group.IsSolvable (H ⧸ P.toSubgroup) := by
    apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
    rw [← Subgroup.index_eq_card]
    have hsub : P.toSubgroup.index.primeFactors ⊆ (6 : ℕ).primeFactors :=
      Nat.primeFactors_mono h6 (by norm_num)
    have h6card : ((6 : ℕ).primeFactors).card ≤ 2 := by
      have : (6 : ℕ).primeFactors = {2, 3} := by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
          Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors (by norm_num)]
        rfl
      rw [this]
      exact Finset.card_le_two
    exact (Finset.card_le_card hsub).trans h6card
  have hsolv : Group.IsSolvable H := Group.isSolvable_of_subgroup_quotient P.toSubgroup
  by_contra hnot
  haveI : Nontrivial H := not_subsingleton_iff_nontrivial.1 hnot
  exact Group.IsPerfect.not_isSolvable H hsolv

theorem m23_perfect_core {G : Type} [Group G] [Finite G] [Group.IsPerfect G]
    (hcard : Nat.card G = 2688) (D O : Subgroup G) [D.Normal] [O.Normal]
    (hD64 : 64 ∣ Nat.card D) (hOodd : Odd (Nat.card O))
    (hDO : ∀ g ∈ D, ∃ k : ℕ, g ^ 2 ^ k ∈ O) : False := by
  have hidx : D.index ∣ 42 := by
    have h1 : D.index * 64 ∣ 42 * 64 := by
      rw [show (42 : ℕ) * 64 = 2688 by norm_num, ← hcard, ← Subgroup.index_mul_card]
      exact Nat.mul_dvd_mul_left _ hD64
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
  have hDtop : D = ⊤ := by
    have hsub : Subsingleton (G ⧸ D) :=
      m23_perfect_card_dvd_42_subsingleton (by rw [← Subgroup.index_eq_card]; exact hidx)
    exact QuotientGroup.subgroup_eq_top_of_subsingleton D hsub
  have h2 : IsPGroup 2 (G ⧸ O) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hDO g (by rw [hDtop]; exact Subgroup.mem_top g)
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent (G ⧸ O) := IsPGroup.isNilpotent h2
  have hsub : Subsingleton (G ⧸ O) := by
    by_contra hnot
    haveI : Nontrivial (G ⧸ O) := not_subsingleton_iff_nontrivial.1 hnot
    exact Group.IsPerfect.not_isSolvable (G ⧸ O) inferInstance
  have hOtop : O = ⊤ := QuotientGroup.subgroup_eq_top_of_subsingleton O hsub
  rw [hOtop, Subgroup.card_top, hcard] at hOodd
  exact absurd hOodd (by decide)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
