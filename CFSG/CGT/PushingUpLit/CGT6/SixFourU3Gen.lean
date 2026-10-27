module

public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.Timmesfeld75.L2Pair

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped MatrixGroups

section L2Gen

open CFSG.CGT.Timmesfeld75

theorem card_sl2_two_pow {M : Type*} [Group M] {n : ℕ} (hn : n ≠ 0)
    (e : M ≃* SL(2, GaloisField 2 n)) : Nat.card M = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_congr e.toEquiv, card_SL2_eq, GaloisField.card 2 n hn]

theorem l2_gen_facts {Γ : Type} [Group Γ] {J Y₀ : Subgroup Γ} {n : ℕ} (hn : 2 ≤ n) (hJY : J ≤ Y₀)
    (hJ : Nat.card J = 2 ^ n) (e : Y₀ ≃* SL(2, GaloisField 2 n)) :
    ∃ g ∈ Y₀, J ⊔ J.map (MulAut.conj g).toMonoidHom = Y₀ := by
  classical
  have hn0 : n ≠ 0 := by omega
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = 2 ^ n := ⟨_, rfl⟩
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hqeven : 2 ∣ q := by
    rw [hq]
    exact dvd_pow_self 2 hn0
  have hq2 : 4 * q ≤ q ^ 2 := by nlinarith
  have hY : Nat.card Y₀ = q * (q ^ 2 - 1) := by rw [hq]; exact card_sl2_two_pow hn0 e
  have hfin : Finite Y₀ := Nat.finite_of_card_ne_zero (by
    rw [hY]
    have : 0 < q := by omega
    have : 0 < q ^ 2 - 1 := by omega
    positivity)
  set S : Subgroup Y₀ := J.subgroupOf Y₀ with hS
  have hScard : Nat.card S = q := by
    rw [hS, hq, ← hJ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJY).toEquiv
  have hSp : IsPGroup 2 S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact IsPGroup.of_card (n := n) (by rw [hScard, hq])
  have hidx : ¬ 2 ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    rw [hScard, hY] at h1
    have h2 : S.index = q ^ 2 - 1 := by
      have hpos : 0 < q := by omega
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    rw [h2]
    have h3 : 2 ∣ q ^ 2 := dvd_pow hqeven two_ne_zero
    omega
  have hpair : IsL2Pair ↥Y₀ S (2 ^ n) :=
    IsL2Pair.of_psl_isPGroup (f := n) hn0 ⟨e.trans pslMulEquivSL.symm⟩ hSp hidx
  have hN : Nat.card (Subgroup.normalizer (S : Set Y₀)) = q * (q - 1) := by
    rw [hq]; exact hpair.card_normalizer
  have hex : ∃ g : Y₀, g ∉ Subgroup.normalizer (S : Set Y₀) := by
    by_contra hall
    push Not at hall
    have : Subgroup.normalizer (S : Set Y₀) = ⊤ := eq_top_iff.mpr fun g _ => hall g
    rw [this, Subgroup.card_top, hY] at hN
    have hpos : 0 < q := by omega
    have := Nat.eq_of_mul_eq_mul_left hpos hN
    omega
  obtain ⟨g, hg⟩ := hex
  have hne : Timmesfeld75.conjSubgroup 1 S ≠ Timmesfeld75.conjSubgroup g S := by
    intro hcon
    rw [Timmesfeld75.conjSubgroup_eq_conjSubgroup_iff, inv_one, one_mul] at hcon
    exact hg hcon
  have htop := hpair.sup_conj_eq_top hne
  refine ⟨(g : Γ), g.2, ?_⟩
  have h1 := congrArg (Subgroup.map Y₀.subtype) htop
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
  have hS' : S.map Y₀.subtype = J := by
    rw [hS, Subgroup.subgroupOf_map_subtype, inf_of_le_left hJY]
  have h2 : (Timmesfeld75.conjSubgroup 1 S).map Y₀.subtype = J := by
    rw [Timmesfeld75.conjSubgroup_one, hS']
  have h3 : (Timmesfeld75.conjSubgroup g S).map Y₀.subtype = J.map (MulAut.conj (g : Γ)).toMonoidHom := by
    unfold Timmesfeld75.conjSubgroup
    rw [Subgroup.map_map, ← hS', Subgroup.map_map]
    congr 1
  rw [h2, h3] at h1
  exact h1

end L2Gen

end CFSG.CGT.PushingUpLit.CGT6
