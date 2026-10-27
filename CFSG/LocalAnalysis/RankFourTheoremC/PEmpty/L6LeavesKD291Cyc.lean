module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open Subgroup

theorem factorization_orderOf_eq_of_not_pow {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} (hp : p.Prime) {c : G} (hc : ∀ b : G, b ^ p ≠ c) :
    (orderOf c).factorization p = (Nat.card G).factorization p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg c)
  have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpos : 0 < Nat.card G := Nat.card_pos
  set k' : ℕ := (k % (Nat.card G : ℤ)).toNat with hk'
  have hk'eq : g ^ k' = c := by
    rw [← hk, ← zpow_natCast]
    have hnn : 0 ≤ k % (Nat.card G : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
    rw [hk', Int.toNat_of_nonneg hnn, ← hord]
    exact (zpow_mod_orderOf g k).symm ▸ rfl
  have hnp : ¬ p ∣ k' := by
    rintro ⟨m, hm⟩
    exact hc (g ^ m) (by rw [← pow_mul, mul_comm, ← hm, hk'eq])
  have hk0 : k' ≠ 0 := fun h => hnp (h ▸ dvd_zero p)
  have hordc : orderOf c = Nat.card G / Nat.gcd (Nat.card G) k' := by
    rw [← hk'eq, orderOf_pow' g hk0, hord]
  have hgcd : ¬ p ∣ Nat.gcd (Nat.card G) k' := fun h => hnp (h.trans (Nat.gcd_dvd_right _ _))
  rw [hordc, Nat.factorization_div (Nat.gcd_dvd_left _ _)]
  simp [Nat.factorization_eq_zero_of_not_dvd hgcd]

theorem exists_pow_mul_orderOf_eq {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (c : G) : ∃ d ∈ zpowers c, orderOf (d ^ p * c) = p ^ (orderOf c).factorization p := by
  have hm : 0 < orderOf c := orderOf_pos c
  set a := (orderOf c).factorization p with ha
  set m' := orderOf c / p ^ a with hm'
  have hmm : p ^ a * m' = orderOf c := Nat.ordProj_mul_ordCompl_eq_self (orderOf c) p
  have hcop : Nat.Coprime p m' := Nat.coprime_ordCompl hp hm.ne'
  have hm'0 : m' ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmm
    omega
  obtain ⟨t, -, ht0⟩ := Nat.exists_mul_mod_eq_of_coprime (m' - 1) hcop hm'0
  have h1 : Nat.ModEq m' (p * t + 1) (m' - 1 + 1) := Nat.ModEq.add_right 1 ht0
  have h2 : m' - 1 + 1 = m' := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm'0)
  rw [h2] at h1
  have ht : m' ∣ p * t + 1 :=
    Nat.modEq_zero_iff_dvd.1 (h1.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl))
  refine ⟨c ^ t, Subgroup.pow_mem _ (Subgroup.mem_zpowers c) t, ?_⟩
  have hexp : (c ^ t) ^ p * c = c ^ (p * t + 1) := by
    rw [← pow_mul, mul_comm t p, ← pow_succ]
  rw [hexp]
  have hN : p * t + 1 ≠ 0 := by omega
  rw [orderOf_pow' c hN]
  obtain ⟨N₁, hN₁⟩ := ht
  have hcopN : Nat.Coprime (p ^ a) (p * t + 1) :=
    Nat.Coprime.pow_left a ((Nat.coprime_mul_left_add_right p 1 t).2 (Nat.coprime_one_right p))
  have hcopN₁ : Nat.Coprime (p ^ a) N₁ := by
    rw [hN₁] at hcopN
    exact Nat.Coprime.coprime_mul_left_right hcopN
  have hgcd : Nat.gcd (orderOf c) (p * t + 1) = m' := by
    rw [← hmm, hN₁, mul_comm (p ^ a) m', Nat.gcd_mul_left, hcopN₁.gcd_eq_one, mul_one]
  rw [hgcd, ← hmm]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm'0)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
