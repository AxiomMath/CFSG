module

public import CFSG.LieType.SeitzGeneration.ExcTorusRank
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Five
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Eight
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Nine
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Twelve
public import CFSG.LieType.SeitzGeneration.ExcTorusE6One
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Two
public import CFSG.LieType.SeitzGeneration.ExcTorusE6Three

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Adjoint


theorem rankLE1_E6 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card K) (hcnt : degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1) :
    RankLE1 p (adjointGroup Tag.E6 K) := by
  have he0 := orderOf_natCast_ne_zero hp hpq
  have hlt := orderOf_lt_prime hp hpq (rfl : orderOf ((Nat.card K : ℕ) : ZMod p) = _)
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt he0 hlt
  have he4 : 4 ≤ e := by
    by_contra h
    have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
    interval_cases e <;> revert hcnt <;> decide
  have hp3 : 3 < p := by omega
  by_cases h0 : degCount Tag.E6 e = 0
  · intro F hF
    rw [elemAbelian_card_eq_one_of_degCount_zero (by simp) K hp hp3 hpq he h0 hF]
    exact hp.one_lt.le
  · have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (by simp) (Nat.pos_of_ne_zero h0)
    interval_cases e <;> first | exact absurd hcnt (by decide) | exact absurd h0 (by decide) | skip
    · exact (sylowTorus_E6_five K hp he).rankLE1 hp
    · exact (sylowTorus_E6_eight K hp he).rankLE1 hp
    · exact (sylowTorus_E6_nine K hp he).rankLE1 hp
    · exact (sylowTorus_E6_twelve K hp he).rankLE1 hp

theorem not_rankLE2_E6 (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) (hcnt : 3 ≤ degCount Tag.E6 (orderOf ((Nat.card K : ℕ) : ZMod p))) :
    ¬ RankLE2 p (adjointGroup Tag.E6 K) := by
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rw [he] at hcnt
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (e := e) (by simp) (by omega)
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have h1 : 1 ≤ e := Nat.pos_of_ne_zero he0
  interval_cases e <;> first | exact absurd hcnt (by decide) | skip
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_one K hp hp3 he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_two K hp hp3 he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc
  · obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_three K hp he
    exact not_rankLE2_of_elemAbelian hp (by norm_num) hE hc

end Adjoint

end CFSG.LieType.SeitzGeneration
