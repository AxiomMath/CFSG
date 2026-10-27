module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section Omega

variable {G : Type} [Group G]

theorem pow_mul_eq_of_comm {a b : G} (hb : Commute b ⁅b, a⁆) (n : ℕ) :
    b ^ n * a = ⁅b, a⁆ ^ n * a * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : b * ⁅b, a⁆ ^ n = ⁅b, a⁆ ^ n * b := (hb.symm.pow_left n).symm.eq
    have h2 : b * a = ⁅b, a⁆ * a * b := by rw [commutatorElement_def]; group
    generalize ⁅b, a⁆ = c at ih h1 h2 ⊢
    calc b ^ (n + 1) * a = b * (b ^ n * a) := by group
      _ = b * (c ^ n * a * b ^ n) := by rw [ih]
      _ = (b * c ^ n) * a * b ^ n := by group
      _ = (c ^ n * b) * a * b ^ n := by rw [h1]
      _ = c ^ n * (b * a) * b ^ n := by group
      _ = c ^ n * (c * a * b) * b ^ n := by rw [h2]
      _ = c ^ (n + 1) * a * b ^ (n + 1) := by group

theorem mul_pow_class_two {a b : G} (ha : Commute a ⁅b, a⁆) (hb : Commute b ⁅b, a⁆) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n * ⁅b, a⁆ ^ (n.choose 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow := pow_mul_eq_of_comm (a := a) hb n
    have hcc : Nat.choose (n + 1) 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    generalize hk : n.choose 2 = k at ih ⊢
    rw [hcc, hk]
    generalize hc : ⁅b, a⁆ = c at ha hb hpow ih ⊢
    have h1 : c ^ k * a = a * c ^ k := (ha.symm.pow_left k).eq
    have h3 : c ^ n * a = a * c ^ n := (ha.symm.pow_left n).eq
    have h4 : c ^ n * b ^ n = b ^ n * c ^ n := (hb.symm.pow_pow n n).eq
    have h5 : c ^ (n + k) * b = b * c ^ (n + k) := (hb.symm.pow_left (n + k)).eq
    calc (a * b) ^ (n + 1) = (a * b) ^ n * (a * b) := by rw [pow_succ]
      _ = a ^ n * b ^ n * c ^ k * (a * b) := by rw [ih]
      _ = a ^ n * b ^ n * (c ^ k * a) * b := by group
      _ = a ^ n * b ^ n * (a * c ^ k) * b := by rw [h1]
      _ = a ^ n * (b ^ n * a) * c ^ k * b := by group
      _ = a ^ n * (c ^ n * a * b ^ n) * c ^ k * b := by rw [hpow]
      _ = a ^ n * (c ^ n * a) * b ^ n * c ^ k * b := by group
      _ = a ^ n * (a * c ^ n) * b ^ n * c ^ k * b := by rw [h3]
      _ = a ^ (n + 1) * (c ^ n * b ^ n) * c ^ k * b := by group
      _ = a ^ (n + 1) * (b ^ n * c ^ n) * c ^ k * b := by rw [h4]
      _ = a ^ (n + 1) * b ^ n * (c ^ (n + k) * b) := by group
      _ = a ^ (n + 1) * b ^ n * (b * c ^ (n + k)) := by rw [h5]
      _ = a ^ (n + 1) * b ^ (n + 1) * c ^ (n + k) := by group

theorem exists_omega1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup G} (hcl : ⁅⁅D, D⁆, D⁆ = ⊥) :
    ∃ Q : Subgroup G, ∀ x, x ∈ Q ↔ x ∈ D ∧ x ^ p = 1 := by
  have hle : ⁅D, D⁆ ≤ centralizer (D : Set G) := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcl
  have hcomm : ∀ d ∈ D, ∀ x ∈ D, ∀ y ∈ D, Commute d ⁅y, x⁆ := fun d hd x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hle (Subgroup.commutator_mem_commutator hy hx)) d hd
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := by
    rcases hp.eq_two_or_odd' with h | ⟨m, hm⟩
    · exact absurd h hp2
    · exact ⟨m, hm⟩
  refine ⟨{ carrier := {x | x ∈ D ∧ x ^ p = 1}
            mul_mem' := ?_
            one_mem' := ⟨D.one_mem, one_pow p⟩
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro x y ⟨hxD, hxp⟩ ⟨hyD, hyp⟩
    refine ⟨D.mul_mem hxD hyD, ?_⟩
    have hx : Commute x ⁅y, x⁆ := hcomm x hxD x hxD y hyD
    have hy : Commute y ⁅y, x⁆ := hcomm y hyD x hxD y hyD
    have h := mul_pow_class_two hx hy p
    have hcp : ⁅y, x⁆ ^ p = 1 := by
      rw [hy.commutatorElement_pow_left p, hyp, commutatorElement_one_left]
    have hch : p.choose 2 = p * m := by
      rw [Nat.choose_two_right, hm]
      have : (2 * m + 1) * (2 * m + 1 - 1) = 2 * ((2 * m + 1) * m) := by
        rw [show 2 * m + 1 - 1 = 2 * m by omega]; ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    rw [h, hxp, hyp, hch, pow_mul, hcp, one_pow, mul_one, mul_one]
  · rintro x ⟨hxD, hxp⟩
    refine ⟨D.inv_mem hxD, ?_⟩
    rw [inv_pow, hxp, inv_one]

end Omega

end CFSG.GH74.GLS.Stage2.Bender.Thm1
