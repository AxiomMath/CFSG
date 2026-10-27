module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Q8Semidihedral

theorem false_of_comm_card_eight {H : Type*} [Group H] [Finite H] (hc : ∀ a b : H, a * b = b * a)
    (hcard : 8 ≤ Nat.card H) {z : H}
    (huniq : ∀ x : H, x * x = 1 → x = 1 ∨ x = z) (hexp : ∀ x : H, x ^ 4 = 1) : False := by
  classical
  let f : H →* H := MonoidHom.mk' (fun x => x * x) (fun a b => by
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [hc b a]
      _ = a * a * (b * b) := by simp only [mul_assoc])
  have hf : ∀ x, f x = x * x := fun x => rfl
  have hker : Nat.card f.ker ≤ 2 := by
    have hsub : (f.ker : Set H) ⊆ {1, z} := by
      intro x hx
      have hx' : x * x = 1 := by
        have := (MonoidHom.mem_ker.1 hx)
        rwa [hf] at this
      rcases huniq x hx' with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Nat.card f.ker = Set.ncard (f.ker : Set H) := (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, z} : Set H) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
  have hrange : Nat.card f.range ≤ 2 := by
    have hsub : (f.range : Set H) ⊆ {1, z} := by
      rintro _ ⟨x, rfl⟩
      have h4 : (x * x) * (x * x) = 1 := by
        have := hexp x
        simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using this
      rcases huniq (x * x) h4 with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Nat.card f.range = Set.ncard (f.range : Set H) := (Nat.card_coe_set_eq _).symm
      _ ≤ Set.ncard ({1, z} : Set H) := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
  have hmul : Nat.card f.ker * Nat.card f.range = Nat.card H := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker] at h1
    exact h1
  have : Nat.card f.ker * Nat.card f.range ≤ 2 * 2 := Nat.mul_le_mul hker hrange
  omega

section Aux

variable {G : Type*} [Group G]

theorem pow_four_conj (q w : G) : (q * w) ^ 4 = (q * (w * q * w)) * (q * (w * q * w)) := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem comm_of_conj_eq_inv {Q : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hinv : ∀ q ∈ Q, w * q * w = q⁻¹) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : x * y = y * x := by
  have hmul : w * (x * y) * w = (w * x * w) * (w * y * w) := by
    calc w * (x * y) * w = w * x * (w * w) * y * w := by rw [hw2]; simp only [mul_one, mul_assoc]
      _ = (w * x * w) * (w * y * w) := by simp only [mul_assoc]
  have h1 : (x * y)⁻¹ = (y * x)⁻¹ := by
    rw [← hinv _ (Q.mul_mem hx hy), hmul, hinv x hx, hinv y hy, mul_inv_rev y x]
  exact inv_injective h1

theorem conj_eq_inv_of_forall_pow_four_ne {Q : Subgroup G} {z w : G}
    (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (huniq : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z) (hexp : ∀ x ∈ Q, x ^ 4 = 1)
    (hwN : ∀ x ∈ Q, w * x * w ∈ Q) (hw2 : w * w = 1)
    (hfix : ∀ x ∈ Q, w * x = x * w → x = 1 ∨ x = z)
    (hcon : ∀ q ∈ Q, (q * w) ^ 4 ≠ z) :
    ∀ q ∈ Q, w * q * w = q⁻¹ := by
  have hww : ∀ a : G, w * (w * a) = a := fun a => by rw [← mul_assoc, hw2, one_mul]
  have hzz : ∀ a : G, z * (z * a) = a := fun a => by rw [← mul_assoc, hz2, one_mul]
  have hstep : ∀ q ∈ Q, q * (w * q * w) = 1 ∨ q * (w * q * w) = z := by
    intro q hq
    have hxQ : q * (w * q * w) ∈ Q := Q.mul_mem hq (hwN q hq)
    have hx4 : (q * (w * q * w)) * (q * (w * q * w)) = (q * w) ^ 4 := (pow_four_conj q w).symm
    have hxx : ((q * (w * q * w)) * (q * (w * q * w))) * ((q * (w * q * w)) * (q * (w * q * w))) = 1 := by
      have := hexp _ hxQ
      simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using this
    have hxx1 : (q * (w * q * w)) * (q * (w * q * w)) = 1 := by
      rcases huniq _ (Q.mul_mem hxQ hxQ) hxx with h | h
      · exact h
      · exact absurd (hx4.symm.trans h) (hcon q hq)
    exact huniq _ hxQ hxx1
  have hzw : w * z * w = z := by
    have hsq : (w * z * w) * (w * z * w) = 1 := by
      simp only [mul_assoc, hww, hzz, hw2]
    rcases huniq _ (hwN z hzQ) hsq with h | h
    · exfalso
      apply hz1
      calc z = w * (w * z * w) * w := by simp only [mul_assoc, hww, hw2, mul_one]
        _ = 1 := by rw [h, mul_one, hw2]
    · exact h
  have hgen : ∀ q ∈ Q, q ≠ 1 → q ≠ z → w * q * w = q⁻¹ := by
    intro q hq hq1 hqz
    rcases hstep q hq with h | h
    · exact eq_inv_of_mul_eq_one_right h
    · exfalso
      have hq2ne : q * q ≠ 1 := fun h' => by
        rcases huniq q hq h' with h'' | h''
        · exact hq1 h''
        · exact hqz h''
      have hq4 : (q * q) * (q * q) = 1 := by
        simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using hexp q hq
      have hqq : q * q = z := by
        rcases huniq (q * q) (Q.mul_mem hq hq) hq4 with h' | h'
        · exact absurd h' hq2ne
        · exact h'
      have hqinv : q⁻¹ = q * z := by
        apply inv_eq_of_mul_eq_one_right
        rw [← mul_assoc, hqq, hz2]
      have hwqw : w * q * w = q := by
        have e1 : w * q * w = q⁻¹ * z := eq_inv_mul_of_mul_eq h
        rw [e1, hqinv, mul_assoc, hz2, mul_one]
      have hcomm : w * q = q * w := by
        calc w * q = w * q * (w * w) := by rw [hw2, mul_one]
          _ = (w * q * w) * w := by simp only [mul_assoc]
          _ = q * w := by rw [hwqw]
      rcases hfix q hq hcomm with h' | h'
      · exact hq1 h'
      · exact hqz h'
  intro q hq
  by_cases hq1 : q = 1
  · rw [hq1, mul_one, hw2, inv_one]
  by_cases hqz : q = z
  · rw [hqz, hzw]
    exact (inv_eq_of_mul_eq_one_right hz2).symm
  · exact hgen q hq hq1 hqz

end Aux

theorem exists_pow_four_eq {G : Type*} [Group G] [Finite G] {Q : Subgroup G} {z w : G}
    (hQ8 : 8 ≤ Nat.card ↥Q) (hzQ : z ∈ Q) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (huniq : ∀ x ∈ Q, x * x = 1 → x = 1 ∨ x = z) (hexp : ∀ x ∈ Q, x ^ 4 = 1)
    (hwN : ∀ x ∈ Q, w * x * w⁻¹ ∈ Q) (hw2 : w * w = 1)
    (hfix : ∀ x ∈ Q, w * x = x * w → x = 1 ∨ x = z) :
    ∃ q ∈ Q, (q * w) ^ 4 = z := by
  by_contra hcon'
  have hcon : ∀ q ∈ Q, (q * w) ^ 4 ≠ z := fun q hq h => hcon' ⟨q, hq, h⟩
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwN' : ∀ x ∈ Q, w * x * w ∈ Q := fun x hx => by
    have := hwN x hx
    rwa [hwinv] at this
  have hinv := conj_eq_inv_of_forall_pow_four_ne hzQ hz2 hz1 huniq hexp hwN' hw2 hfix hcon
  refine false_of_comm_card_eight (H := Q) (z := ⟨z, hzQ⟩) ?_ hQ8 ?_ ?_
  · intro a b
    exact Subtype.ext (comm_of_conj_eq_inv hw2 hinv a.2 b.2)
  · intro x hx
    rcases huniq x x.2 (congrArg Subtype.val hx) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · intro x
    exact Subtype.ext (hexp x x.2)

end Q8Semidihedral

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
