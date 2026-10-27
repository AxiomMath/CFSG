module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AbelianTransitive
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

open Equiv

theorem card_eq_of_abelian_transitive {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin n, ∃ a ∈ A, a i = j) (i0 : Fin n) : Nat.card A = n := by
  have hinj : Function.Injective (fun a : A => (a : Equiv.Perm (Fin n)) i0) := by
    intro a b hab
    have hab' : (a : Equiv.Perm (Fin n)) i0 = (b : Equiv.Perm (Fin n)) i0 := hab
    obtain ⟨c, hcdef⟩ : ∃ c : Equiv.Perm (Fin n), c = (a : Equiv.Perm (Fin n))⁻¹ * b :=
      ⟨_, rfl⟩
    have hc : c ∈ A := by
      rw [hcdef]
      exact A.mul_mem (A.inv_mem a.2) b.2
    have hfix : c i0 = i0 := by
      rw [hcdef, Equiv.Perm.mul_apply, ← hab', ← Equiv.Perm.mul_apply, inv_mul_cancel,
        Equiv.Perm.one_apply]
    have hone : c = 1 := by
      refine Equiv.ext fun j => ?_
      obtain ⟨d, hd, hdj⟩ := htrans i0 j
      have hcd := hcomm c hc d hd
      have h1 : c (d i0) = d i0 := by
        have h2 := congrArg (fun p : Equiv.Perm (Fin n) => p i0) hcd
        simp only [Equiv.Perm.mul_apply] at h2
        rw [h2, hfix]
      rw [← hdj, Equiv.Perm.one_apply, h1]
    rw [hcdef] at hone
    exact Subtype.ext (inv_mul_eq_one.mp hone)
  have hsurj : Function.Surjective (fun a : A => (a : Equiv.Perm (Fin n)) i0) := by
    intro j
    obtain ⟨a, ha, hai⟩ := htrans i0 j
    exact ⟨⟨a, ha⟩, hai⟩
  rw [Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem isCyclic_of_abelian_transitive_77 (A : Subgroup (Equiv.Perm (Fin 77)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htrans : ∀ i j : Fin 77, ∃ a ∈ A, a i = j) : IsCyclic A := by
  have hcard : Nat.card A = 77 := card_eq_of_abelian_transitive A hcomm htrans 0
  have h7 : 7 ∣ Nat.card A := by
    rw [hcard]
    norm_num
  have h11 : 11 ∣ Nat.card A := by
    rw [hcard]
    norm_num
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 7 h7
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 11 h11
  have hxy : Commute x y := Subtype.ext (hcomm x.1 x.2 y.1 y.2)
  have horder : orderOf (x * y) = orderOf x * orderOf y :=
    hxy.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hy]; norm_num)
  have h77 : orderOf (x * y) = 77 := by simp [horder, hx, hy]
  exact isCyclic_of_card_le_orderOf (x * y) (le_of_eq (hcard.trans h77.symm))

variable {n : ℕ}

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
