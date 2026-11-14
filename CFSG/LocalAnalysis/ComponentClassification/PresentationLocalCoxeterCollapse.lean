module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.ComponentClassification.PresentationLocal

variable {V K : Type*} [Group K]

theorem eq_one_of_sq_of_cube {y : K} (h2 : y ^ 2 = 1) (h3 : y ^ 3 = 1) : y = 1 := by
  rw [pow_succ, h2, one_mul] at h3
  exact h3

theorem triangle_free_coxeter_adjacent_generator_collapse (Γ : SimpleGraph V)
    (hconn : Γ.Connected) (htri : Γ.CliqueFree 3) (t : V → K)
    (hgen : Subgroup.closure (Set.range t) = ⊤) (hsq : ∀ v, t v ^ 2 = 1)
    (hadj : ∀ u v, Γ.Adj u v → (t u * t v) ^ 3 = 1)
    (hnadj : ∀ u v, u ≠ v → ¬ Γ.Adj u v → (t u * t v) ^ 2 = 1) {u v : V} (huv : Γ.Adj u v)
    (heq : t u = t v) :
    ∃ x : K, x ^ 2 = 1 ∧ (∀ w, t w = x) ∧ IsCyclic K ∧ Nat.card K ≤ 2 := by
  classical
  set x := t u with hxdef
  have hx : x * x = 1 := by rw [← sq]; exact hsq u
  have key : ∀ a b c, Γ.Adj a b → t a = x → t b = x → Γ.Adj a c → t c = x := by
    intro a b c hab ha hb hac
    by_cases hcb : c = b
    · rw [hcb]
      exact hb
    have hncb : ¬ Γ.Adj c b := fun hcb' =>
      htri {a, b, c} (SimpleGraph.is3Clique_triple_iff.2 ⟨hab, hac, hcb'.symm⟩)
    have h2 : (t c * x) ^ 2 = 1 := by
      rw [← hb]
      exact hnadj c b hcb hncb
    have h3 : (t c * x) ^ 3 = 1 := by
      rw [← ha]
      exact hadj c a hac.symm
    have h1 := eq_one_of_sq_of_cube h2 h3
    calc t c = t c * x * x := by rw [mul_assoc, hx, mul_one]
      _ = x := by rw [h1, one_mul]
  have hwalk : ∀ (a b : V) (_ : Γ.Walk a b), (t a = x ∧ ∃ a', Γ.Adj a a' ∧ t a' = x) →
      t b = x ∧ ∃ b', Γ.Adj b b' ∧ t b' = x := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hac p ih =>
      rintro ⟨ha, a', haa', ha'⟩
      exact ih ⟨key _ a' _ haa' ha ha' hac, _, hac.symm, ha⟩
  have hall : ∀ w, t w = x := fun w =>
    (hwalk u w (hconn.preconnected u w).some ⟨rfl, v, huv, heq.symm⟩).1
  have hrange : Set.range t = {x} := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨w, hw⟩ => hw ▸ hall w, fun hy => ⟨u, hy.symm⟩⟩
  have htop : Subgroup.zpowers x = ⊤ := by
    rw [Subgroup.zpowers_eq_closure, ← hrange, hgen]
  have hz2 : x ^ (2 : ℤ) = 1 := by simpa using hsq u
  have hzz : ∀ r : ℤ, x ^ (r + r) = 1 := fun r => by
    rw [show r + r = (2 : ℤ) * r from (two_mul r).symm, zpow_mul x 2 r, hz2, one_zpow]
  have hxpow : ∀ k : ℤ, x ^ k = 1 ∨ x ^ k = x := by
    intro k
    rcases Int.even_or_odd k with hk | hk
    · left
      obtain ⟨r, hr⟩ := hk
      rw [hr]
      exact hzz r
    · right
      obtain ⟨r, hr⟩ := hk
      rw [hr, zpow_add, zpow_mul x 2 r, hz2, one_zpow, one_mul, zpow_one]
  have hcyc : IsCyclic K :=
    IsCyclic.mk ⟨x, fun y => Subgroup.mem_zpowers_iff.mp (htop.ge (Subgroup.mem_top y))⟩
  have hsurj : Function.Surjective (fun i : Fin 2 => if (i : ℕ) = 0 then (1 : K) else x) := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop.ge (Subgroup.mem_top y))
    rcases hxpow k with h | h
    · exact ⟨0, by simpa using h.symm.trans hk⟩
    · exact ⟨1, by simpa using h.symm.trans hk⟩
  refine ⟨x, hsq u, hall, hcyc, ?_⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  simpa using hle

end CFSG.ComponentClassification.PresentationLocal
