module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpDefs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup

namespace OrdFour

variable {A : Type} [Group A]

theorem exists_mem_sq_ne_one {W : Subgroup A} (h : ¬ ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    ∃ w ∈ W, w * w ≠ 1 := by
  by_contra hcon
  push Not at hcon
  refine h fun a ha b hb => ?_
  have hab : a * b * (a * b) = 1 := hcon _ (mul_mem ha hb)
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hcon a ha)
  have hb1 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hcon b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha1, hb1]

theorem orderOf_eq_four_of_sq {w : A} (h1 : w * w ≠ 1) (h2 : (w * w) * (w * w) = 1) :
    orderOf w = 4 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := w)
    (by simpa [pow_two] using h1) (by simpa [pow_succ, mul_assoc] using h2)
  simpa using h

theorem closure_comm_of_pairwise {S : Set A} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ a ∈ closure S, ∀ b ∈ closure S, a * b = b * a := by
  intro a ha b hb
  have h1 : closure S ≤ centralizer S := (closure_le _).2 fun t ht =>
    mem_centralizer_iff.2 fun s hs => hS s hs t ht
  have h2 : closure S ≤ centralizer ((closure S : Subgroup A) : Set A) := by
    rw [centralizer_closure]
    exact h1
  exact (mem_centralizer_iff.1 (h2 ha) b hb).symm

theorem conj_mem_closure {W : Subgroup A} {g : A} (hg : g ∈ normalizer (W : Set A)) {e : A}
    (he : e ∈ closure {w : A | w ∈ W ∧ orderOf w = 4}) :
    g * e * g⁻¹ ∈ closure {w : A | w ∈ W ∧ orderOf w = 4} := by
  induction he using Subgroup.closure_induction with
  | mem t ht =>
    refine subset_closure ⟨(mem_normalizer_iff.1 hg t).1 ht.1, ?_⟩
    have hs : SemiconjBy g t (g * t * g⁻¹) := by simp [SemiconjBy, mul_assoc]
    rw [← hs.orderOf_eq]
    exact ht.2
  | one => simp [one_mem]
  | mul a b _ _ ha hb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  | inv a _ ha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem ha

theorem mem_normalizer_closure {W : Subgroup A} {g : A} (hg : g ∈ normalizer (W : Set A)) :
    g ∈ normalizer
      ((closure {w : A | w ∈ W ∧ orderOf w = 4} : Subgroup A) : Set A) := by
  rw [mem_normalizer_iff]
  intro e
  refine ⟨conj_mem_closure hg, fun he => ?_⟩
  have := conj_mem_closure (inv_mem hg) he
  simpa [mul_assoc] using this

end OrdFour

open OrdFour in
theorem exists_noncomm_order_four {A : Type} [Group A] [Finite A] {p : ℕ} {W X : Subgroup A}
    {z : A} (h : Part1 p W X z) (hC : Core412 W X z) :
    ∃ u ∈ W, ∃ v ∈ W, orderOf u = 4 ∧ orderOf v = 4 ∧ u * v ≠ v * u := by
  by_contra hcon
  push Not at hcon
  have hcomm := closure_comm_of_pairwise (S := {w : A | w ∈ W ∧ orderOf w = 4})
    fun a ha b hb => hcon a ha.1 b hb.1 ha.2 hb.2
  have hEW : closure {w : A | w ∈ W ∧ orderOf w = 4} ≤ W :=
    (closure_le W).2 fun t ht => ht.1
  have hEc := h.abel_central _ hEW
    (fun w hw u hu => conj_mem_closure (le_normalizer hw) hu)
    (fun x hx => mem_normalizer_closure (h.setup.XW hx))
    (mem_normalizer_closure h.setup.zW) hcomm
  obtain ⟨w, hwW, hw1⟩ := exists_mem_sq_ne_one h.nonab
  have hw4 : orderOf w = 4 :=
    orderOf_eq_four_of_sq hw1 (hC.Z_exp2 _ (hC.sq_central w hwW))
  have hwE : w ∈ closure {w : A | w ∈ W ∧ orderOf w = 4} := subset_closure ⟨hwW, hw4⟩
  exact hw1 (hC.Z_exp2 w ⟨hwW, hEc hwE⟩)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
