module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.CGT.PushingUpLit.BHS7

theorem exists_coboundary_of_odd_index {E M : Type*} [Group E] [Group M] [Finite E]
    (hcomm : ∀ a b : M, a * b = b * a) (hM : ∀ m : M, m * m = 1) (ρ : E →* MulAut M)
    (c : E → M) (hc : ∀ a b, c (a * b) = ρ a (c b) * c a) (S : Subgroup E)
    (hS : ∀ s ∈ S, c s = 1) (hodd : ¬ 2 ∣ S.index) : ∃ m₀ : M, ∀ e, c e = m₀ * (ρ e m₀)⁻¹ := by
  classical
  let _ : CommGroup M := { ‹Group M› with mul_comm := hcomm }
  have _ : Fintype E := Fintype.ofFinite E
  have hconst : ∀ a b : E, a⁻¹ * b ∈ S → c a = c b := by
    intro a b hab
    have h1 := hc a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hS _ hab, map_one, one_mul] at h1
    exact h1.symm
  let f : E ⧸ S → M :=
    Quotient.lift c (fun a b (h : QuotientGroup.leftRel S a b) =>
      hconst a b (QuotientGroup.leftRel_apply.mp h))
  have hfmk : ∀ a : E, f (QuotientGroup.mk a) = c a := fun a => rfl
  have hf : ∀ (e : E) (x : E ⧸ S), ρ e (f x) = f (e • x) * (c e)⁻¹ := by
    intro e x
    induction x using QuotientGroup.induction_on with
    | H a =>
      show ρ e (c a) = c (e * a) * (c e)⁻¹
      rw [hc e a, mul_inv_cancel_right]
  have _ : Fintype (E ⧸ S) := Fintype.ofFinite _
  set m₁ : M := ∏ x : E ⧸ S, f x with hm₁
  have hcard : Fintype.card (E ⧸ S) = S.index := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  have hρ : ∀ e : E, ρ e m₁ = m₁ * ((c e)⁻¹) ^ S.index := by
    intro e
    have h1 : ρ e m₁ = ∏ x : E ⧸ S, (f (e • x) * (c e)⁻¹) := by
      rw [hm₁, map_prod]
      exact Finset.prod_congr rfl fun x _ => hf e x
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
    congr 1
    exact Fintype.prod_equiv (MulAction.toPerm e) (fun x => f (e • x)) f (fun x => rfl)
  have hodd' : Odd S.index := Nat.odd_iff.mpr (by omega)
  have hpow : ∀ e : E, ((c e)⁻¹) ^ S.index = c e := by
    intro e
    obtain ⟨k, hk⟩ := hodd'
    have hinv : (c e)⁻¹ = c e := inv_eq_of_mul_eq_one_right (hM (c e))
    rw [hk, pow_succ, pow_mul, hinv, pow_two, hM, one_pow, one_mul]
  refine ⟨m₁⁻¹, fun e => ?_⟩
  have h2 := hρ e
  rw [hpow e] at h2
  rw [map_inv, inv_inv, h2]
  exact (inv_mul_cancel_left m₁ (c e)).symm

end CFSG.CGT.PushingUpLit.BHS7
