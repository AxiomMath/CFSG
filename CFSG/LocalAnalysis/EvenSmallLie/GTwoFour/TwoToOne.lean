module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.Finite

public noncomputable section

namespace CFSG.EvenSmallLie.GTwoFour

open Subgroup

section TwoToOne

variable {M X : Type*} [Group M] [Group X] {π : M →* X} {z : M}

theorem card_sq_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card {x : A // x * x = a} = Nat.card {y : B // y * y = e a} :=
  Nat.card_congr (e.toEquiv.subtypeEquiv fun x => by
    change x * x = a ↔ e x * e x = e a
    rw [← map_mul, e.injective.eq_iff])

theorem card_subtype_le_of_imp {A : Type*} [Finite A] {p q : A → Prop} (h : ∀ a, p a → q a) :
    Nat.card {a // p a} ≤ Nat.card {a // q a} :=
  Nat.card_le_card_of_injective (fun a => ⟨a.1, h a.1 a.2⟩) fun a b hab => by
    simp only [Subtype.mk.injEq] at hab
    exact Subtype.ext hab

variable [Finite M] (hπ : Function.Surjective π) (hz : ∀ k, π k = 1 ↔ k = 1 ∨ k = z)
include hπ hz

omit [Finite M] hπ in
theorem eq_or_eq_mul_of_map_eq {s s' : M} (h : π s = π s') : s' = s ∨ s' = s * z := by
  rcases (hz (s⁻¹ * s')).1 (by rw [map_mul, map_inv, h, inv_mul_cancel]) with h' | h'
  · left; rw [← mul_inv_cancel_left s s', h', mul_one]
  · right; rw [← mul_inv_cancel_left s s', h']

theorem card_le_two_mul (S : Subgroup M) (T : X → Prop) :
    Nat.card {s : S // T (π s)} ≤ 2 * Nat.card {q : X // q ∈ S.map π ∧ T q} := by
  classical
  have : Finite X := Finite.of_surjective π hπ
  let σ : X → M := Function.surjInv hπ
  have hσ : ∀ q, π (σ q) = q := Function.surjInv_eq hπ
  let f : {s : S // T (π s)} → {q : X // q ∈ S.map π ∧ T q} × Bool := fun s =>
    (⟨π s.1, ⟨s.1, s.1.2, rfl⟩, s.2⟩, decide ((s.1 : M) = σ (π s.1)))
  have hf : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, hsT⟩ ⟨⟨s', hs'⟩, hs'T⟩ h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq, decide_eq_decide] at h
    obtain ⟨h1, h2⟩ := h
    refine Subtype.ext (Subtype.ext ?_)
    change s = s'
    by_cases hb : s = σ (π s)
    · have hb' : s' = σ (π s') := h2.1 hb
      rw [hb, hb', h1]
    · have hb' : ¬ s' = σ (π s') := fun h => hb (h2.2 h)
      rcases eq_or_eq_mul_of_map_eq hz h1 with h' | h'
      · exact h'.symm
      · rcases eq_or_eq_mul_of_map_eq hz (hσ (π s)).symm with h'' | h''
        · exact absurd h''.symm hb
        · exact absurd (by rw [← h1, h'', ← h']) hb'
  calc Nat.card {s : S // T (π s)}
      ≤ Nat.card ({q : X // q ∈ S.map π ∧ T q} × Bool) := Nat.card_le_card_of_injective f hf
    _ = 2 * Nat.card {q : X // q ∈ S.map π ∧ T q} := by
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

omit hπ in
theorem two_mul_card_le (hz1 : z ≠ 1) (S : Subgroup M) (hzS : z ∈ S)
    (T : X → Prop) :
    2 * Nat.card {q : X // q ∈ S.map π ∧ T q} ≤ Nat.card {s : S // T (π s)} := by
  classical
  have hz0 : π z = 1 := (hz z).2 (Or.inr rfl)
  have hτ : ∀ q : {q : X // q ∈ S.map π ∧ T q}, ∃ s : S, π s = q.1 := fun q => by
    obtain ⟨s, hs, hsq⟩ := q.2.1
    exact ⟨⟨s, hs⟩, hsq⟩
  choose τ hτ using hτ
  let g : {q : X // q ∈ S.map π ∧ T q} × Bool → {s : S // T (π s)} := fun p =>
    if p.2 then ⟨τ p.1, by rw [hτ]; exact p.1.2.2⟩
    else ⟨τ p.1 * ⟨z, hzS⟩, by
      change T (π ((τ p.1 : M) * z))
      rw [map_mul, hz0, mul_one, hτ]
      exact p.1.2.2⟩
  have hgπ : ∀ p, π (g p).1 = p.1.1 := fun ⟨q, b⟩ => by
    cases b
    · change π ((τ q : M) * z) = q.1
      rw [map_mul, hz0, mul_one, hτ]
    · exact hτ q
  have hg : Function.Injective g := by
    rintro ⟨q, b⟩ ⟨q', b'⟩ h
    have hq : q = q' := Subtype.ext (by rw [← hgπ (q, b), ← hgπ (q', b'), h])
    subst hq
    cases b <;> cases b'
    · rfl
    · exfalso
      have h' := congrArg (fun x : {s : S // T (π s)} => ((x.1 : S) : M)) h
      change (τ q : M) * z = τ q at h'
      exact hz1 (mul_eq_left.1 h')
    · exfalso
      have h' := congrArg (fun x : {s : S // T (π s)} => ((x.1 : S) : M)) h
      change (τ q : M) = τ q * z at h'
      exact hz1 (mul_eq_left.1 h'.symm)
    · rfl
  calc 2 * Nat.card {q : X // q ∈ S.map π ∧ T q}
      = Nat.card ({q : X // q ∈ S.map π ∧ T q} × Bool) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]
    _ ≤ Nat.card {s : S // T (π s)} := Nat.card_le_card_of_injective g hg

end TwoToOne

end CFSG.EvenSmallLie.GTwoFour
