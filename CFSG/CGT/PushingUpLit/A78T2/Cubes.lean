module

public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.CGT.PushingUpLit.A78T2

variable {F : Type*} [Field F]

@[expose] def cubeSet (F : Type*) [Field F] : Set F := {x | ∃ t : F, t ≠ 0 ∧ x = t ^ 3}

theorem eq_of_dvd_of_three {D q : ℕ} (h1 : D ∣ q) (h2 : D - 1 ∣ q - 1) (h3 : q - 1 ≤ 3 * (D - 1))
    (h8 : 8 ≤ q) (hev : 2 ∣ q) : D = q := by
  obtain ⟨k, hk⟩ := h2
  have hD2 : 2 ≤ D := by
    by_contra hD
    have : D - 1 = 0 := by omega
    rw [this, zero_mul] at hk
    omega
  have hk3 : k ≤ 3 := by
    have : (D - 1) * k ≤ (D - 1) * 3 := by rw [← hk]; linarith
    exact Nat.le_of_mul_le_mul_left this (by omega)
  obtain ⟨m, hm⟩ := hev
  interval_cases k
  · omega
  · omega
  · omega
  · obtain ⟨n, hn⟩ := h1
    have hn3 : n < 3 := by
      have : D * n < D * 3 := by rw [← hn]; omega
      exact Nat.lt_of_mul_lt_mul_left this
    interval_cases n <;> omega

variable [Finite F]

theorem closure_cubes_eq_top {e : ℕ} (hq : Nat.card F = 2 ^ e) (he : 3 ≤ e) :
    AddSubgroup.closure (cubeSet F) = ⊤ := by
  classical
  have := Fintype.ofFinite F
  set A := AddSubgroup.closure (cubeSet F) with hA
  have hgen : ∀ t : F, t ≠ 0 → t ^ 3 ∈ A := fun t ht => AddSubgroup.subset_closure ⟨t, ht, rfl⟩
  have h1 : (1 : F) ∈ A := by simpa using hgen 1 one_ne_zero
  have hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A := by
    intro x hx y hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx' =>
      obtain ⟨t, ht, rfl⟩ := hx'
      induction hy using AddSubgroup.closure_induction with
      | mem y hy' =>
        obtain ⟨s, hs, rfl⟩ := hy'
        rw [← mul_pow]
        exact hgen _ (mul_ne_zero ht hs)
      | zero => rw [mul_zero]; exact A.zero_mem
      | add y y' _ _ h1 h2 => rw [mul_add]; exact A.add_mem h1 h2
      | neg y _ h1 => rw [mul_neg]; exact A.neg_mem h1
    | zero => rw [zero_mul]; exact A.zero_mem
    | add x x' _ _ h1 h2 => rw [add_mul]; exact A.add_mem h1 h2
    | neg x _ h1 => rw [neg_mul]; exact A.neg_mem h1
  have hpow : ∀ x ∈ A, ∀ n : ℕ, x ^ n ∈ A := by
    intro x hx n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  let A₁ : Subgroup Fˣ :=
    { carrier := {u | (u : F) ∈ A}
      one_mem' := by simpa using h1
      mul_mem' := fun {u v} hu hv => by
        show ((u * v : Fˣ) : F) ∈ A
        rw [Units.val_mul]
        exact hmul _ hu _ hv
      inv_mem' := fun {u} hu => by
        show ((u⁻¹ : Fˣ) : F) ∈ A
        have hpu : u ^ Nat.card Fˣ = 1 := pow_card_eq_one'
        have hpos : 0 < Nat.card Fˣ := Nat.card_pos
        have hinv : u⁻¹ = u ^ (Nat.card Fˣ - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos, hpu]
        rw [hinv, Units.val_pow_eq_pow_val]
        exact hpow _ hu _ }
  have hmemA₁ : ∀ u : Fˣ, u ∈ A₁ ↔ (u : F) ∈ A := fun u => Iff.rfl
  have hcardA : Nat.card A₁ + 1 = Nat.card A := by
    have hinj : Function.Injective (fun u : A₁ => ((u : Fˣ) : F)) := by
      intro u v huv
      exact Subtype.ext (Units.ext huv)
    have hrange : Set.range (fun u : A₁ => ((u : Fˣ) : F)) = (A : Set F) \ {0} := by
      ext x
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨u.2, (u : Fˣ).ne_zero⟩
      · rintro ⟨hx, hx0⟩
        refine ⟨⟨Units.mk0 x hx0, ?_⟩, rfl⟩
        exact hx
    have e1 : Nat.card A₁ = ((A : Set F) \ {0}).ncard := by
      rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]
    have e2 : ((A : Set F) \ {0}).ncard + 1 = (A : Set F).ncard :=
      Set.ncard_sdiff_singleton_add_one A.zero_mem (Set.toFinite _)
    rw [e1, e2, ← Nat.card_coe_set_eq]
    rfl
  have hdvd1 : Nat.card A ∣ Nat.card F := AddSubgroup.card_addSubgroup_dvd_card A
  have hunits : Nat.card Fˣ = Nat.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hdvd2 : Nat.card A₁ ∣ Nat.card Fˣ := Subgroup.card_subgroup_dvd_card A₁
  have hcube : Nat.card F - 1 ≤ 3 * Nat.card A₁ := by
    let cb : Fˣ →* Fˣ := powMonoidHom 3
    have hrle : cb.range ≤ A₁ := by
      rintro _ ⟨u, rfl⟩
      show ((u ^ 3 : Fˣ) : F) ∈ A
      rw [Units.val_pow_eq_pow_val]
      exact hgen _ u.ne_zero
    have hkr := Subgroup.card_ker_mul_card_range cb
    have hker : Nat.card cb.ker ≤ 3 := by
      have : Fintype Fˣ := Fintype.ofFinite _
      have h3 := IsCyclic.card_pow_eq_one_le (α := Fˣ) (n := 3) (by norm_num)
      have e3 : Nat.card cb.ker = Nat.card {u : Fˣ // u ^ 3 = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun u => by simp [cb, MonoidHom.mem_ker])
      rw [e3, Nat.card_eq_fintype_card, Fintype.card_subtype]
      convert h3
    have hrc : Nat.card cb.range ≤ Nat.card A₁ := Subgroup.card_le_of_le hrle
    rw [← hunits, ← hkr]
    calc Nat.card cb.ker * Nat.card cb.range ≤ 3 * Nat.card cb.range :=
          Nat.mul_le_mul_right _ hker
      _ ≤ 3 * Nat.card A₁ := Nat.mul_le_mul_left _ hrc
  have hq8 : 8 ≤ Nat.card F := by
    rw [hq]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hev : 2 ∣ Nat.card F := by rw [hq]; exact dvd_pow_self 2 (by omega)
  have hA1 : Nat.card A₁ = Nat.card A - 1 := by omega
  have hD : Nat.card A = Nat.card F := by
    refine eq_of_dvd_of_three hdvd1 ?_ ?_ hq8 hev
    · rw [← hA1, ← hunits]; exact hdvd2
    · rw [← hA1]; exact hcube
  exact AddSubgroup.eq_top_of_card_eq A hD

theorem mul_mem_of_closure_cubes {e : ℕ} (hq : Nat.card F = 2 ^ e) (he : 3 ≤ e)
    (B : AddSubgroup F) (hB : ∀ t : F, t ≠ 0 → ∀ r ∈ B, t ^ 3 * r ∈ B) (x : F) {r : F}
    (hr : r ∈ B) : x * r ∈ B := by
  have hx : x ∈ AddSubgroup.closure (cubeSet F) := by
    rw [closure_cubes_eq_top hq he]; trivial
  induction hx using AddSubgroup.closure_induction with
  | mem x hx' =>
    obtain ⟨t, ht, rfl⟩ := hx'
    exact hB t ht r hr
  | zero => rw [zero_mul]; exact B.zero_mem
  | add x x' _ _ h1 h2 => rw [add_mul]; exact B.add_mem h1 h2
  | neg x _ h1 => rw [neg_mul]; exact B.neg_mem h1

end CFSG.CGT.PushingUpLit.A78T2
