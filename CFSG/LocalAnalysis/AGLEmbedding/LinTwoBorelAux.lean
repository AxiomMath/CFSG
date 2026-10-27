module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.End

public section

namespace CFSG.AGLEmbedding

section Torus

variable {F : Type*} [Field F]

theorem eq_sq_sub_sq_of_two_ne_zero (h2 : (2 : F) ≠ 0) (x : F) :
    x = ((x + 1) / 2) ^ 2 - ((x - 1) / 2) ^ 2 := by
  field_simp
  ring

theorem mul_mem_of_sq_mul_mem (h2 : (2 : F) ≠ 0) {A : AddSubgroup F}
    (hA : ∀ μ : F, μ ≠ 0 → ∀ a ∈ A, μ ^ 2 * a ∈ A) {a : F} (ha : a ∈ A) (x : F) :
    x * a ∈ A := by
  have hsq : ∀ μ : F, μ ^ 2 * a ∈ A := by
    intro μ
    rcases eq_or_ne μ 0 with rfl | hμ
    · rw [zero_pow two_ne_zero, zero_mul]
      exact A.zero_mem
    · exact hA μ hμ a ha
  rw [eq_sq_sub_sq_of_two_ne_zero h2 x, sub_mul]
  exact A.sub_mem (hsq _) (hsq _)

variable {G : Type*} [Group G]

theorem mem_normalizer_range_of_torus (ψ : Multiplicative F →* G) {c : G} {μ : F} (hμ : μ ≠ 0)
    (hc : ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd (μ ^ 2 * Multiplicative.toAdd a))) :
    c ∈ Subgroup.normalizer (ψ.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (hc a).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨Multiplicative.ofAdd ((μ ^ 2)⁻¹ * Multiplicative.toAdd b), ?_⟩
    have h := hc (Multiplicative.ofAdd ((μ ^ 2)⁻¹ * Multiplicative.toAdd b))
    rw [toAdd_ofAdd, mul_inv_cancel_left₀ (pow_ne_zero 2 hμ), ofAdd_toAdd, hb] at h
    exact mul_left_cancel (mul_right_cancel h)

theorem range_le_of_torus (h2 : (2 : F) ≠ 0) (ψ : Multiplicative F →* G) {W : Subgroup G}
    (hc : ∀ μ : Fˣ, ∃ c ∈ Subgroup.normalizer (W : Set G), ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a)))
    {a : Multiplicative F} (ha : ψ a ∈ W) (ha1 : ψ a ≠ 1) : ψ.range ≤ W := by
  let A : AddSubgroup F :=
    { carrier := {x | ψ (Multiplicative.ofAdd x) ∈ W}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul] at hx hy ⊢
        exact W.mul_mem hx hy
      zero_mem' := by simp
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, ofAdd_neg, map_inv] at hx ⊢
        exact W.inv_mem hx }
  have hmemA : ∀ x, x ∈ A ↔ ψ (Multiplicative.ofAdd x) ∈ W := fun x => Iff.rfl
  have hA : ∀ μ : F, μ ≠ 0 → ∀ x ∈ A, μ ^ 2 * x ∈ A := by
    intro μ hμ x hx
    obtain ⟨c, hcW, hc⟩ := hc (Units.mk0 μ hμ)
    have h := hc (Multiplicative.ofAdd x)
    rw [Units.val_mk0, toAdd_ofAdd] at h
    rw [hmemA, ← h]
    exact (Subgroup.mem_normalizer_iff.mp hcW _).mp hx
  have ha0 : Multiplicative.toAdd a ≠ 0 := by
    intro h0
    apply ha1
    rw [← ofAdd_toAdd a, h0, ofAdd_zero, map_one]
  have haA : Multiplicative.toAdd a ∈ A := by rwa [hmemA, ofAdd_toAdd]
  rintro _ ⟨b, rfl⟩
  have hb := mul_mem_of_sq_mul_mem h2 hA haA (Multiplicative.toAdd b / Multiplicative.toAdd a)
  rwa [div_mul_cancel₀ _ ha0, hmemA, ofAdd_toAdd] at hb

theorem conj_eq_of_torus (p : ℕ) [Fact p.Prime] [CharP F p] (h2 : (2 : F) ≠ 0)
    (ψ : Multiplicative F →* G) (hinj : Function.Injective ψ) {w : G}
    (hw : ∀ a : Multiplicative F, w * ψ a * w⁻¹ ∈ ψ.range)
    (hc : ∀ μ : Fˣ, ∃ c : G, (∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a))) ∧
      w * c * w⁻¹ * c⁻¹ ∈ ψ.range)
    {k : ℕ} (hwk : w ^ p ^ k = 1) (a : Multiplicative F) : w * ψ a * w⁻¹ = ψ a := by
  let Φ : F → G := fun x => ψ (Multiplicative.ofAdd x)
  have hΦ : ∀ x, Φ x = ψ (Multiplicative.ofAdd x) := fun x => rfl
  have hΦadd : ∀ x y, Φ (x + y) = Φ x * Φ y := fun x y => by
    rw [hΦ, hΦ, hΦ, ofAdd_add, map_mul]
  have hΦcomm : ∀ x y, Φ x * Φ y = Φ y * Φ x := fun x y => by
    rw [← hΦadd, ← hΦadd, add_comm]
  have hΦinj : Function.Injective Φ := hinj.comp Multiplicative.ofAdd.injective
  have hsq : ∀ μ : Fˣ, ∀ x y, w * Φ x * w⁻¹ = Φ y →
      w * Φ ((μ : F) ^ 2 * x) * w⁻¹ = Φ ((μ : F) ^ 2 * y) := by
    intro μ x y hxy
    obtain ⟨c, hc, z, hz⟩ := hc μ
    have hcx : c * Φ x * c⁻¹ = Φ ((μ : F) ^ 2 * x) := by
      rw [hΦ, hΦ, hc, toAdd_ofAdd]
    have hcy : c * Φ y * c⁻¹ = Φ ((μ : F) ^ 2 * y) := by
      rw [hΦ, hΦ, hc, toAdd_ofAdd]
    have hwc : w * c = ψ z * c * w := by rw [hz]; group
    have hzΦ : ψ z = Φ (Multiplicative.toAdd z) := by rw [hΦ, ofAdd_toAdd]
    calc w * Φ ((μ : F) ^ 2 * x) * w⁻¹ = (w * c) * Φ x * (w * c)⁻¹ := by rw [← hcx]; group
      _ = ψ z * (c * (w * Φ x * w⁻¹) * c⁻¹) * (ψ z)⁻¹ := by rw [hwc]; group
      _ = ψ z * Φ ((μ : F) ^ 2 * y) * (ψ z)⁻¹ := by rw [hxy, hcy]
      _ = Φ ((μ : F) ^ 2 * y) := by rw [hzΦ, hΦcomm, mul_inv_cancel_right]
  obtain ⟨l, hl⟩ := hw (Multiplicative.ofAdd 1)
  set lam : F := Multiplicative.toAdd l with hlam
  have hl' : w * Φ 1 * w⁻¹ = Φ (1 * lam) := by rw [one_mul, hΦ, hΦ, hlam, ofAdd_toAdd, hl]
  let A : AddSubgroup F :=
    { carrier := {x | w * Φ x * w⁻¹ = Φ (x * lam)}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [hΦadd, add_mul, hΦadd, ← hx, ← hy]
        group
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, zero_mul, hΦ, ofAdd_zero, map_one, mul_one, mul_inv_cancel]
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        have hneg : ∀ y, Φ (-y) = (Φ y)⁻¹ := fun y => by rw [hΦ, hΦ, ofAdd_neg, map_inv]
        rw [hneg, neg_mul, hneg, ← hx]
        group }
  have hmemA : ∀ x, x ∈ A ↔ w * Φ x * w⁻¹ = Φ (x * lam) := fun x => Iff.rfl
  have hAsq : ∀ μ : F, μ ≠ 0 → ∀ x ∈ A, μ ^ 2 * x ∈ A := by
    intro μ hμ x hx
    rw [hmemA] at hx ⊢
    have h := hsq (Units.mk0 μ hμ) x (x * lam) hx
    rwa [Units.val_mk0, ← mul_assoc] at h
  have hall : ∀ x, w * Φ x * w⁻¹ = Φ (x * lam) := fun x => by
    have h := mul_mem_of_sq_mul_mem h2 hAsq ((hmemA 1).mpr hl') x
    rwa [mul_one, hmemA] at h
  have hpow : ∀ m : ℕ, ∀ x, w ^ m * Φ x * (w ^ m)⁻¹ = Φ (x * lam ^ m) := by
    intro m
    induction m with
    | zero => intro x; rw [pow_zero, pow_zero, mul_one, one_mul, inv_one, mul_one]
    | succ m ih =>
      intro x
      calc w ^ (m + 1) * Φ x * (w ^ (m + 1))⁻¹ = w * (w ^ m * Φ x * (w ^ m)⁻¹) * w⁻¹ := by
            rw [pow_succ']; group
        _ = Φ (x * lam ^ m * lam) := by rw [ih, hall]
        _ = Φ (x * lam ^ (m + 1)) := by rw [pow_succ, mul_assoc]
  have hlam1 : lam ^ p ^ k = 1 := by
    have h := hpow (p ^ k) 1
    rw [hwk, one_mul, inv_one, mul_one, one_mul] at h
    exact (hΦinj h).symm
  have hlam : lam = 1 := by
    have h : (lam - 1) ^ p ^ k = 0 := by rw [sub_pow_char_pow, hlam1, one_pow, sub_self]
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero k (Fact.out : p.Prime).ne_zero)).mp h)
  have h := hall (Multiplicative.toAdd a)
  rwa [hlam, mul_one, hΦ, ofAdd_toAdd] at h

end Torus

end CFSG.AGLEmbedding
