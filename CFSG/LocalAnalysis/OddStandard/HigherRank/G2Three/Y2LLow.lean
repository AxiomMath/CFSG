module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Abel

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

variable {G : Type} [Group G]

theorem y2l_pow_val_add {N : ℕ} [NeZero N] {g : G} (hg : g ^ N = 1) (a b : ZMod N) :
    g ^ (a + b).val = g ^ a.val * g ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (a.val + b.val) N, pow_add, pow_mul, hg, one_pow, mul_one]

theorem y2l_pow_val_neg {N : ℕ} [NeZero N] {g : G} (hg : g ^ N = 1) (a : ZMod N) :
    g ^ (-a).val = (g ^ a.val)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← y2l_pow_val_add hg, neg_add_cancel, ZMod.val_zero, pow_zero]

@[expose] def y2l_psi (N : ℕ) (u v w : G) (x : Fin 3 → ZMod N) : G :=
  u ^ (x 0).val * v ^ (x 1).val * w ^ (x 2).val

theorem y2l_psi_zero (N : ℕ) [NeZero N] (u v w : G) : y2l_psi N u v w 0 = 1 := by
  simp [y2l_psi]

theorem y2l_psi_add {N : ℕ} [NeZero N] {u v w : G} (hu : u ^ N = 1) (hv : v ^ N = 1)
    (hw : w ^ N = 1) (huv : Commute u v) (huw : Commute u w) (hvw : Commute v w)
    (x y : Fin 3 → ZMod N) :
    y2l_psi N u v w (x + y) = y2l_psi N u v w x * y2l_psi N u v w y := by
  simp only [y2l_psi, Pi.add_apply, y2l_pow_val_add hu, y2l_pow_val_add hv, y2l_pow_val_add hw]
  rw [(huv.pow_pow (y 0).val (x 1).val).mul_mul_mul_comm,
    ((huw.pow_pow (y 0).val (x 2).val).mul_left (hvw.pow_pow (y 1).val (x 2).val)).mul_mul_mul_comm]

theorem y2l_card_ge_of_act {A : Type} [AddCommGroup A] [Finite A] (ψ : A → G)
    (hadd : ∀ a b, ψ (a + b) = ψ a * ψ b) (hψ : Function.Injective ψ) (H : Subgroup G)
    [Finite H] (hψH : ∀ a, ψ a ∈ H) {k : ℕ} (t : Fin k → G) (ht : ∀ i, t i ∈ H)
    (act : Fin k → A → A) (hact : ∀ i a, (t i)⁻¹ * ψ a * t i = ψ (act i a))
    (hdist : ∀ i j, (∀ a, act i a = act j a) → i = j) :
    k * Nat.card A ≤ Nat.card H := by
  have h0 : ψ 0 = 1 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := ψ 0) (by rw [← h, mul_one])
  have hinv : ∀ a, (ψ a)⁻¹ = ψ (-a) := fun a =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  let F : Fin k × A → H := fun p => ⟨t p.1 * ψ p.2, H.mul_mem (ht _) (hψH _)⟩
  have hF : Function.Injective F := by
    rintro ⟨i, a⟩ ⟨j, b⟩ hij
    have h1 : t i * ψ a = t j * ψ b := congrArg Subtype.val hij
    have h2 : t i = t j * ψ (b + -a) := by
      rw [hadd, ← hinv, ← mul_assoc, ← h1, mul_inv_cancel_right]
    have hij' : i = j := by
      refine hdist i j fun x => hψ ?_
      calc ψ (act i x) = (t i)⁻¹ * ψ x * t i := (hact i x).symm
        _ = (ψ (b + -a))⁻¹ * ((t j)⁻¹ * ψ x * t j) * ψ (b + -a) := by rw [h2]; group
        _ = ψ (-(b + -a)) * ψ (act j x) * ψ (b + -a) := by rw [hact j x, hinv]
        _ = ψ (act j x) := by rw [← hadd, ← hadd]; congr 1; abel
    subst hij'
    rw [hψ (mul_left_cancel h1)]
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin] at this

end CFSG.OddStandard.HigherRank.G2Three.Sec2
