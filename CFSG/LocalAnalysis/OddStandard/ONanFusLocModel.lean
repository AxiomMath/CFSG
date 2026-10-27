module

public import Certificates.Data.ONanF2Quot
public import CFSG.LocalAnalysis.OddStandard.ONanSylowFacts

public section

namespace CFSG.OddStandard.ONanRec

open F2 F2.AlpE Model

@[expose] def fE (i : Fin 2) : AlpE := ![lE, lE * zc] i

theorem fE_d : ∀ i : Fin 2, (fE i).d = 0 := by decide

theorem fE_sq : ∀ i : Fin 2, fE i * fE i = gen 0 ^ 2 * gen 1 ^ 2 := by decide

theorem fE_st : ∀ i : Fin 2, stE * fE i = fE i * stE := by decide

theorem stE_d : stE.d = 5 := by decide

theorem stE_sq : stE * stE = 1 := by decide

theorem fE_cent_d : ∀ (i : Fin 2) (d : Fin 8),
    (∀ k : Fin 3, act d k (fE i) = ![(fE i).v0, (fE i).v1, (fE i).v2] k) ↔ (d = 0 ∨ d = 5) := by
  decide

@[expose] def InA0 (i : Fin 2) (y : AlpE) : Prop :=
  y.d = 0 ∧ ∃ k : Fin 4, y * y = fE i ^ (k : ℕ)

instance (i : Fin 2) (y : AlpE) : Decidable (InA0 i y) := by
  unfold InA0
  infer_instance

theorem fE_st_A0 : ∀ (i : Fin 2) (a b c : ZMod 4), InA0 i ⟨0, a, b, c⟩ →
    ∃ k : Fin 4, stE * ⟨0, a, b, c⟩ * stE * (⟨0, a, b, c⟩ : AlpE)⁻¹ = fE i ^ (k : ℕ) := by
  decide

theorem fE_comm_mem : ∀ (i : Fin 2) (a b c : ZMod 4),
    InA0 i ((⟨0, a, b, c⟩ : AlpE) * stE * (⟨0, a, b, c⟩ : AlpE)⁻¹ * stE) := by
  decide

theorem fE_comm_surj : ∀ (i : Fin 2) (a b c : ZMod 4), InA0 i ⟨0, a, b, c⟩ →
    ∃ a' b' c' : ZMod 4, ∃ k : Fin 4,
      (⟨0, a', b', c'⟩ : AlpE) * stE * (⟨0, a', b', c'⟩ : AlpE)⁻¹ * stE =
        ⟨0, a, b, c⟩ * fE i ^ (k : ℕ) := by
  decide

theorem fE_sq_st : ∀ (i : Fin 2) (a b c : ZMod 4),
    InA0 i ((⟨5, a, b, c⟩ : AlpE) * ⟨5, a, b, c⟩) := by
  decide

theorem InA0_one : ∀ i : Fin 2, InA0 i 1 := by decide

theorem InA0_mul : ∀ (i : Fin 2) (a b c a' b' c' : ZMod 4), InA0 i ⟨0, a, b, c⟩ →
    InA0 i ⟨0, a', b', c'⟩ → InA0 i ((⟨0, a, b, c⟩ : AlpE) * ⟨0, a', b', c'⟩) := by
  decide

theorem InA0_inv : ∀ (i : Fin 2) (a b c : ZMod 4), InA0 i ⟨0, a, b, c⟩ →
    InA0 i (⟨0, a, b, c⟩ : AlpE)⁻¹ := by
  decide

theorem eta_of_d_zero {y : AlpE} (hy : y.d = 0) : y = ⟨0, y.v0, y.v1, y.v2⟩ := by
  ext <;> simp [hy]

@[expose] def A0E (i : Fin 2) : Subgroup AlpE where
  carrier := {y | InA0 i y}
  one_mem' := InA0_one i
  mul_mem' := by
    intro x y hx hy
    have hx' : InA0 i ⟨0, x.v0, x.v1, x.v2⟩ := eta_of_d_zero hx.1 ▸ hx
    have hy' : InA0 i ⟨0, y.v0, y.v1, y.v2⟩ := eta_of_d_zero hy.1 ▸ hy
    have := InA0_mul i _ _ _ _ _ _ hx' hy'
    rwa [← eta_of_d_zero hx.1, ← eta_of_d_zero hy.1] at this
  inv_mem' := by
    intro x hx
    have hx' : InA0 i ⟨0, x.v0, x.v1, x.v2⟩ := eta_of_d_zero hx.1 ▸ hx
    have := InA0_inv i _ _ _ hx'
    rwa [← eta_of_d_zero hx.1] at this

theorem mem_A0E {i : Fin 2} {y : AlpE} : y ∈ A0E i ↔ InA0 i y := Iff.rfl

set_option maxRecDepth 100000 in
theorem card_filter_InA0 : ∀ i : Fin 2, (Finset.univ.filter fun y : AlpE => InA0 i y).card = 16 := by
  decide +kernel

theorem card_A0E (i : Fin 2) : Nat.card (A0E i) = 16 := by
  have e : A0E i ≃ {y : AlpE // InA0 i y} := Equiv.subtypeEquivRight fun y => Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_filter_InA0 i

set_option maxRecDepth 100000 in
theorem card_filter_cent_fE : ∀ i : Fin 2,
    (Finset.univ.filter fun g : AlpE => g * fE i = fE i * g).card = 128 := by
  decide +kernel

theorem card_centralizer_fE (i : Fin 2) :
    Nat.card (Subgroup.centralizer ({fE i} : Set AlpE)) = 128 := by
  have e : Subgroup.centralizer ({fE i} : Set AlpE) ≃ {g : AlpE // g * fE i = fE i * g} :=
    Equiv.subtypeEquivRight fun g => by rw [Subgroup.mem_centralizer_singleton_iff]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_filter_cent_fE i

theorem fE_pow_four : ∀ i : Fin 2, fE i ^ 4 = 1 := by decide

theorem fE_sq_ne_one : ∀ i : Fin 2, fE i ^ 2 ≠ 1 := by decide

end CFSG.OddStandard.ONanRec
