module

public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.GH74.GLS.IVK.L2Borel

variable {F : Type} [Field F]

theorem iterate_semilinear (σ : F ≃+* F) (l : F) (j : ℕ) (t : F) :
    (fun x => l * σ x)^[j] t = (∏ i ∈ Finset.range j, (σ ^ i) l) * (σ ^ j) t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, Finset.prod_range_succ, pow_succ]
    simp only [RingAut.mul_apply, map_mul]
    ring

theorem iterate_mul_left (N : F) (j : ℕ) (t : F) : (fun x => N * x)^[j] t = N ^ j * t := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih]
    ring

theorem mul_pred_lt_pow {a : ℕ} (ha : 1 ≤ a) {k : ℕ} (hk : 2 ≤ k) :
    k * a + 1 < (a + 1) ^ k := by
  induction k, hk using Nat.le_induction with
  | base => nlinarith
  | succ k hk ih =>
    have h1 : 1 ≤ (a + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    calc (k + 1) * a + 1 = (k * a + 1) + a := by ring
      _ < (a + 1) ^ k + a := by omega
      _ ≤ (a + 1) ^ k + (a + 1) ^ k * a := by nlinarith
      _ = (a + 1) ^ (k + 1) := by ring

theorem mem_fixed_iff (σ : F ≃+* F) (a : F) :
    a ∈ FixedPoints.subfield (Subgroup.zpowers σ) F ↔ σ a = a := by
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h m
    have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (RingAut F) a := by
      rw [Subgroup.zpowers_le]
      exact h
    exact hle m.2

theorem exists_iterate_eq_id [Finite F] (σ : F ≃+* F) (hσ : σ ≠ 1) {l : F} (hl : l ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ m < Nat.card F - 1 ∧ ∀ t : F, (fun x => l * σ x)^[m] t = t := by
  classical
  have hfin : Finite (F ≃+* F) := Finite.of_injective (fun e : F ≃+* F => (e : F → F))
    (fun a b h => RingEquiv.ext (congrFun h))
  have hfinG : Finite (Subgroup.zpowers σ) := inferInstance
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  have : Fintype F := Fintype.ofFinite F
  set k := orderOf σ with hk
  have hk0 : 0 < k := orderOf_pos σ
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exfalso
      have : k = 1 := by omega
      exact hσ (orderOf_eq_one_iff.1 this)
    · exact h
  set F₀ := FixedPoints.subfield (Subgroup.zpowers σ) F with hF₀
  have hrank : Module.finrank F₀ F = k := by
    rw [FixedPoints.finrank_eq_card, ← Nat.card_eq_fintype_card, Nat.card_zpowers]
  have hcard : Fintype.card F = Fintype.card F₀ ^ k := by
    rw [Module.card_eq_pow_finrank (K := F₀) (V := F), hrank]
  set N : F := ∏ i ∈ Finset.range k, (σ ^ i) l with hN
  have hσk : σ ^ k = 1 := pow_orderOf_eq_one σ
  have hiter : ∀ t, (fun x => l * σ x)^[k] t = N * t := by
    intro t
    rw [iterate_semilinear, hσk]
    simp [hN]
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 fun i _ h => hl (EmbeddingLike.map_eq_zero_iff.1 h)
  have hσN : σ N = N := by
    have h1 : ∏ i ∈ Finset.range (k + 1), (σ ^ i) l = N * (σ ^ k) l := Finset.prod_range_succ _ _
    have h2 : ∏ i ∈ Finset.range (k + 1), (σ ^ i) l = σ N * l := by
      rw [Finset.prod_range_succ', hN, map_prod]
      simp [pow_succ']
    rw [hσk] at h1
    simp only [RingAut.one_apply] at h1
    have h3 : σ N * l = N * l := h2.symm.trans h1
    exact mul_right_cancel₀ hl h3
  have hNF₀ : N ∈ F₀ := (mem_fixed_iff σ N).2 hσN
  set N₀ : F₀ := ⟨N, hNF₀⟩ with hN₀
  have hN₀0 : N₀ ≠ 0 := fun h => hN0 (congrArg Subtype.val h)
  have hpow : N ^ (Fintype.card F₀ - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one N₀ hN₀0
    exact congrArg Subtype.val this
  have hq0 : 2 ≤ Fintype.card F₀ := Fintype.one_lt_card
  refine ⟨k * (Fintype.card F₀ - 1), ?_, ?_, ?_⟩
  · exact Nat.mul_pos hk0 (by omega)
  · rw [Nat.card_eq_fintype_card, hcard]
    have := mul_pred_lt_pow (a := Fintype.card F₀ - 1) (by omega) hk2
    rw [show Fintype.card F₀ - 1 + 1 = Fintype.card F₀ by omega] at this
    omega
  · intro t
    rw [Function.iterate_mul]
    have : (fun x => l * σ x)^[k] = fun x => N * x := funext hiter
    rw [this, iterate_mul_left, hpow, one_mul]

end CFSG.GH74.GLS.IVK.L2Borel
