module

public import CFSG.LieType.Chevalley.GraphFixedParameterFields

public section

namespace CFSG.LocalAnalysis.GLTheoremA.TD4Le

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

structure Std (e : ℕ) (K : Type) [Field K] (σ : K ≃+* K) : Prop where
  he : 1 ≤ e
  hK : Nat.card K = (2 ^ e) ^ 3
  hσ : (∀ c, σ c = c ^ 2 ^ e) ∨ ∀ c, σ c = c ^ (2 ^ e) ^ 2

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {e : ℕ}

theorem Std.charP_two (h : Std e K σ) : CharP K 2 := by
  have hK3 : Nat.card K = 2 ^ (3 * e) := by rw [h.hK, ← pow_mul, mul_comm]
  exact CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by have := h.he; omega) hK3

theorem Std.pow_cube (h : Std e K σ) (c : K) : c ^ (2 ^ e) ^ 3 = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [← h.hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem symm_pow_apply_pow_apply (σ : K ≃+* K) (n : ℕ) (c : K) :
    (σ.symm.toRingHom ^ n) ((σ.toRingHom ^ n) c) = c := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' σ.toRingHom, RingHom.coe_mul, Function.comp_apply, pow_succ σ.symm.toRingHom,
      RingHom.coe_mul, Function.comp_apply]
    simpa using ih c

theorem orbitField_symm (t : TwistTag) (σ : K ≃+* K) (a : Fin t.foldedTag.rank) :
    orbitField t K σ.symm.toRingHom a = orbitField t K σ.toRingHom a := by
  ext c
  rw [mem_orbitField, mem_orbitField]
  constructor
  · intro hc
    have := symm_pow_apply_pow_apply σ.symm (t.orbit a).card c
    rw [σ.symm_symm, hc] at this
    exact this
  · intro hc
    have := symm_pow_apply_pow_apply σ (t.orbit a).card c
    rw [hc] at this
    exact this

theorem Std.exists_normalized (h : Std e K σ) :
    ∃ σ₁ : K ≃+* K, (∀ c, σ₁ c = c ^ 2 ^ e) ∧
      ∀ (t : TwistTag) (a : Fin t.foldedTag.rank),
        orbitField t K σ.toRingHom a = orbitField t K σ₁.toRingHom a := by
  rcases h.hσ with h1 | h2
  · exact ⟨σ, h1, fun _ _ => rfl⟩
  · refine ⟨σ.symm, fun c => ?_, fun t a => (orbitField_symm t σ a).symm⟩
    refine σ.symm_apply_eq.2 ?_
    rw [h2, ← pow_mul, show 2 ^ e * (2 ^ e) ^ 2 = (2 ^ e) ^ 3 by ring, h.pow_cube]

theorem card_orbitField_std (h : Std e K σ) (a : Fin TwistTag.D4.foldedTag.rank) :
    Nat.card (orbitField TwistTag.D4 K σ.toRingHom a) = (2 ^ e) ^ (TwistTag.D4.orbit a).card := by
  obtain ⟨σ₁, hσ₁, hL⟩ := h.exists_normalized
  rw [hL TwistTag.D4 a]
  obtain ⟨σ', hσ', -, hcard, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.D4 Nat.prime_two h.he K h.hK
  have e1 : σ₁.toRingHom = σ'.toRingHom := RingHom.ext fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe,
      hσ₁, hσ']
  rw [e1]
  exact hcard a

theorem Std.apply_eq_of_pow_three (h : Std e K σ) (hQ : 2 ^ e % 3 = 1) {a : K} (ha : a ^ 3 = 1) :
    σ a = a := by
  have key : ∀ n : ℕ, n % 3 = 1 → a ^ n = a := fun n hn => by
    have : n = 3 * (n / 3) + 1 := by omega
    rw [this, pow_succ, pow_mul, ha, one_pow, one_mul]
  rcases h.hσ with h1 | h2
  · rw [h1]
    exact key _ hQ
  · rw [h2]
    refine key _ ?_
    rw [Nat.pow_mod, hQ]

end CFSG.LocalAnalysis.GLTheoremA.TD4Le

end
