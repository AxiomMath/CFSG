module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Combinatorics.Matroid.Init

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

variable {K : Type} [Field K] [Finite K]

theorem exists_pow_card_of_fixes_subfield (F : Subfield K) (ε : K ≃+* K)
    (hε : ∀ c ∈ F, ε c = c) :
    ∃ j < Module.finrank F K, ∀ c, ε c = c ^ (Nat.card F ^ j) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let ε' : K ≃ₐ[F] K := AlgEquiv.ofRingEquiv (f := ε) fun x => hε x x.2
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F K).2 ε'
  refine ⟨n, n.2, fun c => ?_⟩
  have h1 := congrArg (fun φ : K ≃ₐ[F] K => φ c) hn
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h1
  rw [Nat.card_eq_fintype_card]
  exact h1.symm

theorem finrank_eq_of_card_eq_pow (F : Subfield K) {n : ℕ} (hn : Nat.card K = Nat.card F ^ n) :
    Module.finrank F K = n := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype K := Fintype.ofFinite K
  have h1 : Fintype.card K = Fintype.card F ^ Module.finrank F K := Module.card_eq_pow_finrank
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hn] at h1
  have h2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact (Nat.pow_right_injective h2 h1).symm

theorem exists_pow_card_of_fixes_eqLocus (δ : K ≃+* K) {m n : ℕ}
    (hm : Nat.card (RingHom.eqLocusField δ.toRingHom (RingHom.id K)) = m)
    (hK : Nat.card K = m ^ n) (ε : K ≃+* K) (hε : ∀ c, δ c = c → ε c = c) :
    ∃ j < n, ∀ c, ε c = c ^ (m ^ j) := by
  set F : Subfield K := RingHom.eqLocusField δ.toRingHom (RingHom.id K) with hF
  have hfin : Module.finrank F K = n := finrank_eq_of_card_eq_pow F (by rw [hm, hK])
  obtain ⟨j, hj, hεj⟩ := exists_pow_card_of_fixes_subfield F ε fun c hc => hε c hc
  rw [hfin] at hj
  rw [hm] at hεj
  exact ⟨j, hj, hεj⟩

theorem pow_natCard_eq_self (c : K) : c ^ Nat.card K = c := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem eq_one_or_eq_or_eq_inv_of_fixes_eqLocus {q : ℕ} (hK : Nat.card K = q ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q)
    (hq : Nat.card (RingHom.eqLocusField σ.toRingHom (RingHom.id K)) = q)
    (ε : K ≃+* K) (hε : ∀ c, σ c = c → ε c = c) : ε = 1 ∨ ε = σ ∨ ε = σ⁻¹ := by
  obtain ⟨j, hj, hεj⟩ := exists_pow_card_of_fixes_eqLocus σ hq hK ε hε
  interval_cases j
  · left
    exact RingEquiv.ext fun c => by rw [hεj, pow_zero, pow_one]; rfl
  · right; left
    exact RingEquiv.ext fun c => by rw [hεj, pow_one, hσ]
  · right; right
    refine eq_inv_of_mul_eq_one_left (RingEquiv.ext fun c => ?_)
    change ε (σ c) = c
    rw [hεj, hσ, ← pow_mul, show q * q ^ 2 = q ^ 3 by ring, ← hK, pow_natCard_eq_self]

theorem sq_eq_one_of_fixes_eqLocus {m : ℕ} (hK : Nat.card K = m ^ 2) (δ : K ≃+* K)
    (hm : Nat.card (RingHom.eqLocusField δ.toRingHom (RingHom.id K)) = m)
    (ε : K ≃+* K) (hε : ∀ c, δ c = c → ε c = c) : ε ^ 2 = 1 := by
  obtain ⟨j, hj, hεj⟩ := exists_pow_card_of_fixes_eqLocus δ hm hK ε hε
  refine RingEquiv.ext fun c => ?_
  change ε (ε c) = c
  rw [hεj, hεj, ← pow_mul]
  interval_cases j
  · simp
  · rw [pow_one, ← sq, ← hK, pow_natCard_eq_self]

end CFSG.ComponentClassification.CatLeafProof
