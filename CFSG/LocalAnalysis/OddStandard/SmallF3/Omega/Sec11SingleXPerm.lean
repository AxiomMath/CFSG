module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K5S2

public section

namespace CFSG.OddStandard.SmallF3.Omega.K5

theorem s11s_exists_act (s : SL23) : ∃ τ : Equiv.Perm (Fin 4),
    ∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹ :=
  (by decide +kernel : ∀ s : SL23, ∃ τ : Equiv.Perm (Fin 4),
    ∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹) s

theorem s11s_exists_of_even {τ : Equiv.Perm (Fin 4)} (hτ : Equiv.Perm.sign τ = 1) :
    ∃ s : SL23, ∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹ :=
  (by decide +kernel : ∀ τ : Equiv.Perm (Fin 4), Equiv.Perm.sign τ = 1 → ∃ s : SL23,
    ∀ i, s * k5g i * s⁻¹ = k5g (τ i) ∨ s * k5g i * s⁻¹ = (k5g (τ i))⁻¹) τ hτ

theorem s11s_mem_klein_of_comm {p : Equiv.Perm (Fin 4)} (hp : ∀ v ∈ klein, p * v = v * p) :
    p ∈ klein :=
  (by decide +kernel : ∀ p : Equiv.Perm (Fin 4),
    (∀ v : Equiv.Perm (Fin 4), (v * v = 1 ∧ (v = 1 ∨ ∀ i, v i ≠ i)) → p * v = v * p) →
      (p * p = 1 ∧ (p = 1 ∨ ∀ i, p i ≠ i))) p fun v hv => hp v hv

theorem s11s_sign_of_sq_not_klein {p : Equiv.Perm (Fin 4)} (hp : p * p = 1) (hk : p ∉ klein) :
    Equiv.Perm.sign p = -1 :=
  (by decide +kernel : ∀ p : Equiv.Perm (Fin 4), p * p = 1 →
    ¬ (p * p = 1 ∧ (p = 1 ∨ ∀ i, p i ≠ i)) → Equiv.Perm.sign p = -1) p hp hk

theorem s11s_caseB_sq {q : SL23} (hq : q ^ 4 = 1) (h1 : q ≠ 1) (hm : q ≠ -1) :
    (q * (k5g 0)⁻¹ * q⁻¹ * k5g 0) * (q * (k5g 0)⁻¹ * q⁻¹ * k5g 0) = -1 :=
  (by decide +kernel : ∀ q : SL23, q ^ 4 = 1 → q ≠ 1 → q ≠ -1 →
    (q * (k5g 0)⁻¹ * q⁻¹ * k5g 0) * (q * (k5g 0)⁻¹ * q⁻¹ * k5g 0) = -1) q hq h1 hm

theorem s11s_sign_fpf {π : Equiv.Perm (Fin 4 ⊕ Fin 4)} (h2 : π * π = 1) (hf : ∀ p, π p ≠ p) :
    Equiv.Perm.sign π = 1 := by
  have h2' : π ^ 2 = 1 := by rw [pow_two, h2]
  rw [Equiv.Perm.sign_of_pow_two_eq_one h2']
  have h0 : Fintype.card (Function.fixedPoints π) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨p, hp⟩ => hf p hp⟩
  rw [h0]
  decide

end CFSG.OddStandard.SmallF3.Omega.K5
