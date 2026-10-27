module

public import Certificates.Data.Kernel.CosetLat.Avoid
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.Misc.PermClosSound

public section

namespace CFSG.KC.CosetLat

open CFSG.KC.Ord CFSG.KC.LQT.P
open CFSG.KC.Misc.Clos (ClosEnc allN_iff)

variable {Γ : Type*} [Group Γ] {enc : Γ → ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}

theorem allCos_sound (henc : ClosEnc enc M one) {T B : Subgroup Γ} {nT nU : ℕ}
    {ET EU : ℕ → ℕ} (hTx : ∀ g ∈ T, ∃ k < nT, enc g = ET k)
    (hBc : ∀ σ ∈ B, ∃ t ∈ T, ∃ i < nU, ∃ u : Γ, enc u = EU i ∧ t * u = σ) {P : ℕ → Bool}
    (h : ∀ i < nU, allCosAt M ET nT EU P i = true) : ∀ σ ∈ B, P (enc σ) = true := by
  intro σ hσ
  obtain ⟨t, ht, i, hi, u, hu, rfl⟩ := hBc σ hσ
  obtain ⟨k, hk, hke⟩ := hTx t ht
  have h' : P (M (ET k) (EU i)) = true := (allN_iff _ _).1 (h i hi) k hk
  rwa [← hke, ← hu, ← henc.enc_mul] at h'

theorem invPair_sound (henc : ClosEnc enc M one) {a b : Γ} {A A2 B B2 : ℕ} (ha : enc a = A)
    (ha2 : enc (a * a) = A2) (hb : enc b = B) (hb2 : enc (b * b) = B2) {σ : Γ}
    (h : invPairAt M A A2 B B2 (enc σ) = true) : ¬ (σ * a = a * a * σ ∧ σ * b = b * b * σ) := by
  rintro ⟨h1, h2⟩
  have e1 : M (enc σ) A = M A2 (enc σ) := by
    rw [← ha, ← ha2, ← henc.enc_mul, ← henc.enc_mul, h1]
  have e2 : M (enc σ) B = M B2 (enc σ) := by
    rw [← hb, ← hb2, ← henc.enc_mul, ← henc.enc_mul, h2]
  unfold invPairAt at h
  rw [e1, e2, Nat.beq_refl, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem mul_eq_sq_mul_of_conj_inv {a σ : Γ} (h3 : a * a * a = 1) (h : σ * a * σ⁻¹ = a⁻¹) :
    σ * a = a * a * σ := by
  have e : a * a = a⁻¹ := mul_eq_one_iff_eq_inv.1 h3
  rw [e, ← h]
  group

theorem no_inv_pair (henc : ClosEnc enc M one) {T B : Subgroup Γ} {nT nU : ℕ}
    {ET EU : ℕ → ℕ} (hTx : ∀ g ∈ T, ∃ k < nT, enc g = ET k)
    (hBc : ∀ σ ∈ B, ∃ t ∈ T, ∃ i < nU, ∃ u : Γ, enc u = EU i ∧ t * u = σ) {a b : Γ}
    {A A2 B' B2 : ℕ} (ha : enc a = A) (ha2 : enc (a * a) = A2) (hb : enc b = B')
    (hb2 : enc (b * b) = B2) (ha3 : a * a * a = 1) (hb3 : b * b * b = 1)
    (h : ∀ i < nU, allCosAt M ET nT EU (invPairAt M A A2 B' B2) i = true) :
    ∀ v ∈ B, ¬ (v * a * v⁻¹ = a⁻¹ ∧ v * b * v⁻¹ = b⁻¹) := by
  rintro v hv ⟨h1, h2⟩
  exact invPair_sound henc ha ha2 hb hb2 (allCos_sound henc hTx hBc h v hv)
    ⟨mul_eq_sq_mul_of_conj_inv ha3 h1, mul_eq_sq_mul_of_conj_inv hb3 h2⟩

end CFSG.KC.CosetLat

end
