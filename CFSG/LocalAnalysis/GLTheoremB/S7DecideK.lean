module

public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.LocalAnalysis.GLTheoremB.S7DecideK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem h16 : 7 ≤ 16 := by norm_num

@[expose] noncomputable def commK (c d : ℕ) : Bool := Nat.beq (mulK 7 c d) (mulK 7 d c)

@[expose] noncomputable def conjK (c v t₁ t₂ t₃ : ℕ) : Bool :=
  Nat.beq (mulK 7 c v) (mulK 7 t₁ c) || Nat.beq (mulK 7 c v) (mulK 7 t₂ c) ||
    Nat.beq (mulK 7 c v) (mulK 7 t₃ c)

theorem commK_iff {σ τ : Perm (Fin 7)} : commK (enc σ) (enc τ) = true ↔ σ * τ = τ * σ :=
  comm_enc_iff h16

theorem conjK_sound {c v t₁ t₂ t₃ : Perm (Fin 7)}
    (h : conjK (enc c) (enc v) (enc t₁) (enc t₂) (enc t₃) = true) :
    c * v * c⁻¹ = t₁ ∨ c * v * c⁻¹ = t₂ ∨ c * v * c⁻¹ = t₃ := by
  rw [conjK.eq_1, ← enc_mul h16, ← enc_mul h16, ← enc_mul h16, ← enc_mul h16] at h
  simp only [Bool.or_eq_true] at h
  rw [beq_enc_iff h16, beq_enc_iff h16, beq_enc_iff h16] at h
  rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

@[expose] noncomputable def qConj (c : ℕ) : Bool :=
  (!commK c 106180641 ||
      (conjK c 90391056 90391056 70668816 54878736 && conjK c 70668816 90391056 70668816 54878736)) &&
    (!commK c 104153616 ||
      (conjK c 39073281 39073281 22294626 5517606 && conjK c 22294626 39073281 22294626 5517606))

theorem qConj_walk : walkK 7 qConj 7 0 0 0 = true := by decide +kernel

theorem conj_facts_K (a b x y u w : Perm (Fin 7)) (ha : enc a = 106180641)
    (hb : enc b = 104153616) (hx : enc x = 90391056) (hy : enc y = 70668816)
    (hxy : enc (x * y) = 54878736) (hu : enc u = 39073281) (hw : enc w = 22294626)
    (huw : enc (u * w) = 5517606) : ∀ c : Perm (Fin 7),
    (c * a = a * c →
      (c * x * c⁻¹ = x ∨ c * x * c⁻¹ = y ∨ c * x * c⁻¹ = x * y) ∧
      (c * y * c⁻¹ = x ∨ c * y * c⁻¹ = y ∨ c * y * c⁻¹ = x * y)) ∧
    (c * b = b * c →
      (c * u * c⁻¹ = u ∨ c * u * c⁻¹ = w ∨ c * u * c⁻¹ = u * w) ∧
      (c * w * c⁻¹ = u ∨ c * w * c⁻¹ = w ∨ c * w * c⁻¹ = u * w)) := by
  intro c
  have h := walkK_sound qConj_walk c
  rw [qConj.eq_1, ← ha, ← hb, ← hx, ← hy, ← hxy, ← hu, ← hw, ← huw] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · rcases h1 with h1 | ⟨e1, e2⟩
    · rw [commK_iff.2 hc] at h1
      exact absurd h1 (by decide)
    · exact ⟨conjK_sound e1, conjK_sound e2⟩
  · rcases h2 with h2 | ⟨e1, e2⟩
    · rw [commK_iff.2 hc] at h2
      exact absurd h2 (by decide)
    · exact ⟨conjK_sound e1, conjK_sound e2⟩

end CFSG.LocalAnalysis.GLTheoremB.S7DecideK
