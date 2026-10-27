module

public import Certificates.Data.Kernel.L34W.Field23200
public import CFSG.Certificates.Kernel.L34W.ModelSound
public import CFSG.Certificates.Kernel.Multipliers.MonoAllR

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum
open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.ComponentClassification.TBLit.L34P

variable {T A : ℕ → ℕ}

theorem strictB_eq23200 (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem fourthM_of (hT : T1Of T) (hb : boundsOK T A = true) {k : ℕ} (hk : k < 64)
    (h : fourthC T k = true) : fourthM k = (0, 0, 0) ∨ fourthM k = (0, 2, 0) := by
  have hx : 16 * k < 1024 := by omega
  have hs := mulC_lt hb hx hx
  have hf : fourthM k = dec (mulC T (mulC T (16 * k) (16 * k)) (mulC T (16 * k) (16 * k))) := by
    rw [dec_mulC hT hs hs, dec_mulC hT hx hx, dec_sixteen, fourthM]
  simp only [fourthC, strictB_eq23200, Bool.or_eq_true, Nat.beq_eq] at h
  rw [hf]
  rcases h with h | h
  · rw [h]
    exact Or.inl rfl
  · rw [h]
    exact Or.inr rfl

theorem l34pFieldOK_of (hT : T1Of T) (hA : AlOf A) (hb : boundsOK T A = true)
    (h1 : alphaZK A = true) (h2 : fieldK T = true) : l34pFieldOK = true := by
  rw [l34pFieldOK, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [alphaZOK, hA 1 64 (by omega) (by omega), hA 1 65 (by omega) (by omega)]
    exact h1
  · rw [fourthOK, allBelow_eq_true]
    intro k hk
    have h3 := CFSG.Certificates.Mono.allR_spec h2 k (Nat.zero_le k) (by omega)
    cases hc : (comp 42 (wordTab (tg k)) r₂T == comp 42 r₂T (wordTab (tg k)))
    · rfl
    · rw [hc, Bool.not_true, Bool.false_or] at h3
      rw [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]
      exact fourthM_of hT hb hk h3

end CFSG.KC.L34W

end
