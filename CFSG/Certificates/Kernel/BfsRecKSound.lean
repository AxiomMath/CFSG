module

public import Certificates.Data.Kernel.BfsRecK
public import CFSG.Certificates.Kernel.Spor.KeyBfsGen
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.BfsRecK

open CFSG.KS.KeyBfsG CFSG.KC.Enum

private theorem beqT {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

private theorem bltT {a b : Nat} (h : Nat.blt a b = true) : a < b := by
  simpa [Nat.blt_eq] using h

private theorem bleT {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem key_mono {cnt : Nat} {K sig : Nat → Nat}
    (h : ∀ j, j + 1 < cnt → K (sig j) < K (sig (j + 1))) :
    ∀ b a, a < b → b < cnt → K (sig a) < K (sig b) := by
  intro b
  induction b with
  | zero => intro a hab; omega
  | succ b ih =>
    intro a hab hb
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
    · exact lt_trans (ih a h1 (by omega)) (h b hb)
    · subst h1
      exact h a hb

theorem grec_of_recOK {α : Type} {κ : α → Nat} (hκ : Function.Injective κ)
    {st : Nat → α → α} {k cnt : Nat} {root : α} {T : Nat → α} {P L POS K sig sinv : Nat → Nat}
    {stEq : Nat → Nat → Nat → Bool} (hk : 0 < k) (hcnt : 0 < cnt) (hroot : T 0 = root)
    (hst : ∀ l < k, ∀ i < cnt, ∀ j < cnt, stEq l i j = true → st l (T i) = T j)
    (hK : ∀ a b, T a = T b → K a = K b)
    (h : recOK k cnt P L POS K sig sinv stEq = true) :
    GRec κ st k root (κ root) cnt (k * cnt) T P L POS := by
  unfold recOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hp0, hl0⟩, htree⟩, hord⟩, hclose⟩, hsig⟩ := h
  have htree' := CFSG.KS.allN_spec htree
  have hord' := CFSG.KS.allN_spec hord
  have hclose' := CFSG.KS.allN_spec hclose
  have hsig' := CFSG.KS.allN_spec hsig
  have sg : ∀ j < cnt, sig j < cnt ∧ sinv (sig j) = j ∧ sinv j < cnt ∧ sig (sinv j) = j ∧
      (j + 1 < cnt → K (sig j) < K (sig (j + 1))) := by
    intro j hj
    have e := hsig' j hj
    simp only [Bool.and_eq_true, Bool.or_eq_true] at e
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := e
    refine ⟨bltT a1, beqT a2, bltT a3, beqT a4, fun hj1 => ?_⟩
    rcases a5 with a5 | a5
    · have : Nat.blt (j + 1) cnt = true := by simpa [Nat.blt_eq] using hj1
      rw [this] at a5
      exact absurd a5 (by decide)
    · exact bltT a5
  have mono := key_mono (cnt := cnt) (K := K) (sig := sig) fun j hj => (sg j (by omega)).2.2.2.2 hj
  refine ⟨hk, hcnt, hroot, rfl, beqT hp0, beqT hl0, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb e
    have hab : K a = K b := hK a b (hκ e)
    obtain ⟨-, -, sa, ea, -⟩ := sg a ha
    obtain ⟨-, -, sb, eb, -⟩ := sg b hb
    rcases Nat.lt_trichotomy (sinv a) (sinv b) with hlt | heq | hgt
    · have := mono (sinv b) (sinv a) hlt sb
      rw [ea, eb] at this
      omega
    · rw [← ea, ← eb, heq]
    · have := mono (sinv a) (sinv b) hgt sa
      rw [ea, eb] at this
      omega
  · intro i hi0 hi
    have e := htree' i hi
    simp only [Bool.and_eq_true, Bool.or_eq_true] at e
    rcases e with e | ⟨⟨e1, e2⟩, e3⟩
    · exact absurd (beqT e) (by omega)
    · exact ⟨bltT e1, bltT e2, (hst _ (bltT e2) _ (by have := bltT e1; omega) _ hi e3).symm⟩
  · intro i hi0 hi
    have e := hord' i (by omega)
    simp only [Bool.or_eq_true] at e
    rcases e with (e | e) | e
    · exact absurd (beqT e) (by omega)
    · have : Nat.blt (i + 1) cnt = true := by simpa [Nat.blt_eq] using hi
      rw [this] at e
      exact absurd e (by decide)
    · exact bltT e
  · have hc1 : cnt - 1 < cnt := by omega
    rcases Nat.eq_zero_or_pos (cnt - 1) with h0 | h0
    · rw [h0, beqT hp0, beqT hl0, Nat.mul_zero, Nat.add_zero]
      exact Nat.mul_pos hk hcnt
    · have e := htree' (cnt - 1) hc1
      simp only [Bool.and_eq_true, Bool.or_eq_true] at e
      rcases e with e | ⟨⟨e1, e2⟩, -⟩
      · exact absurd (beqT e) (by omega)
      · have h1 := bltT e1
        have h2 := bltT e2
        have : k * P (cnt - 1) + L (cnt - 1) < k * (P (cnt - 1) + 1) := by
          rw [Nat.mul_succ]
          omega
        have h3 : k * (P (cnt - 1) + 1) ≤ k * cnt := Nat.mul_le_mul_left k (by omega)
        omega
  · intro e he
    have c := hclose' e he
    simp only [Bool.and_eq_true, Bool.or_eq_true] at c
    obtain ⟨⟨c1, c2⟩, c3⟩ := c
    have hek : e / k < cnt := by
      rw [Nat.div_lt_iff_lt_mul hk]
      rw [Nat.mul_comm] at he
      exact he
    refine ⟨bltT c1, congrArg κ (hst _ (Nat.mod_lt _ hk) _ hek _ (bltT c1) c2), ?_⟩
    rcases c3 with c3 | c3
    · exact Or.inl (beqT c3)
    · exact Or.inr (bleT c3)

end CFSG.KC.BfsRecK

end
