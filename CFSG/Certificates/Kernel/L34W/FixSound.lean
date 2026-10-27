
module

public import Certificates.Data.Kernel.L34W.Fix
public import CFSG.Certificates.Kernel.L34W.ModKSound
public import CFSG.Certificates.Kernel.L34W.OuterSound

public section

namespace CFSG.KC.L34W

open CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.GrSLit.L34Facts.Real CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

variable {T A : ℕ → ℕ}

theorem betaK_eq (b i x : ℕ) : betaK A b i x =
    mk (pg 10 (mask 10) b (x / 16) / 16)
      (pg 10 (mask 10) b (x / 16) / 4 % 4 + (x / 4 % 4 * (ent A i 64 % 48 / 12) +
        x % 4 * (ent A i 65 % 48 / 12)))
      (pg 10 (mask 10) b (x / 16) % 4 + (x / 4 % 4 * (ent A i 64 % 12 / 3) +
        x % 4 * (ent A i 65 % 12 / 3))) := by
  unfold betaK
  simp only [strictN_eq']
  rfl

@[expose] def BRow (b t i : ℕ) : Prop := ∀ k < 64, dec (pg 10 (mask 10) b k) = betaYM t i (k, 0, 0)

theorem dec_betaK (hA : AlOf A) {b t i : ℕ} (hb : BRow b t i) (hi : i < 36) {x : ℕ}
    (hx : x < 1024) : dec (betaK A b i x) = betaYM t i (dec x) := by
  have e : dec x = (x / 16, ((x / 4 % 4 : ℕ) : ZMod 4), ((x % 4 : ℕ) : ZMod 4)) := rfl
  rw [betaK_eq, dec_mk, e, betaYM_ctr, ← hb (x / 16) (by omega), hA i 64 hi (by norm_num),
    hA i 65 hi (by norm_num)]
  simp only [dec, quad]
  push_cast
  rfl

theorem fixC_eq (hA : AlOf A) {b t i : ℕ} (hb : BRow b t i) (hi : i < 36) (m : ℕ) {x : ℕ}
    (hx : x < 1024) : fixC A b i m x = fixKB (kbOfMask m) t i (dec x) := by
  unfold fixC fixKB
  rw [eqC_eq, dec_betaK hA hb hi hx]

theorem bIf_iff {c x y : Bool} : bIf(c, x, y) = true ↔ (c = true ∧ x = true) ∨ (c = false ∧ y = true) := by
  cases c <;> simp

theorem d1W_spec (hT : T1Of T) (hA : AlOf A) {m i b i' b' t t' x y : ℕ} (hb : BRow b t i)
    (hb' : BRow b' t' i') (hi : i < 36) (hi' : i' < 36) (h : d1W T A m i b i' b' x y = true) :
    ∃ a ∈ allM, ∃ c ∈ allM, eqKB (kbOfMask m) c a = false ∧
      fixKB (kbOfMask m) t i a = true ∧ fixKB (kbOfMask m) t' i' a = true ∧
      isInvKB (kbOfMask m) a = true ∧ fixKB (kbOfMask m) t i c = true ∧
      fixKB (kbOfMask m) t' i' c = true ∧ isInvKB (kbOfMask m) c = true := by
  unfold d1W at h
  simp only [bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hx, hy⟩, hne⟩, ⟨⟨f1, f2⟩, f3⟩, ⟨g1, g2⟩, g3⟩ := h
  have hx' := Nat.blt_eq.mp hx
  have hy' := Nat.blt_eq.mp hy
  refine ⟨dec x, dec_mem_allM hx', dec y, dec_mem_allM hy', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eqC_eq] at hne
    exact hne
  · rw [fixC_eq hA hb hi m hx'] at f1
    exact f1
  · rw [fixC_eq hA hb' hi' m hx'] at f2
    exact f2
  · rw [isInvC_eq hT m hx'] at f3
    exact f3
  · rw [fixC_eq hA hb hi m hy'] at g1
    exact g1
  · rw [fixC_eq hA hb' hi' m hy'] at g2
    exact g2
  · rw [isInvC_eq hT m hy'] at g3
    exact g3

@[expose] def DProp (kb : List Bool) (t i k : ℕ) (x : MElt) : Prop :=
  x ∈ allM ∧ fixKB kb t i x = true ∧ isInvKB kb x = true ∧
    eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true

theorem dP_spec (hT : T1Of T) (hA : AlOf A) {m i b t k x : ℕ} (hb : BRow b t i) (hi : i < 36)
    (hk : k < 64) (h : dP T A m i b k x = true) : x < 1024 ∧ DProp (kbOfMask m) t i k (dec x) := by
  unfold dP at h
  simp only [bAnd_iff] at h
  obtain ⟨⟨hx, hf⟩, hv, hc⟩ := h
  have hx' := Nat.blt_eq.mp hx
  refine ⟨hx', dec_mem_allM hx', ?_, ?_, ?_⟩
  · rw [fixC_eq hA hb hi m hx'] at hf
    exact hf
  · rw [isInvC_eq hT m hx'] at hv
    exact hv
  · have e : Nat.mul 16 k = 16 * k := rfl
    rw [e, commC_eq hT m hx' (by omega), dec_sixteen] at hc
    exact hc

theorem dist3_spec {m x y z : ℕ} (h : dist3 m x y z = true) :
    eqKB (kbOfMask m) (dec y) (dec x) = false ∧ eqKB (kbOfMask m) (dec z) (dec x) = false ∧
      eqKB (kbOfMask m) (dec z) (dec y) = false := by
  unfold dist3 at h
  simp only [bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
  rw [eqC_eq, eqC_eq, eqC_eq] at h
  exact h

theorem mask_facts : ∀ q < 15, expType (kbOfMask (kbMasks.getD q 0)) = exK q ∧
    (hasBit cycMask q = true →
      kbZero (kbOfMask (kbMasks.getD q 0)) = true ∨ kbCyc (kbOfMask (kbMasks.getD q 0)) = true) ∧
    (q = 14 → kbFull (kbOfMask (kbMasks.getD q 0)) = true) := by
  decide +kernel

theorem dW_spec (hT : T1Of T) (hA : AlOf A) {q i b t ty k w : ℕ} (hb : BRow b t i) (hi : i < 36)
    (hk64 : k < 64) (hq : q < 15) (hty : typeOf t i = ty)
    (h : dW T A (kbMasks.getD q 0) q i b ty k w = true) :
    let kb := kbOfMask (kbMasks.getD q 0)
    (∃ x, DProp kb t i k x ∧ x.1 ≠ 0 ∧ x.1 ≠ k) ∨
      (∃ a b c d, DProp kb t i k a ∧ DProp kb t i k b ∧ DProp kb t i k c ∧ DProp kb t i k d ∧
        eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false ∧
        eqKB kb d a = false ∧ eqKB kb d b = false ∧ eqKB kb d c = false) ∨
      (k ≠ 0 ∧ typeOf t i = expType kb ∧ (kbZero kb = true ∨ kbCyc kb = true) ∧
        (kbFull kb = true ∨ ∃ a b c, DProp kb t i k a ∧ DProp kb t i k b ∧ DProp kb t i k c ∧
          eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false)) := by
  intro kb
  obtain ⟨hex, hcy, hfu⟩ := mask_facts q hq
  unfold dW at h
  simp only [strictB_eq] at h
  generalize pg 10 (mask 10) w 0 = tag at h
  generalize pg 10 (mask 10) w 1 = x at h
  generalize pg 10 (mask 10) w 2 = y at h
  generalize pg 10 (mask 10) w 3 = z at h
  generalize pg 10 (mask 10) w 4 = u at h
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
    obtain ⟨hp, h0, hk⟩ := h
    obtain ⟨-, hx⟩ := dP_spec hT hA hb hi hk64 hp
    exact Or.inl ⟨dec x, hx, Nat.ne_of_beq_eq_false h0, Nat.ne_of_beq_eq_false hk⟩
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨p1, p2⟩, p3, p4⟩, hd, e1, e2, e3⟩ := h
    obtain ⟨d1, d2, d3⟩ := dist3_spec hd
    rw [eqC_eq] at e1 e2 e3
    exact Or.inr (Or.inl ⟨dec x, dec y, dec z, dec u, (dP_spec hT hA hb hi hk64 p1).2,
      (dP_spec hT hA hb hi hk64 p2).2, (dP_spec hT hA hb hi hk64 p3).2,
      (dP_spec hT hA hb hi hk64 p4).2, d1, d2, d3, e1, e2, e3⟩)
  rcases bIf_iff.1 h with ⟨-, h⟩ | ⟨-, h⟩
  · simp only [bAnd_iff, bNot_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hk0, hty'⟩, hc, hr⟩ := h
    refine Or.inr (Or.inr ⟨fun e => ?_, ?_, hcy hc, ?_⟩)
    · subst e
      exact absurd hk0 (by decide)
    · exact hty.trans ((Nat.eq_of_beq_eq_true hty').trans hex.symm)
    · rcases bIf_iff.1 hr with ⟨h14, -⟩ | ⟨-, h3⟩
      · exact Or.inl (hfu (Nat.eq_of_beq_eq_true h14))
      · simp only [bAnd_iff] at h3
        obtain ⟨⟨p1, p2⟩, p3, hd⟩ := h3
        obtain ⟨d1, d2, d3⟩ := dist3_spec hd
        exact Or.inr ⟨dec x, dec y, dec z, (dP_spec hT hA hb hi hk64 p1).2,
          (dP_spec hT hA hb hi hk64 p2).2, (dP_spec hT hA hb hi hk64 p3).2, d1, d2, d3⟩
  · exact absurd h (by decide)

theorem liftsKB_eq (hA : AlOf A) (kb : List Bool) {i : ℕ} (hi : i < 36) :
    liftsKB kb i = liftsQ kb (ent A i 64) (ent A i 65) := by
  unfold liftsKB liftsQ
  rw [hA i 64 hi (by norm_num), hA i 65 hi (by norm_num)]

end CFSG.KC.L34W

end
