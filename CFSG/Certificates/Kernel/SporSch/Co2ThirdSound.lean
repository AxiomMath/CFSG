module

public import Certificates.Data.Kernel.SporSch.Co2Third
public import CFSG.Certificates.Kernel.Spor.RawAgree
public import CFSG.Certificates.Kernel.Spor.EnumBaseSound

public section

namespace CFSG.KS.Co2Third

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.BaseEq CFSG.KS.Raw.Orb CFSG.Monster.B.Co2

theorem cntN_card (n : Nat) (f : Nat → Bool) :
    cntN n f = ((Finset.range n).filter fun i => f i = true).card := by
  rw [CFSG.KS.EnumBase.cntN_eq]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hf : f n = true
    · rw [if_pos hf, Finset.card_insert_of_notMem (by simp)]
      simp [hf]
    · rw [if_neg hf]
      simp [hf]

theorem walkIK_eq {n w m nw kS T R c r : Nat} {S SI : Nat → Nat} {σ : Nat → Equiv.Perm (Fin n)}
    (hσ : ∀ j < r, ∀ x : Fin n, pg w m (invLetterK S SI kS (stAt T j)) x = ((σ j)⁻¹ x : Nat))
    (hR : ∀ k < c, 0 < k → rpar w m nw R k < k ∧ rlab n nw R k < r) :
    ∀ f k, k < c → ∀ z : Fin n, walkIK n w m nw S SI kS T R f k z =
      ((treeF σ (rpar w m nw R) (rlab n nw R) f k)⁻¹ z : Nat) := by
  intro f
  induction f with
  | zero =>
    intro k _ z
    rfl
  | succ f ih =>
    intro k hk z
    change nIf(Nat.beq k (nat_lit 0), (z : Nat), walkIK n w m nw S SI kS T R f (rpar w m nw R k)
      (pg w m (invLetterK S SI kS (stAt T (rlab n nw R k))) z)) = _
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [treeF]
    · obtain ⟨hp, hl⟩ := hR k hk hk0
      have hne : Nat.beq k (nat_lit 0) = false :=
        Bool.eq_false_iff.2 fun e => absurd (Nat.eq_of_beq_eq_true e) (Nat.pos_iff_ne_zero.1 hk0)
      rw [hne, hσ _ hl z]
      change walkIK n w m nw S SI kS T R f (rpar w m nw R k) (((σ (rlab n nw R k))⁻¹ z : Fin n) : Nat) = _
      rw [ih _ (by omega) _]
      simp only [treeF, show k ≠ 0 by omega, ↓reduceIte, mul_inv_rev, Equiv.Perm.mul_apply]

theorem fixList_spec {n w m U cF : Nat} {F : Nat → Nat} (h : fixListK n w m U F cF = true) :
    (∀ i < cF, F i < n ∧ pg w m U (F i) = F i) ∧
      (∀ i, i + 1 < cF → F i < F (i + 1)) ∧
      ((Finset.range n).filter fun z => pg w m U z = z).card = cF := by
  unfold fixListK at h
  rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩
  · have := allN_spec h1 i hi
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
    exact this
  · have := allN_spec h2 i (by change i < cF - 1; omega)
    rwa [Nat.blt_eq] at this
  · rw [Nat.beq_eq, cntN_card] at h3
    simpa [Nat.beq_eq] using h3

theorem inK_iff {O : Nat → Nat} {c z : Nat} : inK O c z = true ↔ ∃ i < c, O i = z := by
  unfold inK
  rw [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, allN_iff]
  push_neg
  simp [Nat.beq_eq]

end CFSG.KS.Co2Third

end
