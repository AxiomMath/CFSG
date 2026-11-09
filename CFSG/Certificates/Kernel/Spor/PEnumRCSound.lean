module

public import Certificates.Data.Kernel.Spor.PEnumRC
public import CFSG.Certificates.Kernel.Spor.PEnumRSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KS.PEnumRC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH

variable {n w : Nat}

theorem penumPtRC_spec {m k cnt i : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (h : penumPtRC n w m G GI k cnt T PL POS SRT SRI i = true) :
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      r32 POS (parOf PL i * k + labOf PL i) = i) ∧
    (∀ j < k, r32 POS (i * k + j) < cnt ∧
      T (r32 POS (i * k + j)) = stepK n w m true G GI j (T i)) := by
  unfold penumPtRC at h
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨ht, hpos, -⟩ := h
  refine ⟨fun hi => ?_, fun j hj => ?_⟩
  · have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
    rw [e] at ht
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, CFSG.KS.Raw.Orb.bAnd_eq,
      Bool.and_eq_true, Nat.blt_eq, Nat.mul_eq, Nat.add_eq] at ht
    exact ⟨ht.1, ht.2.1, Nat.eq_of_beq_eq_true ht.2.2.1⟩
  · have hq := CFSG.KS.Raw.Orb.allN_iff.1 hpos j hj
    simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Nat.mul_eq, Nat.add_eq,
      Bool.and_eq_true, Nat.blt_eq] at hq
    exact ⟨hq.1, Nat.eq_of_beq_eq_true hq.2.1⟩

theorem recPtK_spec {m k i : Nat} {G GI T PL : Nat → Nat}
    (h : recPtK n w m G GI k T PL i = true) (hi : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧
      T i = stepK n w m true G GI (labOf PL i) (T (parOf PL i)) := by
  unfold recPtK at h
  have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
  rw [e] at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, Nat.blt_eq] at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h⟩

theorem recMulPtK_spec {m k i : Nat} {GI T PL : Nat → Nat}
    (h : recMulPtK n w m GI k T PL i = true) (hi : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧ T i = pcomp n w m (T (parOf PL i)) (GI (labOf PL i)) := by
  unfold recMulPtK at h
  have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
  rw [e] at h
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bIf_eq, Nat.blt_eq] at h
  split_ifs at h with h1 h2
  exact ⟨h1, h2, Nat.eq_of_beq_eq_true h⟩

theorem penumRC_step {m k cnt i : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hb : ∀ i < cnt, penumPtRC n w m G GI k cnt T PL POS SRT SRI i = true) (hi : i < cnt)
    (hi0 : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧
      T i = stepK n w m true G GI (labOf PL i) (T (parOf PL i)) := by
  obtain ⟨hp, hl, e⟩ := (penumPtRC_spec (hb i hi)).1 hi0
  obtain ⟨-, e'⟩ := (penumPtRC_spec (hb (parOf PL i) (by omega))).2 _ hl
  rw [e] at e'
  exact ⟨hp, hl, e'⟩

theorem penumRC_canon {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (h0 : canonK n w (mask w) (n * w) (T 0) = true)
    (hb : ∀ i < cnt, penumPtRC n w (mask w) G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact h0
    · obtain ⟨hp, hl, e⟩ := penumRC_step hb hi hi0
      rw [e]
      exact CFSG.KC.BfsPin.canonK_pcomp
        (CFSG.KC.BfsPin.canonK_pcomp (hG _ hl) (ih _ hp (by omega))) (hGI _ hl)

theorem penumPtK_of_RC {k cnt : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (h0 : canonK n w (mask w) (n * w) (T 0) = true)
    (hb : ∀ i < cnt, penumPtRC n w (mask w) G GI k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true := by
  have hT := penumRC_canon hG hGI h0 hb
  intro i hi
  have h := hb i hi
  unfold penumPtRC at h
  unfold penumPtK
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hT i hi, ?_, h2, h3⟩
  by_cases hi0 : i = 0
  · subst hi0
    rfl
  · obtain ⟨-, hl, e⟩ := penumRC_step hb hi hi0
    have hpos := ((penumPtRC_spec (hb i hi)).1 hi0).2.2
    have e1 : Nat.beq (r32 POS (Nat.add (Nat.mul (parOf PL i) k) (labOf PL i))) i = true := by
      simp only [Nat.mul_eq, Nat.add_eq]
      rw [hpos, Nat.beq_refl]
    have e2 : Nat.beq (T i) (stepK n w (mask w) true G GI (labOf PL i) (T (parOf PL i))) =
        true := by
      rw [← e, Nat.beq_refl]
    rw [e1] at h1
    rw [e2]
    exact h1

end CFSG.KS.PEnumRC

end
