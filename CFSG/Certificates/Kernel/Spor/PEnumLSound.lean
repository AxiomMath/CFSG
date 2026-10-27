module

public import Certificates.Data.Kernel.Spor.PEnumL
public import CFSG.Certificates.Kernel.Spor.PEnumRSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KS.PEnumL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum

variable {n w : Nat}

theorem penumSlL_spec {m k cnt lo len : Nat} {G T PL POS SRT SRI : Nat → Nat}
    (h : penumSlL n w m G k cnt T PL POS SRT SRI lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → penumPtL n w m G k cnt T PL POS SRT SRI i = true := by
  intro i h1 h2 h3
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  exact h'

theorem penumPtL_spec {m k cnt i : Nat} {G T PL POS SRT SRI : Nat → Nat}
    (h : penumPtL n w m G k cnt T PL POS SRT SRI i = true) :
    (i ≠ 0 → parOf PL i < i ∧ labOf PL i < k ∧
      r32 POS (parOf PL i * k + labOf PL i) = i) ∧
    (∀ j < k, r32 POS (i * k + j) < cnt ∧
      T (r32 POS (i * k + j)) = pcomp n w m (G j) (T i)) := by
  unfold penumPtL at h
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

theorem penumL_step {k cnt i : Nat} {G T PL POS SRT SRI : Nat → Nat}
    (hb : ∀ i < cnt, penumPtL n w (mask w) G k cnt T PL POS SRT SRI i = true) (hi : i < cnt)
    (hi0 : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧
      T i = pcomp n w (mask w) (G (labOf PL i)) (T (parOf PL i)) := by
  obtain ⟨hp, hl, e⟩ := (penumPtL_spec (hb i hi)).1 hi0
  obtain ⟨-, e'⟩ := (penumPtL_spec (hb (parOf PL i) (by omega))).2 _ hl
  rw [e] at e'
  exact ⟨hp, hl, e'⟩

theorem penumL_canon {k cnt cap : Nat} {G T PL POS SRT SRI : Nat → Nat}
    (hsz : szOK n w = true) (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtL n w (mask w) G k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [CFSG.KS.PEnumR.head_zero hh]
      exact (CFSG.KC.BfsPin.PP.id hsz).1
    · obtain ⟨hp, hl, e⟩ := penumL_step hb hi hi0
      rw [e]
      exact CFSG.KC.BfsPin.canonK_pcomp (hG _ hl) (ih _ hp (by omega))

theorem penumPtK_of_L {k cnt cap : Nat} {G GI T PL POS SRT SRI : Nat → Nat}
    (hsz : szOK n w = true) (hG : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (hh : penumHdK (pidn n w) cnt cap T PL = true)
    (hb : ∀ i < cnt, penumPtL n w (mask w) G k cnt T PL POS SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) false G GI k cnt T PL POS SRT SRI i = true := by
  have hT := penumL_canon hsz hG hh hb
  have hstep : ∀ j x, stepK n w (mask w) false G GI j x = pcomp n w (mask w) (G j) x :=
    fun _ _ => rfl
  intro i hi
  have h := hb i hi
  unfold penumPtL at h
  unfold penumPtK
  simp only [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hT i hi, ?_, ?_, h3⟩
  · by_cases hi0 : i = 0
    · subst hi0
      rfl
    · obtain ⟨hp, hl, e⟩ := penumL_step hb hi hi0
      have hpos := ((penumPtL_spec (hb i hi)).1 hi0).2.2
      have e1 : Nat.beq (r32 POS (Nat.add (Nat.mul (parOf PL i) k) (labOf PL i))) i = true := by
        simp only [Nat.mul_eq, Nat.add_eq]
        rw [hpos, Nat.beq_refl]
      have e2 : Nat.beq (T i) (stepK n w (mask w) false G GI (labOf PL i) (T (parOf PL i))) =
          true := by
        rw [hstep, ← e, Nat.beq_refl]
      rw [e1] at h1
      rw [e2]
      exact h1
  · rw [CFSG.KS.Raw.Orb.allN_iff] at h2 ⊢
    intro j hj
    have hq := h2 j hj
    rw [hstep]
    exact hq

end CFSG.KS.PEnumL

end
