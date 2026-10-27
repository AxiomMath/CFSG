module

public import Certificates.Data.Kernel.Spor.PEnumC
public import Certificates.Data.Kernel.Spor.MulHQ
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.J2ModelsSound

public section

namespace CFSG.KS.PEnumC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.Raw.Orb

variable {n w k K cnt : Nat} {G GI S T PL POS CL SRT SRI : Nat → Nat}

theorem bIf_false (t e : Bool) : Bool.rec (motive := fun _ => Bool) e t false = e := rfl

theorem cl_spec (hcl : ∀ c < cnt * K, findPtK cnt T (prodQK n w (mask w) K T S) CL c = true)
    {i j : Nat} (hi : i < cnt) (hj : j < K) :
    r32 CL (i * K + j) < cnt ∧ T (r32 CL (i * K + j)) = pcomp n w (mask w) (T i) (S j) := by
  have hc : i * K + j < cnt * K := by
    have : i * K + K ≤ cnt * K := by
      have := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at this
    omega
  have h := hcl _ hc
  unfold findPtK at h
  rw [strictB_eq, bAnd_eq, Bool.and_eq_true] at h
  have hd : (i * K + j) / K = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hm : (i * K + j) % K = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  refine ⟨Nat.blt_eq.mp h.1, ?_⟩
  have e := Nat.eq_of_beq_eq_true h.2
  rw [e]
  change pcomp n w (mask w) (T ((i * K + j) / K)) (S ((i * K + j) % K)) = _
  rw [hd, hm]

theorem penumPtC_par {i : Nat} (h : penumPtC k K cnt T PL POS CL SRT SRI i = true) (hi : i ≠ 0) :
    parOf PL i < i ∧ labOf PL i < k ∧ r32 CL (parOf PL i * K + labOf PL i) = i := by
  unfold penumPtC at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  have ht := h.1
  have e : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi (Nat.eq_of_beq_eq_true h)
  rw [e] at ht
  simp only [bIf_false, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at ht
  exact ⟨ht.1, ht.2.1, Nat.eq_of_beq_eq_true ht.2.2.1⟩

theorem penumC_canon (hkK : k ≤ K) (hS : ∀ j < k, S j = GI j)
    (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (h0 : canonK n w (mask w) (n * w) (T 0) = true)
    (hcl : ∀ c < cnt * K, findPtK cnt T (prodQK n w (mask w) K T S) CL c = true)
    (hc : ∀ i < cnt, penumPtC k K cnt T PL POS CL SRT SRI i = true) :
    ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact h0
    · obtain ⟨hp, hl, e⟩ := penumPtC_par (hc i hi) hi0
      have hq := (cl_spec hcl (Nat.lt_trans hp hi) (Nat.lt_of_lt_of_le hl hkK)).2
      rw [e, hS _ hl] at hq
      rw [hq]
      exact CFSG.KC.BfsPin.canonK_pcomp (ih _ hp (Nat.lt_trans hp hi)) (hGI _ hl)

theorem penumPtK_of_C (hkK : k ≤ K) (hG : ∀ j < k, G j = pidn n w) (hS : ∀ j < k, S j = GI j)
    (hGI : ∀ j < k, canonK n w (mask w) (n * w) (GI j) = true)
    (h0 : canonK n w (mask w) (n * w) (T 0) = true)
    (hcl : ∀ c < cnt * K, findPtK cnt T (prodQK n w (mask w) K T S) CL c = true)
    (hc : ∀ i < cnt, penumPtC k K cnt T PL POS CL SRT SRI i = true) :
    ∀ i < cnt, penumPtK n w (mask w) (n * w) true G GI k cnt T PL POS SRT SRI i = true := by
  intro i hi
  have hT := penumC_canon hkK hS hGI h0 hcl hc
  have step : ∀ j < k, ∀ x < cnt, stepK n w (mask w) true G GI j (T x) =
      pcomp n w (mask w) (T x) (GI j) := by
    intro j hj x hx
    have e0 : stepK n w (mask w) true G GI j (T x) =
        pcomp n w (mask w) (pcomp n w (mask w) (G j) (T x)) (GI j) := rfl
    rw [e0, hG _ hj, CFSG.KC.J2Models.pcomp_idL (hT x hx)]
  have h := hc i hi
  unfold penumPtC at h
  unfold penumPtK
  rw [strictB_eq, bAnd_eq, hT i hi, Bool.true_and]
  rw [bAnd_eq, Bool.and_eq_true] at h ⊢
  obtain ⟨hpar, hrest⟩ := h
  rw [bAnd_eq, Bool.and_eq_true] at hrest ⊢
  obtain ⟨hpos, hsrt⟩ := hrest
  refine ⟨?_, ?_, hsrt⟩
  · by_cases hi0 : i = 0
    · have e : Nat.beq i 0 = true := Nat.beq_eq.mpr hi0
      rw [e]
    · obtain ⟨hp, hl, e⟩ := penumPtC_par (hc i hi) hi0
      have e' : Nat.beq i 0 = false := Bool.eq_false_iff.2 fun h => hi0 (Nat.eq_of_beq_eq_true h)
      rw [e'] at hpar ⊢
      simp only [bIf_false, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hpar ⊢
      refine ⟨hp, hl, ?_, hpar.2.2.2⟩
      have hq := (cl_spec hcl (Nat.lt_trans hp hi) (Nat.lt_of_lt_of_le hl hkK)).2
      rw [e, hS _ hl] at hq
      rw [step _ hl _ (Nat.lt_trans hp hi), ← hq]
      exact Nat.beq_refl _
  · rw [allN_iff] at hpos ⊢
    intro j hj
    have hq := hpos j hj
    rw [strictB_eq] at hq ⊢
    rw [bAnd_eq, Bool.and_eq_true] at hq ⊢
    obtain ⟨hq1, hq2⟩ := hq
    rw [bAnd_eq, Bool.and_eq_true] at hq2 ⊢
    refine ⟨hq1, ?_, hq2.2⟩
    have e := Nat.eq_of_beq_eq_true hq2.1
    have hc' := (cl_spec hcl hi (Nat.lt_of_lt_of_le hj hkK)).2
    rw [hS _ hj] at hc'
    rw [step _ hj _ hi, e]
    change Nat.beq (T (r32 CL (i * K + j))) (pcomp n w (mask w) (T i) (GI j)) = true
    rw [hc']
    exact Nat.beq_refl _

theorem penumSlC_spec {lo len : Nat} (h : penumSlC k K cnt T PL POS CL SRT SRI lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt → penumPtC k K cnt T PL POS CL SRT SRI i = true := by
  intro i h1 h2 h3
  have h' := allN_iff.1 h (i - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Nat.blt_eq.mpr h3
  rw [hb] at h'
  exact h'

end CFSG.KS.PEnumC

end
