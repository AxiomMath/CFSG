module

public import Certificates.Data.Kernel.Spor.MulHQI
public import Certificates.Data.Kernel.Spor.PEnumC
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PEnumCSound
import CFSG.Certificates.Kernel.Spor.RawSch3FSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb

variable {n w k cnt : Nat} {T G GI CL : Nat → Nat}

theorem bothK_lt' {j : Nat} (h : j < k) : bothK k G GI j = G j := by
  unfold bothK
  rw [CFSG.KS.Raw.Orb.nIf_eq, if_pos (Nat.blt_eq.mpr h)]

theorem bothK_ge' {j : Nat} (h : k ≤ j) : bothK k G GI j = GI (j - k) := by
  have hb : Nat.blt j k = false := by
    cases e : Nat.blt j k
    · rfl
    · have := Nat.blt_eq.mp e
      omega
  unfold bothK
  rw [hb]
  rfl

theorem clH_fwd (h : ∀ c < cnt * (k + k), clHK n w (mask w) k cnt T G GI CL c = true)
    {c : Nat} (hc : c < cnt * (k + k)) (hj : c % (k + k) < k) :
    findPtK cnt T (prodQK n w (mask w) (k + k) T (bothK k G GI)) CL c = true := by
  have h1 := h c hc
  unfold clHK at h1
  have e : Nat.blt (Nat.mod c (Nat.add k k)) k = true := Nat.blt_eq.mpr hj
  rw [e] at h1
  exact h1

theorem clH_at (h : ∀ c < cnt * (k + k), clHK n w (mask w) k cnt T G GI CL c = true)
    {x j : Nat} (hx : x < cnt) (hj : j < k) :
    r32 CL (x * (k + k) + j) < cnt ∧
      T (r32 CL (x * (k + k) + j)) = pcomp n w (mask w) (T x) (G j) := by
  have hK : 0 < k + k := by omega
  have hc : x * (k + k) + j < cnt * (k + k) := by
    have : x * (k + k) + (k + k) ≤ cnt * (k + k) := by
      have := Nat.mul_le_mul_right (k + k) (Nat.succ_le_of_lt hx)
      rwa [Nat.succ_mul] at this
    omega
  have hmod : (x * (k + k) + j) % (k + k) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (x * (k + k) + j) / (k + k) = x := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have h2 := clH_fwd h hc (by rw [hmod]; exact hj)
  unfold findPtK at h2
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h2
  refine ⟨Nat.blt_eq.mp h2.1, ?_⟩
  rw [Nat.eq_of_beq_eq_true h2.2]
  change pcomp n w (mask w) (T ((x * (k + k) + j) / (k + k)))
    (bothK k G GI ((x * (k + k) + j) % (k + k))) = _
  rw [hdiv, hmod, bothK_lt' hj]

theorem clH_canon {PL POS SRT SRI : Nat → Nat}
    (hGc : ∀ j < k, canonK n w (mask w) (n * w) (G j) = true)
    (h0 : canonK n w (mask w) (n * w) (T 0) = true)
    (h : ∀ c < cnt * (k + k), clHK n w (mask w) k cnt T G GI CL c = true)
    (hc : ∀ i < cnt, CFSG.KS.PEnumC.penumPtC k (k + k) cnt T PL POS CL SRT SRI i = true) :
    ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi
    by_cases hi0 : i = 0
    · subst hi0
      exact h0
    · obtain ⟨hp, hl, e⟩ := CFSG.KS.PEnumC.penumPtC_par (hc i hi) hi0
      have hq := (clH_at h (Nat.lt_trans hp hi) hl).2
      rw [e] at hq
      rw [hq]
      exact CFSG.KC.BfsPin.canonK_pcomp (ih _ hp (Nat.lt_trans hp hi)) (hGc _ hl)

theorem findPt_of_clH (hT : ∀ i < cnt, canonK n w (mask w) (n * w) (T i) = true)
    (hGI : ∀ j < k, invEqK n w (mask w) (n * w) (G j) (GI j) = true)
    (h : ∀ c < cnt * (k + k), clHK n w (mask w) k cnt T G GI CL c = true) :
    ∀ c < cnt * (k + k),
      findPtK cnt T (prodQK n w (mask w) (k + k) T (bothK k G GI)) CL c = true := by
  intro c hc
  by_cases hj : c % (k + k) < k
  · exact clH_fwd h hc hj
  · have h1 := h c hc
    unfold clHK at h1
    have e : Nat.blt (Nat.mod c (Nat.add k k)) k = false := by
      cases e' : Nat.blt (Nat.mod c (Nat.add k k)) k
      · rfl
      · exact absurd (Nat.blt_eq.mp e') hj
    rw [e] at h1
    unfold invIxK at h1
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h1
    obtain ⟨hq, hb⟩ := h1
    have hq' : r32 CL c < cnt := Nat.blt_eq.mp hq
    have hK : 0 < k + k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        rw [Nat.add_zero, Nat.mul_zero] at hc
        exact absurd hc (Nat.not_lt_zero _)
      · omega
    have hjk : c % (k + k) - k < k := by
      have := Nat.mod_lt c hK
      omega
    have hpos : r32 CL (r32 CL c * (k + k) + (c % (k + k) - k)) = c / (k + k) :=
      Nat.eq_of_beq_eq_true hb
    have hTi := (clH_at h hq' hjk).2
    rw [hpos] at hTi
    unfold findPtK
    rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true]
    refine ⟨hq, ?_⟩
    have hQ : prodQK n w (mask w) (k + k) T (bothK k G GI) c =
        pcomp n w (mask w) (pcomp n w (mask w) (T (r32 CL c)) (G (c % (k + k) - k)))
          (GI (c % (k + k) - k)) := by
      change pcomp n w (mask w) (T (c / (k + k))) (bothK k G GI (c % (k + k))) = _
      rw [hTi, bothK_ge' (j := c % (k + k)) (by omega)]
    rw [hQ]
    obtain ⟨hn, hw, hT0, -⟩ := CFSG.KS.PF.canon_facts (hT _ hq')
    have hn32 : n < 2 ^ 32 := by omega
    have hpr := permOK_right (hGI _ hjk)
    have eq : T (r32 CL c) = pcomp n w (mask w)
        (pcomp n w (mask w) (T (r32 CL c)) (G (c % (k + k) - k))) (GI (c % (k + k) - k)) := by
      refine CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hT0
        (CFSG.KS.PF.pcomp_shr _ _ hn32 (CFSG.KS.PF.w_pos hw)) fun i hi => ?_
      rw [CFSG.KS.PF.pg_pcomp hn32 hi, CFSG.KS.PF.pg_pcomp hn32 (hpr i hi).1, (hpr i hi).2]
    rw [← eq]
    exact Nat.beq_refl _

end CFSG.KS.MulH

end
