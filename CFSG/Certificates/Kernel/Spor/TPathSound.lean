module

public import Certificates.Data.Kernel.Spor.TPath
public import Certificates.Data.CFSGNative.Perm.Path
public import CFSG.Certificates.Kernel.Spor.TBfsSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.TBfs

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.Perm.Native CFSG.Sporadic.Th.Native

structure PathPt (n r : Nat) (L : Nat → Nat → Nat) (LV : Nat → Nat)
    (PTS POS PAR LAB TI : Nat → Nat) (k : Nat) : Prop where
  lt : r32 PTS k < n
  pos : r32 POS (r32 PTS k) = k
  tree : 0 < k → r32 PAR k < k ∧ r32 TI k < r ∧ r32 LAB k = LV (r32 TI k) ∧
    L (LV (r32 TI k)) (r32 PTS (r32 PAR k)) = r32 PTS k

theorem pathPt_spec {n r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {k : Nat}
    (h : tpathPtK n r L LV PTS POS PAR LAB TI k = true) :
    PathPt n r L LV PTS POS PAR LAB TI k := by
  unfold tpathPtK at h
  rw [Raw.Orb.strictB_eq] at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, ht⟩ := h
  refine ⟨by simpa [Nat.blt_eq] using h1, by simpa [Nat.beq_eq] using h2, fun hk => ?_⟩
  have e : Nat.beq k 0 = false :=
    Bool.eq_false_iff.2 fun h => (Nat.pos_iff_ne_zero.1 hk) (Nat.eq_of_beq_eq_true h)
  rw [Raw.Orb.bIf_eq, e, ite_eq_right (by decide), Raw.Orb.strictB_eq, Raw.Orb.strictB_eq] at ht
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at ht
  exact ht

theorem tpathSl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tpathSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tpathPtK n r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := Raw.Orb.allN_iff.1 h (k - lo) (by omega)
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem tpathK_sound {n root cnt r : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} {letters : Array Table} {lv : Array Nat}
    (hlv : lv.size = r ∧ ∀ t < r, lv[t]! = LV t ∧ LV t < letters.size ∧
      ∀ x < n, ap letters[LV t]! x = L (LV t) x)
    (hh : tpathHdK root cnt PTS = true)
    (hp : ∀ k < cnt, tpathPtK n r L LV PTS POS PAR LAB TI k = true) :
    orbPathOK n root (tbfsRec n cnt PTS POS PAR LAB) letters lv = true := by
  unfold tpathHdK at hh
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hh
  obtain ⟨hc, hr⟩ := hh
  unfold Perm.Native.orbPathOK orbPathAt
  simp only [tbfsRec, Array.size_ofFn, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨hc, by rw [ap_ofFn hc, hr]⟩, ?_⟩
  rw [allIn_iff]
  intro k hk
  have P := pathPt_spec (hp k hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  simp only [ap_ofFn hk, ap_ofFn P.lt, P.pos]
  refine ⟨⟨decide_eq_true P.lt, trivial⟩, ?_⟩
  by_cases h0 : k = 0
  · exact Or.inl h0
  · right
    obtain ⟨a1, a2, a3, a4⟩ := P.tree (by omega)
    obtain ⟨hlvt, -, hap⟩ := hlv.2 _ a2
    have hpa : r32 PAR k < cnt := by omega
    rw [ap_ofFn hpa, a3, hap _ (pathPt_spec (hp _ hpa)).lt, a4]
    refine ⟨⟨decide_eq_true a1, ?_⟩, rfl⟩
    have hs : r32 TI k < lv.size := by
      rw [hlv.1]
      exact a2
    rw [Array.contains_iff_mem, ← hlvt, getElem!_pos lv _ hs]
    exact Array.getElem_mem hs

end CFSG.KS.TBfs

end
