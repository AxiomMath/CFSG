
module

public import Certificates.Data.Kernel.L34Scan2
public import CFSG.Certificates.Kernel.L34W.Tab42Sound
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Scan2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34W CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

theorem ex_of_notB_allN {n : Nat} {f : Nat → Bool} (h : CFSG.KLie.CT.notB (allN n f) = true) :
    ∃ k < n, f k = false := by
  rw [notB_iff] at h
  by_contra hc
  push Not at hc
  have : allN n f = true := CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => by
    have := hc k hk
    cases e : f k
    · exact absurd e this
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem memL_spec {N x : Nat} {T : Nat → Nat} (h : memL N T x = true) : ∃ q < N, T q = x := by
  obtain ⟨q, hq, h'⟩ := ex_of_notB_allN h
  refine ⟨q, hq, Nat.eq_of_beq_eq_true ?_⟩
  cases e : Nat.beq (T q) x
  · rw [e] at h'
    exact absurd h' (by decide)
  · rfl

theorem found_of_memL {N x : Nat} {T : Nat → Nat} (h : memL N T x = true) :
    found (indexOf (pts 42 6 N T)) (pts 42 6 N T) (unpack 42 6 x) = true := by
  obtain ⟨q, hq, e⟩ := memL_spec h
  unfold pts
  exact found_pts hq e

theorem ppowK_succ (x k : Nat) : ppowK x (k + 1) = pcomp 42 6 (mask 6) (ppowK x k) x := rfl

theorem ppowK_spec {x : Nat} (hx : Cn x) (P : Nat → Tab) (h0 : P 0 = idTab 42)
    (hs : ∀ k, P (k + 1) = comp 42 (P k) (unpack 42 6 x)) :
    ∀ k, Cn (ppowK x k) ∧ P k = unpack 42 6 (ppowK x k)
  | 0 => ⟨cn_pidn, h0.trans idTab42⟩
  | k + 1 => by
    obtain ⟨c, e⟩ := ppowK_spec hx P h0 hs k
    rw [hs, e, comp_unpack' c hx, ppowK_succ]
    exact ⟨canonK_pcomp c hx, rfl⟩

theorem wordK_eq {G : Nat → Nat} (hG : GensG G) (w : List Nat) :
    Cn (pword (gS G) w (pidn 42 6)) ∧ wordTab w = unpack 42 6 (pword (gS G) w (pidn 42 6)) := by
  unfold wordTab
  rw [idTab42]
  exact pword_spec (gS G) genT w _ cn_pidn fun j _ => genT_gS hG j

theorem ncomm_of {x g : Nat} (hx : Cn x) (hg : Cn g) (h : CFSG.KLie.CT.notB (commPt 42 6 x g) = true) :
    (!(comp 42 (unpack 42 6 x) (unpack 42 6 g) == comp 42 (unpack 42 6 g) (unpack 42 6 x))) =
      true := by
  cases hb : (comp 42 (unpack 42 6 x) (unpack 42 6 g) == comp 42 (unpack 42 6 g) (unpack 42 6 x))
  · rfl
  · rw [notB_iff, (commPt_iff hx hg).2 (beq_iff_eq.1 hb)] at h
    exact absurd h (by decide)

theorem nbeq_of {p q : Nat} (hp : Cn p) (hq : Cn q) (h : CFSG.KLie.CT.notB (Nat.beq p q) = true) :
    (!(unpack 42 6 p == unpack 42 6 q)) = true := by
  rw [beq_unpack hp hq, notB_iff.1 h]
  rfl

theorem mem_pts {N : Nat} {T : Nat → Nat} {x : Tab} (hx : x ∈ (pts 42 6 N T).toList) :
    ∃ i < N, x = unpack 42 6 (T i) := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hx
  obtain ⟨i, hi, e⟩ := hx
  have hi' : i < N := by rwa [size_pts] at hi
  exact ⟨i, hi', by rw [← e, CFSG.KC.L34Scan.pts_getElem hi']⟩

theorem pts_mem {N i : Nat} {T : Nat → Nat} (hi : i < N) :
    unpack 42 6 (T i) ∈ (pts 42 6 N T).toList := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem]
  exact ⟨i, by rw [size_pts]; exact hi, CFSG.KC.L34Scan.pts_getElem hi⟩

theorem pts_toList_all {N : Nat} {T : Nat → Nat} {f : Tab → Bool}
    (h : ∀ i < N, f (unpack 42 6 (T i)) = true) : (pts 42 6 N T).toList.all f = true :=
  List.all_eq_true.2 fun x hx => by
    obtain ⟨i, hi, rfl⟩ := mem_pts hx
    exact h i hi

theorem pts_toList_any {N : Nat} {T : Nat → Nat} {f : Tab → Bool}
    (h : ∃ i < N, f (unpack 42 6 (T i)) = true) : (pts 42 6 N T).toList.any f = true := by
  obtain ⟨i, hi, e⟩ := h
  exact List.any_eq_true.2 ⟨_, pts_mem hi, e⟩

theorem pts_all {N : Nat} {T : Nat → Nat} {f : Tab → Bool}
    (h : ∀ i < N, f (unpack 42 6 (T i)) = true) : (pts 42 6 N T).all f = true := by
  rw [← Array.all_toList]
  exact pts_toList_all h

end CFSG.KC.L34Scan2

end
