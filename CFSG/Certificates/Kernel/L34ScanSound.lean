module

public import Certificates.Data.Kernel.L34Scan
public import CFSG.Certificates.Kernel.L34KSound
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34CertInputs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4FixL34Inputs
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB)

theorem strictB_app (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem scanSl_spec {f : Nat → Bool} {T : Nat → Nat} {L K N : Nat} (hN : N = L * K) (hL : 0 < L)
    (h : ∀ s < K, scanSl f T L s = true) : ∀ i < N, f (T i) = true := by
  intro i hi
  have hs : i / L < K := by
    rw [hN] at hi
    exact (Nat.div_lt_iff_lt_mul hL).2 (by rw [Nat.mul_comm]; exact hi)
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 (h (i / L) hs) (i % L) (Nat.mod_lt _ hL)
  rw [strictB_app] at h'
  have e : Nat.add (Nat.mul L (i / L)) (i % L) = i := Nat.div_add_mod i L
  rw [e] at h'
  exact h'

variable {n w : Nat}

theorem pow2K_succ (k x : Nat) :
    pow2K n w (k + 1) x = pcomp n w (mask w) (pow2K n w k x) (pow2K n w k x) := rfl

theorem pow2K_canon {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    ∀ k, canonK n w (mask w) (n * w) (pow2K n w k x) = true
  | 0 => hx
  | k + 1 => by
    rw [pow2K_succ]
    exact canonK_pcomp (pow2K_canon hx k) (pow2K_canon hx k)

theorem pow2K_unpack {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    ∀ k, unpack n w (pow2K n w k x) = (fun t => comp n t t)^[k] (unpack n w x)
  | 0 => rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply', ← pow2K_unpack hx k, pow2K_succ,
      comp_unpack' (pow2K_canon hx k) (pow2K_canon hx k)]

theorem commAll_eq {x m : Nat} {CP : Nat → Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hc : ∀ c < m, canonK n w (mask w) (n * w) (CP c) = true) :
    (allBelow m fun c => comp n (unpack n w x) (unpack n w (CP c)) ==
      comp n (unpack n w (CP c)) (unpack n w x)) = allN m fun c => commPt n w x (CP c) := by
  rw [Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff, CFSG.KS.Raw.Orb.allN_iff]
  refine forall_congr' fun c => imp_congr_right fun hcm => ?_
  rw [beq_iff_eq, commPt_iff hx (hc c hcm)]

theorem powTwoTab_unpack {x : Nat} (hx : canonK 42 6 (mask 6) (42 * 6) x = true) :
    ∀ k, CFSG.ComponentClassification.GrSLit.powTwoTab (unpack 42 6 x) k =
      unpack 42 6 (pow2K 42 6 k x)
  | 0 => rfl
  | k + 1 => by
    rw [pow2K_succ, ← comp_unpack' (pow2K_canon hx k) (pow2K_canon hx k), ← powTwoTab_unpack hx k]
    rfl

theorem pow256T_unpack {x : Nat} (hx : canonK 42 6 (mask 6) (42 * 6) x = true) :
    CFSG.ComponentClassification.CatFactsL4U4.pow256T (unpack 42 6 x) =
      unpack 42 6 (pow2K 42 6 8 x) := by
  rw [pow2K_unpack hx]
  rfl

theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl

theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem hsz42 : szOK 42 6 = true := by decide

theorem pts_get' {N i : Nat} {T : Nat → Nat} (hi : i < N) :
    (pts n w N T)[i]! = unpack n w (T i) := by
  unfold pts
  exact pts_get hi

theorem pts_getElem {N i : Nat} {T : Nat → Nat} (hi : i < N) :
    (pts n w N T)[i]'(by rw [size_pts]; exact hi) = unpack n w (T i) :=
  Array.getElem_ofFn ..

theorem twoCentralOK_of {N m : Nat} {T CP : Nat → Nat}
    (hT : ∀ i < N, canonK 42 6 (mask 6) (42 * 6) (T i) = true)
    (hc : ∀ c < m, canonK 42 6 (mask 6) (42 * 6) (CP c) = true)
    (h : ∀ i < N, twoK 42 6 m CP (pidn 42 6) (T i) = true) :
    CFSG.ComponentClassification.GrSLit.twoCentralOK (pts 42 6 N T) (pts 42 6 m CP) = true := by
  unfold CFSG.ComponentClassification.GrSLit.twoCentralOK
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := hT i hi
  have e1 : (allBelow (pts 42 6 m CP).size fun j =>
      comp 42 (pts 42 6 N T)[i]! (pts 42 6 m CP)[j]! ==
        comp 42 (pts 42 6 m CP)[j]! (pts 42 6 N T)[i]!) =
      allBelow m fun c => comp 42 (unpack 42 6 (T i)) (unpack 42 6 (CP c)) ==
        comp 42 (unpack 42 6 (CP c)) (unpack 42 6 (T i)) := by
    rw [size_pts, Bool.eq_iff_iff, CFSG.KS.BfsReplay.allBelow_iff,
      CFSG.KS.BfsReplay.allBelow_iff]
    refine forall_congr' fun c => imp_congr_right fun hcm => ?_
    rw [pts_get' hi, pts_get' hcm]
  rw [e1, commAll_eq hx hc, pts_get' hi, powTwoTab_unpack hx, idTab_unpack' hsz42,
    beq_unpack (pow2K_canon hx 8) (canon_pidn hsz42)]
  have h' := h i hi
  unfold twoK at h'
  rwa [orB_eq, notB_eq] at h'

theorem fixCheck_of {N m r : Nat} {T CP : Nat → Nat}
    (hT : ∀ i < N, canonK 42 6 (mask 6) (42 * 6) (T i) = true)
    (hc : ∀ c < m, canonK 42 6 (mask 6) (42 * 6) (CP c) = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true)
    (h : ∀ i < N, fixK 42 6 r m CP (pidn 42 6) (T i) = true) :
    CFSG.ComponentClassification.CatFactsL4U4.fixCheck (pts 42 6 N T) (pts 42 6 m CP)
      (unpack 42 6 r) = true := by
  unfold CFSG.ComponentClassification.CatFactsL4U4.fixCheck
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := hT i hi
  have eall : ((pts 42 6 m CP).all fun c =>
      CFSG.ComponentClassification.CatFactsL4U4.commT (unpack 42 6 (T i)) c) =
      allN m fun c => commPt 42 6 (T i) (CP c) := by
    rw [Bool.eq_iff_iff, Array.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
    constructor
    · intro H c hcm
      have h2 := H c (by rw [size_pts]; exact hcm)
      rw [pts_getElem hcm] at h2
      unfold CFSG.ComponentClassification.CatFactsL4U4.commT at h2
      rw [beq_iff_eq] at h2
      exact (commPt_iff hx (hc c hcm)).2 h2
    · intro H c hcm
      have hcm' : c < m := by rwa [size_pts] at hcm
      rw [pts_getElem hcm']
      unfold CFSG.ComponentClassification.CatFactsL4U4.commT
      rw [beq_iff_eq]
      exact (commPt_iff hx (hc c hcm')).1 (H c hcm')
  rw [pts_get' hi, eall]
  unfold CFSG.ComponentClassification.CatFactsL4U4.commT
  have ecr : (comp 42 (unpack 42 6 (T i)) (unpack 42 6 r) ==
      comp 42 (unpack 42 6 r) (unpack 42 6 (T i))) = commPt 42 6 (T i) r := by
    rw [Bool.eq_iff_iff, beq_iff_eq, commPt_iff hx hr]
  rw [ecr, pow256T_unpack hx, idTab_unpack' hsz42,
    beq_unpack (pow2K_canon hx 8) (canon_pidn hsz42), beq_unpack hx (canon_pidn hsz42),
    beq_unpack hx hr]
  have h' := h i hi
  unfold fixK at h'
  simpa only [orB_eq, notB_eq, Bool.or_assoc] using h'

end CFSG.KC.L34Scan

end
