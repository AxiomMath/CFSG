module

public import Certificates.Data.Kernel.L34Inv
public import CFSG.Certificates.Kernel.L34KSound
public import CFSG.Certificates.Kernel.L34KSnd.Tab
public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.HeAutKLoops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeAutKSound

public section

namespace CFSG.KC.L34Inv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB anyN)

variable {n w : Nat}

theorem andB_eq (a b : Bool) : CFSG.KLie.CT.andB a b = (a && b) := by cases a <;> rfl
theorem orB_eq (a b : Bool) : CFSG.KLie.CT.orB a b = (a || b) := by cases a <;> rfl
theorem notB_eq (a : Bool) : CFSG.KLie.CT.notB a = !a := by cases a <;> rfl

theorem anyN_iff {m : Nat} {f : Nat → Bool} : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero =>
    exact ⟨fun h => (nomatch h.symm.trans (rfl : anyN 0 f = false)),
      fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    change CFSG.KLie.CT.orB (f m) (anyN m f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

theorem centK_of_slices {N T r m I CT L K CC} (hN : N = L * K)
    (hs : ∀ s < K, centSl n w T r L CC s = true) (h0 : CC 0 = 0) (hK : CC K = m)
    (hl : centList n w N T r m I CT = true) : centK n w N T r m I CT = true := by
  have hrun : ∀ s ≤ K,
      CFSG.KC.HeAutK.cntR (fun i => commPt n w (T i) r) 0 (L * s) = CC s := by
    intro s
    induction s with
    | zero => intro _; rw [h0]; rfl
    | succ s ih =>
      intro hsK
      have e := Nat.eq_of_beq_eq_true (hs s (by omega))
      change CC s + CFSG.KC.HeAutK.cntR (fun i => commPt n w (T i) r) (L * s) L = CC (s + 1) at e
      rw [Nat.mul_succ, CFSG.KC.HeAutK.cntR_add, ih (by omega), Nat.zero_add, e]
  unfold centK
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.L34KSnd.andB_iff]
  refine ⟨?_, hl⟩
  rw [hN, hrun K le_rfl, hK]
  exact Nat.beq_refl m

theorem pts_size (N : Nat) (T : Nat → Nat) : (pts n w N T).size = N := by simp [pts]

theorem mem_pts_iff {N : Nat} {T : Nat → Nat} {y : Tab} :
    y ∈ pts n w N T ↔ ∃ i < N, unpack n w (T i) = y := by
  unfold pts
  rw [Array.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem pts_get' {N i : Nat} {T : Nat → Nat} (hi : i < N) :
    (pts n w N T)[i]! = unpack n w (T i) := CFSG.KC.L34KSnd.pts_get hi

theorem anyBelow_get_iff (A : Array Tab) (g : Tab → Bool) :
    anyBelow A.size (fun j => g A[j]!) = true ↔ ∃ y ∈ A, g y = true := by
  rw [CFSG.KC.L34KSnd.anyBelow_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    rw [getElem!_pos A j hj] at h
    exact ⟨A[j], Array.getElem_mem hj, h⟩
  · rintro ⟨y, hy, h⟩
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hy
    exact ⟨j, hj, by rw [getElem!_pos A j hj]; exact h⟩

theorem memTab_pts {N x : Nat} {T : Nat → Nat}
    (hc : ∀ i < N, canonK n w (mask w) (n * w) (T i) = true)
    (hx : canonK n w (mask w) (n * w) x = true) :
    memTab (pts n w N T) (unpack n w x) = memK N T x := by
  rw [Bool.eq_iff_iff]
  unfold memTab memK
  rw [anyBelow_get_iff (pts n w N T) (fun y => y == unpack n w x), anyN_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨i, hi, rfl⟩ := mem_pts_iff.1 hy
    rw [CFSG.KC.L34KSnd.beq_unpack (hc i hi) hx] at h
    exact ⟨i, hi, h⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨_, mem_pts_iff.2 ⟨i, hi, rfl⟩, ?_⟩
    rw [CFSG.KC.L34KSnd.beq_unpack (hc i hi) hx]
    exact h

theorem beq_id {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    (unpack n w x == idTab n) = Nat.beq x (pidn n w) := by
  rw [CFSG.KC.L34KSnd.idTab_unpack' (CFSG.KC.L34KSnd.canon_sz hx),
    CFSG.KC.L34KSnd.beq_unpack hx (CFSG.KC.L34KSnd.canon_pidn (CFSG.KC.L34KSnd.canon_sz hx))]

theorem beq_r {x r : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    (unpack n w x == unpack n w r) = Nat.beq x r := CFSG.KC.L34KSnd.beq_unpack hx hr

theorem sq_id {x : Nat} (hx : canonK n w (mask w) (n * w) x = true) :
    (comp n (unpack n w x) (unpack n w x) == idTab n) =
      Nat.beq (pcomp n w (mask w) x x) (pidn n w) := by
  rw [CFSG.KC.L34KSnd.comp_unpack' hx hx, beq_id (CFSG.KC.BfsPin.canonK_pcomp hx hx)]

theorem pow3_id {y : Nat} (hy : canonK n w (mask w) (n * w) y = true) :
    (powTab n (unpack n w y) 3 == idTab n) =
      Nat.beq (pcomp n w (mask w) y (pcomp n w (mask w) y (pcomp n w (mask w) y (pidn n w))))
        (pidn n w) := by
  have hsz := CFSG.KC.L34KSnd.canon_sz hy
  have he := CFSG.KC.L34KSnd.canon_pidn hsz
  have h1 := CFSG.KC.BfsPin.canonK_pcomp hy he
  have h2 := CFSG.KC.BfsPin.canonK_pcomp hy h1
  have e : powTab n (unpack n w y) 3 =
      comp n (unpack n w y) (comp n (unpack n w y) (comp n (unpack n w y) (idTab n))) := rfl
  rw [e, CFSG.KC.L34KSnd.idTab_unpack' hsz, CFSG.KC.L34KSnd.comp_unpack' hy he,
    CFSG.KC.L34KSnd.comp_unpack' hy h1, CFSG.KC.L34KSnd.comp_unpack' hy h2,
    CFSG.KC.L34KSnd.beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hy h2) he]

theorem comm_beq {x y : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hy : canonK n w (mask w) (n * w) y = true) :
    (comp n (unpack n w y) (unpack n w x) == comp n (unpack n w x) (unpack n w y)) =
      Nat.beq (pcomp n w (mask w) y x) (pcomp n w (mask w) x y) := by
  rw [CFSG.KC.L34KSnd.comp_unpack' hy hx, CFSG.KC.L34KSnd.comp_unpack' hx hy,
    CFSG.KC.L34KSnd.beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hy hx)
      (CFSG.KC.BfsPin.canonK_pcomp hx hy)]

theorem anyBelow_filter_pts {m : Nat} {CT : Nat → Nat} (p : Tab → Bool) (g : Tab → Bool)
    (f : Nat → Bool) (hf : ∀ j < m, (p (unpack n w (CT j)) && g (unpack n w (CT j))) = f j) :
    anyBelow ((pts n w m CT).filter p).size (fun j => g ((pts n w m CT).filter p)[j]!) =
      anyN m f := by
  rw [Bool.eq_iff_iff, anyBelow_get_iff, anyN_iff]
  constructor
  · rintro ⟨y, hy, h⟩
    obtain ⟨hy1, hy2⟩ := Array.mem_filter.1 hy
    obtain ⟨j, hj, rfl⟩ := mem_pts_iff.1 hy1
    refine ⟨j, hj, ?_⟩
    rw [← hf j hj, hy2, h]
    rfl
  · rintro ⟨j, hj, h⟩
    rw [← hf j hj, Bool.and_eq_true] at h
    exact ⟨_, Array.mem_filter.2 ⟨mem_pts_iff.2 ⟨j, hj, rfl⟩, h.1⟩, h.2⟩

end CFSG.KC.L34Inv

end
