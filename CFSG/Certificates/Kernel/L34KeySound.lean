module

public import Certificates.Data.Kernel.L34Key
public import CFSG.Certificates.Kernel.L34KSound
public import CFSG.ClassicalInvolution.SmallCases.NobqL34CheckInputs
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Key

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.PSL3Four.Native CFSG.ClassicalInvolution.Nobq
open CFSG.KLie.CT (andB orB notB)

variable {n w : Nat}

theorem exists_of_notB_allN' {m : Nat} {f : Nat → Bool} (h : CFSG.KLie.CT.notB (allN m f) = true) :
    ∃ k < m, f k = false := by
  rw [notB_iff] at h
  by_contra hc
  push Not at hc
  have : allN m f = true := CFSG.KS.Raw.Orb.allN_iff.2 fun k hk => by
    have := hc k hk
    cases e : f k
    · exact absurd e this
    · rfl
  rw [this] at h
  exact absurd h (by decide)

theorem sqPt_eq {x r : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    sqPt n w x r = Nat.beq (pcomp n w (mask w) x x) r := by
  cases h : Nat.beq (pcomp n w (mask w) x x) r
  · cases hs : sqPt n w x r
    · rfl
    · exfalso
      unfold sqPt at hs
      refine Nat.ne_of_beq_eq_false h (eq_of_pg (CFSG.KC.BfsPin.canonK_pcomp hx hx) hr
        fun i hi => ?_)
      rw [pg_pcomp' hx hi]
      exact Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 hs i hi)
  · have e := Nat.eq_of_beq_eq_true h
    unfold sqPt
    refine CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.beq_eq.mpr ?_
    rw [← e, pg_pcomp' hx hi]

theorem commPt_eq {x g : Nat} (hx : canonK n w (mask w) (n * w) x = true)
    (hg : canonK n w (mask w) (n * w) g = true) :
    commPt n w x g = Nat.beq (pcomp n w (mask w) x g) (pcomp n w (mask w) g x) := by
  rw [Bool.eq_iff_iff, commPt_iff hx hg, comp_unpack' hx hg, comp_unpack' hg hx]
  constructor
  · intro e
    rw [unpack_inj' (CFSG.KC.BfsPin.canonK_pcomp hx hg) (CFSG.KC.BfsPin.canonK_pcomp hg hx) e]
    exact Nat.beq_refl _
  · intro h
    rw [Nat.eq_of_beq_eq_true h]

theorem keyTab_of {N m r : Nat} {T C : Nat → Nat}
    (hT : ∀ i < N, canonK 42 6 (mask 6) (42 * 6) (T i) = true)
    (hC : ∀ c < m, canonK 42 6 (mask 6) (42 * 6) (C c) = true)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true)
    (h : ∀ i < N, keyK 42 6 m C r (T i) = true) :
    keyTabCheck (pts 42 6 N T) (pts 42 6 m C) (unpack 42 6 r) = true := by
  unfold keyTabCheck
  rw [CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro i hi
  have hx := hT i hi
  have h' := h i hi
  unfold keyK at h'
  rw [pts_get' hi, comp_unpack' hx hx, beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hx hx) hr]
  rcases orB_iff.1 h' with h1 | h1
  · rw [notB_iff, sqPt_eq hx hr] at h1
    rw [h1]
    rfl
  · obtain ⟨j, hj, hj'⟩ := exists_of_notB_allN' h1
    rw [strictB_app] at hj'
    have hv := hC j hj
    cases e : CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (commPt 42 6 (T i) (C j)))
        (CFSG.KLie.CT.notB (Nat.beq (pcomp 42 6 (mask 6) (T i) (C j))
          (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) r (C j)) (T i))))
    · rw [e] at hj'
      exact absurd hj' (by decide)
    · obtain ⟨c1, c2⟩ := andB_iff.1 e
      rw [notB_iff, commPt_eq hx hv] at c1
      rw [notB_iff] at c2
      rw [Bool.or_eq_true]
      right
      rw [anyBelow_iff]
      refine ⟨j, by rw [size_pts]; exact hj, ?_⟩
      rw [pts_get' hj, comp_unpack' hx hv, comp_unpack' hv hx, comp_unpack' hr hv,
        comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp hr hv) hx,
        beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hx hv) (CFSG.KC.BfsPin.canonK_pcomp hv hx),
        beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hx hv)
          (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hr hv) hx), c1, c2]
      rfl

theorem cqTab_of {m r : Nat} {C CI : Nat → Nat}
    (hC : ∀ c < m, canonK 42 6 (mask 6) (42 * 6) (C c) = true)
    (hCI : ∀ c < m, canonK 42 6 (mask 6) (42 * 6) (CI c) = true ∧
      pcomp 42 6 (mask 6) (C c) (CI c) = pidn 42 6)
    (hr : canonK 42 6 (mask 6) (42 * 6) r = true) (h : cqK 42 6 m C CI r = true) :
    cqTabCheck (pts 42 6 m C) ((pts 42 6 m C).map (invTab 42)) (unpack 42 6 r) = true := by
  have hinv := invsOK_of_pcomp (n := 42) (w := 6) (gs := pts 42 6 m C) (ng := m) (G := C)
    (GI := CI) (size_pts _ _ _ _) (fun k hk => pts_get' hk)
    (fun k hk => ⟨hC k hk, (hCI k hk).1, (hCI k hk).2⟩)
  unfold cqTabCheck
  rw [hinv.2, Bool.true_and, CFSG.KS.BfsReplay.allBelow_iff, size_pts]
  intro a ha
  have hx := hC a ha
  unfold cqK at h
  rw [strictB_app] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h a ha
  rw [strictB_app] at h'
  rw [pts_get' ha, comp_unpack' hx hx, beq_unpack (CFSG.KC.BfsPin.canonK_pcomp hx hx) hr]
  rcases orB_iff.1 h' with h1 | h1
  · rw [notB_iff] at h1
    rw [h1]
    rfl
  · obtain ⟨b, hb, hb'⟩ := exists_of_notB_allN' h1
    rw [strictB_app] at hb'
    have hg := hC b hb
    have hgi := (hCI b hb).1
    have hq := CFSG.KC.BfsPin.canonK_pcomp hx
      (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hg hx) hgi)
    cases e : CFSG.KLie.CT.andB (invPt 42 6 (pcomp 42 6 (mask 6) (C a)
        (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (C b) (C a)) (CI b))))
        (CFSG.KLie.CT.andB (CFSG.KLie.CT.notB (Nat.beq (pcomp 42 6 (mask 6) (C a)
          (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (C b) (C a)) (CI b))) (pidn 42 6)))
          (CFSG.KLie.CT.notB (Nat.beq (pcomp 42 6 (mask 6) (C a)
            (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (C b) (C a)) (CI b))) r)))
    · rw [e] at hb'
      exact absurd hb' (by decide)
    · obtain ⟨c1, c23⟩ := andB_iff.1 e
      obtain ⟨c2, c3⟩ := andB_iff.1 c23
      rw [notB_iff] at c2 c3
      rw [Bool.or_eq_true]
      right
      rw [anyBelow_iff]
      refine ⟨b, hb, ?_⟩
      unfold cqTab
      rw [pts_get' hb, hinv.1 b hb, comp_unpack' hg hx,
        comp_unpack' (CFSG.KC.BfsPin.canonK_pcomp hg hx) hgi,
        comp_unpack' hx (CFSG.KC.BfsPin.canonK_pcomp (CFSG.KC.BfsPin.canonK_pcomp hg hx) hgi),
        (invPt_iff hq).1 c1, idTab_unpack' hsz42, beq_unpack hq (canon_pidn hsz42),
        beq_unpack hq hr, c2, c3]
      simp only [beq_self_eq_true, Bool.not_false, Bool.and_self]

end CFSG.KC.L34Key

end
