module

public import Certificates.Data.Kernel.Spor.WordF
public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.LocalQTCovTPrim
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Certificates.Kernel.SporSch.BfsParSound
public import CFSG.Certificates.Kernel.SporSch.HNArr
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck

public section

namespace CFSG.KS.WordF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

variable {n w : Nat}

theorem pcomp_unpack (hn : n < 2 ^ 32) {P Q : Nat} (hQ : ∀ i < n, pg w (mask w) Q i < n) :
    CFSG.ONSchreier.Native.pcomp n (unpack n w P) (unpack n w Q) =
      unpack n w (pcomp n w (mask w) P Q) :=
  CFSG.KC.LQT.Cov.T.compA_unpack hn hQ

theorem pid_unpack (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    CFSG.ONSchreier.Native.pid n = unpack n w (pidn n w) :=
  (CFSG.KC.LQT.Cov.T.unpack_pidn hn hw).symm

theorem pinvCand_unpack {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    CFSG.ONSchreier.Native.pinvCand n (unpack n w P) = unpack n w Q := by
  obtain ⟨h1, h2⟩ := CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack h)
  have h3 := (CFSG.KS.BfsPar.prep_pinvCand (n := n) (t := unpack n w P) h1).1
  apply Array.ext
  · rw [CFSG.KS.HNArr.pinvCand_size]
    simp [unpack]
  · intro i hi1 hi2
    have hi : i < n := by simpa [unpack] using hi2
    have e1 : (CFSG.ONSchreier.Native.pinvCand n (unpack n w P))[i]! =
        (((CFSG.Monster.B.Co2.permOfArr n (unpack n w P))⁻¹ ⟨i, hi⟩ : Fin n) : ℕ) := h3 ⟨i, hi⟩
    have e2 : (unpack n w Q)[i]! =
        (((CFSG.Monster.B.Co2.permOfArr n (unpack n w P))⁻¹ ⟨i, hi⟩ : Fin n) : ℕ) := h2 ⟨i, hi⟩
    rw [← getElem!_pos _ i hi1, ← getElem!_pos _ i hi2, e1, e2]

theorem evA_unpack {k : Nat} {L Li : Array (Array Nat)} {LP LPI : Nat → Nat}
    (hn : n < 16777216) (hw : n + 1 < 2 ^ w)
    (hL : ∀ i < k, L[i]! = unpack n w (LP i)) (hLi : ∀ i < k, Li[i]! = unpack n w (LPI i))
    (hr : ∀ i < k, ∀ x < n, pg w (mask w) (LP i) x < n ∧ pg w (mask w) (LPI i) x < n)
    (wd : List (Fin k × Bool)) :
    CFSG.ASVolI.burnsideF48t_evA n L Li wd =
        unpack n w (evFK n w (mask w) (pidn n w) LP LPI wd) ∧
      ∀ x < n, pg w (mask w) (evFK n w (mask w) (pidn n w) LP LPI wd) x < n := by
  have h32 : n < 2 ^ 32 := lt_trans hn (by norm_num)
  induction wd with
  | nil =>
    refine ⟨pid_unpack hn hw, fun x hx => ?_⟩
    have e : evFK n w (mask w) (pidn n w) LP LPI ([] : List (Fin k × Bool)) = pidn n w := rfl
    rw [e, CFSG.KS.PF.pg_pidn hn hw hx]
    exact hx
  | cons l wd ih =>
    obtain ⟨⟨i, hi⟩, b⟩ := l
    have hev : evFK n w (mask w) (pidn n w) LP LPI ((⟨i, hi⟩, b) :: wd) =
        pcomp n w (mask w) (cond b (LP i) (LPI i)) (evFK n w (mask w) (pidn n w) LP LPI wd) := by
      cases b <;> rfl
    have hlet : CFSG.ASVolI.burnsideF48t_letA L Li ((⟨i, hi⟩, b) : Fin k × Bool) =
        unpack n w (cond b (LP i) (LPI i)) := by
      cases b
      · simpa [CFSG.ASVolI.burnsideF48t_letA] using hLi i hi
      · simpa [CFSG.ASVolI.burnsideF48t_letA] using hL i hi
    rw [hev]
    refine ⟨?_, fun x hx => ?_⟩
    · rw [CFSG.ASVolI.burnsideF48t_evA, ih.1, hlet, pcomp_unpack h32 ih.2]
    · rw [CFSG.KS.PF.pg_pcomp h32 hx]
      cases b
      · exact (hr i hi _ (ih.2 x hx)).2
      · exact (hr i hi _ (ih.2 x hx)).1

end CFSG.KS.WordF

end
