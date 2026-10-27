module

public import Certificates.Data.Kernel.Q8WitL34
public import Certificates.Data.TwinPerpSmSp1WitL34
public import CFSG.Certificates.Kernel.Q8WitSound
public import CFSG.Certificates.Kernel.L34KSound
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

namespace CFSG.KC.Q8Wit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.E81K
open CFSG.KC.L34K CFSG.KC.L34KSnd CFSG.KS.Prim
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native Certificates.TwinPerpSmSp1
open CFSG.Monster.B.Co2 (allLt_iff)

variable {n w : ℕ}

theorem pts_get' {N i : ℕ} {T : ℕ → ℕ} (hi : i < N) : (pts n w N T)[i]! = unpack n w (T i) := by
  unfold pts
  exact pts_get hi

theorem q8SqIn_of {N M : ℕ} {T SQ I ST W : ℕ → ℕ} {ps : Array (Array ℕ)}
    (hsz : szOK n w = true) (hps : ps.size = N) (hpt : ∀ i < N, ps[i]! = unpack n w (T i))
    (hpT : ∀ i < N, Fp n w (T i)) (htabs : tabsK n w N T SQ I = true)
    (h : sqInK n w N SQ M ST W = true) :
    q8SqIn n ps (ps.map fun y => compA n y y) (pts n w M ST) = true := by
  have ht : ∀ i < N, SQ i = pcomp n w (mask w) (T i) (T i) := fun i hi => by
    have e := allNP_iff.1 htabs i hi
    simp only [Bool.and_eq_true] at e
    exact Nat.eq_of_beq_eq_true e.1
  have hid : idA n = unpack n w (pidn n w) := idA_eq hsz
  have hF1 : Fp n w (pidn n w) := PP.id hsz
  have hsq : ∀ i < N, (ps.map fun y => compA n y y)[i]! = unpack n w (SQ i) := fun i hi => by
    rw [getMap ps _ (by rw [hps]; exact hi), hpt i hi, compA_F (hpT i hi) (hpT i hi), (ht i hi)]
  have hFs : ∀ i < N, Fp n w (SQ i) := fun i hi => by
    rw [ht i hi]
    exact (hpT i hi).mul (hpT i hi)
  unfold q8SqIn
  rw [allLt_iff, hps]
  intro i hi
  have hi' := allNP_iff.1 h i hi
  rw [hsq i hi, hid, eqA_F (hFs i hi) hF1, compA_F (hFs i hi) (hFs i hi),
    eqA_F ((hFs i hi).mul (hFs i hi)) hF1]
  simp only [Bool.or_eq_true] at hi' ⊢
  rcases hi' with hi' | hi'
  · exact Or.inl hi'
  right
  rw [allLt_iff]
  intro j _
  simp only [Bool.or_eq_true]
  right
  simp only [Bool.and_eq_true] at hi'
  obtain ⟨hw, he⟩ := hi'
  have hw' : W i < M := Nat.blt_eq.mp hw
  unfold memTab anyBelow
  rw [List.any_eq_true]
  refine ⟨W i, List.mem_range.2 (by rw [size_pts]; exact hw'), ?_⟩
  rw [pts_get' hw', Nat.eq_of_beq_eq_true he]
  exact beq_self_eq_true _

theorem canon_powK {t : ℕ} (hsz : szOK n w = true) (ht : canonK n w (mask w) (n * w) t = true) :
    ∀ e, canonK n w (mask w) (n * w) (powK n w t e) = true
  | 0 => canon_pidn hsz
  | e + 1 => canonK_pcomp ht (canon_powK hsz ht e)

theorem powTab_unpack {t : ℕ} (hsz : szOK n w = true)
    (ht : canonK n w (mask w) (n * w) t = true) :
    ∀ e, powTab n (unpack n w t) e = unpack n w (powK n w t e)
  | 0 => idTab_unpack' hsz
  | e + 1 => by
    rw [powTab, powTab_unpack hsz ht e, comp_unpack' ht (canon_powK hsz ht e)]
    rfl

theorem cent_of {N m e : ℕ} {RT CP : ℕ → ℕ} (hsz : szOK n w = true)
    (hRc : ∀ k < N, canonK n w (mask w) (n * w) (RT k) = true)
    (hCc : ∀ a < m, canonK n w (mask w) (n * w) (CP a) = true)
    (h : ∀ k < N, centPtK n w RT m CP e k = true) :
    (allBelow (pts n w N RT).size fun k =>
      !(allBelow (pts n w m CP).size fun a =>
          comp n (pts n w m CP)[a]! (pts n w N RT)[k]! ==
            comp n (pts n w N RT)[k]! (pts n w m CP)[a]!) ||
        powTab n (pts n w N RT)[k]! e == idTab n) = true := by
  unfold allBelow
  rw [List.all_eq_true]
  intro k hk
  have hk' : k < N := by
    have := List.mem_range.1 hk
    rwa [size_pts] at this
  have hc := h k hk'
  unfold centPtK at hc
  rw [pts_get' hk', powTab_unpack hsz (hRc k hk'), idTab_unpack' hsz,
    beq_unpack (canon_powK hsz (hRc k hk') e) (canon_pidn hsz)]
  simp only [Bool.or_eq_true] at hc ⊢
  rcases hc with hc | hc
  · left
    rw [Bool.not_eq_true'] at hc ⊢
    rw [Bool.eq_false_iff] at hc ⊢
    intro hall
    apply hc
    rw [allNP_iff]
    intro a ha
    have := List.all_eq_true.1 hall a (List.mem_range.2 (by rw [size_pts]; exact ha))
    rw [pts_get' ha, comp_unpack' (hCc a ha) (hRc k hk'), comp_unpack' (hRc k hk') (hCc a ha),
      beq_unpack (canonK_pcomp (hCc a ha) (hRc k hk')) (canonK_pcomp (hRc k hk') (hCc a ha))]
      at this
    exact this
  · exact Or.inr hc

end CFSG.KC.Q8Wit

end
