module

public import Certificates.Data.Kernel.TwistDce3.Defs
public import CFSG.Certificates.Kernel.TwistDce2.Sound
import CFSG.Certificates.Kernel.TwistDce3.Fold

public section

namespace CFSG.Certificates.TwDce3

open CFSG.KC.TwDce3 CFSG.Certificates.CosetEnumeration CFSG.KC.YModel CFSG.Certificates.TwDce
open CFSG.KC.TwDce2 (ivL dKind dN1 dN2)
open CFSG.Certificates.TwDce2 (wdVal)

variable {G : Type*} [Group G]

theorem dce_sound {PB : ℕ} {F RD RW RA WD RJ : ℕ → ℕ} {INVM BS NB NT PSF PSB N C : ℕ}
    (hfold : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 N 1 = C) (hC : 0 < C)
    (H : Subgroup G) (x : ℕ → G) (t : G)
    (hxH : ∀ c < 12, x c ∈ H)
    (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12)
    (hTf : ∀ c < NT, CFSG.KC.TwDce.thL PSF c < 12 ∧ x c * t = t * x (CFSG.KC.TwDce.thL PSF c))
    (hTb : ∀ c < NT, CFSG.KC.TwDce.thL PSB c < 12 ∧
      x c * t⁻¹ = t⁻¹ * x (CFSG.KC.TwDce.thL PSB c))
    (hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
      evalWord (wdVal x t) (wList (WD i)) = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
        CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord x w = 1)
    (hlen : ∀ r < N, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧ CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16) :
    ∃ X : ℕ → G, X 0 = 1 ∧ ∀ r < N, dKind (RD r) < 5 ∧ dN1 (RD r) < C ∧ dN2 (RD r) < C ∧
      (dKind (RD r) < 3 →
        X (dN1 (RD r)) * wVal x (RW r) * t * (X (dN2 (RD r)) * wVal x (RA r))⁻¹ ∈ H) ∧
      (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal x (RW r))⁻¹ ∈ H) := by
  obtain ⟨X, hX0, hX⟩ := CFSG.Certificates.TwDce3.Fold.dce_fold hfold hC H x t hxH hinv hNT hTf
    hTb (wdVal x t) (fun c hc => by simp [wdVal, hc]) (by simp [wdVal]) (by simp [wdVal])
    (by simp [wdVal]) hWD hone hlen
  exact ⟨X, hX0, hX⟩

theorem dce_sound_comm {PB : ℕ} {F RD RW RA WD RJ : ℕ → ℕ} {INVM BS NB NT N C : ℕ}
    (hfold : foldRange PB F INVM BS NB NT idMap idMap RD RW RA WD RJ 0 N 1 = C) (hC : 0 < C)
    (H : Subgroup G) (x : ℕ → G) (t : G)
    (hxH : ∀ c < 12, x c ∈ H)
    (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hNT : NT ≤ 12) (hT : ∀ c < NT, x c * t = t * x c)
    (hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
      evalWord (wdVal x t) (wList (WD i)) = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt PB (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
        CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord x w = 1)
    (hlen : ∀ r < N, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧ CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16) :
    ∃ X : ℕ → G, X 0 = 1 ∧ ∀ r < N, dKind (RD r) < 5 ∧ dN1 (RD r) < C ∧ dN2 (RD r) < C ∧
      (dKind (RD r) < 3 →
        X (dN1 (RD r)) * wVal x (RW r) * t * (X (dN2 (RD r)) * wVal x (RA r))⁻¹ ∈ H) ∧
      (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal x (RW r))⁻¹ ∈ H) := by
  have hid : ∀ c < NT, CFSG.KC.TwDce.thL idMap c = c := fun c hc =>
    CFSG.Certificates.TwDce3.Words.thL_idMap (by omega)
  refine dce_sound hfold hC H x t hxH hinv hNT (fun c hc => ?_) (fun c hc => ?_) hWD hone hlen
  · rw [hid c hc]
    exact ⟨by omega, hT c hc⟩
  · rw [hid c hc]
    exact ⟨by omega, CFSG.Certificates.TwDce2.Walk.inv_comm_of (hT c hc)⟩

end CFSG.Certificates.TwDce3

end
