module

public import Certificates.Data.Kernel.TwistDce2.Defs
public import CFSG.Certificates.Kernel.TwistDce.Sound
import CFSG.Certificates.Kernel.TwistDce2.Fold

public section

namespace CFSG.Certificates.TwDce2

open CFSG.KC.TwDce2 CFSG.Certificates.CosetEnumeration CFSG.KC.YModel
  CFSG.Certificates.TwDce

variable {G : Type*} [Group G]

@[expose] noncomputable def wdVal (x : ℕ → G) (t : G) (c : ℕ) : G :=
  if c < 12 then x c else if c = 12 then t else if c = 13 then t⁻¹ else 1

theorem dce_sound {F RD RW RA WD RJ : ℕ → ℕ} {INVM BS NB N C : ℕ}
    (hfold : foldRange F INVM BS NB RD RW RA WD RJ 0 N 1 = C) (hC : 0 < C)
    (H : Subgroup G) (x : ℕ → G) (t : G)
    (hxH : ∀ c < 12, x c ∈ H)
    (hinv : ∀ c < 12, ivL INVM c < 12 ∧ x (ivL INVM c) = (x c)⁻¹)
    (hT : ∀ c < 4, x c * t = t * x c)
    (hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
      evalWord (wdVal x t) (wList (WD i)) = 1)
    (hone : ∀ w : List ℕ, (∀ c ∈ w, c < 12) →
      (∀ i < NB, w.foldl (fun p c => fieldAt 11 (F c) p) (CFSG.KC.TwDce.fld BS (16 * i) 65535) =
        CFSG.KC.TwDce.fld BS (16 * i) 65535) → evalWord x w = 1)
    (hlen : ∀ r < N, CFSG.KC.TwDce.wLen (RW r) < 2 ^ 16 ∧ CFSG.KC.TwDce.wLen (RA r) < 2 ^ 16) :
    ∃ X : ℕ → G, X 0 = 1 ∧ ∀ r < N, dKind (RD r) < 5 ∧ dN1 (RD r) < C ∧ dN2 (RD r) < C ∧
      (dKind (RD r) < 3 →
        X (dN1 (RD r)) * wVal x (RW r) * t * (X (dN2 (RD r)) * wVal x (RA r))⁻¹ ∈ H) ∧
      (3 ≤ dKind (RD r) → X (dN1 (RD r)) * (X (dN2 (RD r)) * wVal x (RW r))⁻¹ ∈ H) := by
  obtain ⟨X, hX0, hX⟩ := CFSG.Certificates.TwDce2.Fold.dce_fold hfold hC H x t hxH hinv hT
    (wdVal x t) (fun c hc => by simp [wdVal, hc]) (by simp [wdVal]) (by simp [wdVal])
    (by simp [wdVal]) hWD hone hlen
  exact ⟨X, hX0, hX⟩

end CFSG.Certificates.TwDce2

end
