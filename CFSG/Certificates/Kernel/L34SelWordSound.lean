module

public import Certificates.Data.Kernel.L34SelWord
public import CFSG.Certificates.Kernel.L34NormSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34SelWord

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.KLie.CT (fget andB orB notB anyN)

theorem selK_sound {N M : Nat} {J W : Nat → Nat} {P : Nat → Bool} {ok : Nat → Nat → Bool}
    (h : selK N J P M W ok = true) {q : Nat} (hq : q < N) (hP : P (J q % 32) = true) :
    ∃ m < M, fget (W m) 0 32 = J q / 32 ∧ ok m (J q / 32) = true := by
  have h1 := CFSG.KS.Raw.Orb.allN_iff.1 h q hq
  rw [strictB_eq, CFSG.KC.L34KSnd.orB_iff, CFSG.KC.L34KSnd.notB_iff] at h1
  rcases h1 with h1 | h1
  · change P (J q % 32) = false at h1
    rw [hP] at h1
    exact absurd h1 (by decide)
  · obtain ⟨m, hm, hok⟩ := anyN_iff.1 h1
    rw [CFSG.KC.L34KSnd.andB_iff] at hok
    exact ⟨m, hm, Nat.eq_of_beq_eq_true hok.1, hok.2⟩

variable {n w : Nat}

theorem wordK_succ (c0 c1 len wd acc : Nat) :
    wordK n w c0 c1 (len + 1) wd acc = wordK n w c0 c1 len (wd / 2)
      (pcomp n w (mask w) acc (nIf(Nat.beq (wd % 2) 0, c0, c1))) := by
  change strictN _ _ = _
  rw [strictN_eq]
  rfl

theorem wordK_mem {H : Subgroup (Equiv.Perm (Fin n))} {c0 c1 : Nat}
    (h0 : canonK n w (mask w) (n * w) c0 = true) (h1 : canonK n w (mask w) (n * w) c1 = true)
    (g0 : ∃ g ∈ H, TabRep (unpack n w c0) g) (g1 : ∃ g ∈ H, TabRep (unpack n w c1) g) :
    ∀ len wd acc, canonK n w (mask w) (n * w) acc = true → (∃ g ∈ H, TabRep (unpack n w acc) g) →
      canonK n w (mask w) (n * w) (wordK n w c0 c1 len wd acc) = true ∧
        ∃ g ∈ H, TabRep (unpack n w (wordK n w c0 c1 len wd acc)) g := by
  intro len
  induction len with
  | zero => exact fun _ _ ha hg => ⟨ha, hg⟩
  | succ len ih =>
    intro wd acc ha hg
    rw [wordK_succ]
    have hL : canonK n w (mask w) (n * w) (nIf(Nat.beq (wd % 2) 0, c0, c1)) = true ∧
        ∃ g ∈ H, TabRep (unpack n w (nIf(Nat.beq (wd % 2) 0, c0, c1))) g := by
      cases Nat.beq (wd % 2) 0
      · exact ⟨h1, g1⟩
      · exact ⟨h0, g0⟩
    obtain ⟨hLc, gL, hgL, hrL⟩ := hL
    obtain ⟨ga, hga, hra⟩ := hg
    refine ih _ _ (canonK_pcomp ha hLc) ⟨ga * gL, H.mul_mem hga hgL, ?_⟩
    rw [← CFSG.KC.L34KSnd.comp_unpack' ha hLc]
    exact hra.comp hrL

theorem wordK_rep {H : Subgroup (Equiv.Perm (Fin n))} {c0 c1 : Nat}
    (h0 : canonK n w (mask w) (n * w) c0 = true) (h1 : canonK n w (mask w) (n * w) c1 = true)
    (g0 : ∃ g ∈ H, TabRep (unpack n w c0) g) (g1 : ∃ g ∈ H, TabRep (unpack n w c1) g)
    {len wd G : Nat} (hw : wordK n w c0 c1 len wd (pidn n w) = G) :
    ∃ g ∈ H, TabRep (unpack n w G) g := by
  have hsz := CFSG.KC.L34KSnd.canon_sz h0
  obtain ⟨-, hg⟩ := wordK_mem h0 h1 g0 g1 len wd (pidn n w) (CFSG.KC.L34KSnd.canon_pidn hsz)
    ⟨1, H.one_mem, by rw [← CFSG.KC.L34KSnd.idTab_unpack' hsz]; exact TabRep.idTab⟩
  rwa [hw] at hg

end CFSG.KC.L34SelWord

end
