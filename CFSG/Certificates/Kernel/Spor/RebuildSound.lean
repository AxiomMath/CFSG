module

public import CFSG.Certificates.Kernel.Spor.RawAgree

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.KS.Raw

variable {n w : Nat}

@[expose] def RebSt (n w : Nat) (a ai : Array Nat) (A AI : Nat) : Prop :=
  a.size = n ∧ ai.size = n ∧ ∃ γ : Equiv.Perm (Fin n), Rep n a γ ∧ Rep n ai γ⁻¹ ∧
    PRep n w A γ ∧ PRep n w AI γ⁻¹

theorem rebSt_init (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    RebSt n w (idA n) (idA n) (pidn n w) (pidn n w) :=
  ⟨by simp [idA], by simp [idA], 1, rep_idA, by rw [inv_one]; exact rep_idA,
    prep_pidn hn hw, by rw [inv_one]; exact prep_pidn hn hw⟩

theorem rebStep_spec (hn : n < 16777216) {R : Nat} {L : Level} {TK : Nat → Equiv.Perm (Fin n)}
    {TR TRI : Nat → Nat} (hA : Agree n w R L TK)
    (hT : ∀ k < rcnt R, PRep n w (TR (roff n (n * w) R + k)) (TK k) ∧
      PRep n w (TRI (roff n (n * w) R + k)) (TK k)⁻¹)
    {a ai : Array Nat} {A AI b : Nat} (hs : RebSt n w a ai A AI) (hb : b < n)
    (hk : rpos w (mask w) (n * w) R (pg w (mask w) AI b) < rcnt R) :
    L.pos[ai[b]!]! = rpos w (mask w) (n * w) R (pg w (mask w) AI b) ∧
      RebSt n w (compA n a L.tr[L.pos[ai[b]!]!]!) (compA n L.trInv[L.pos[ai[b]!]!]! ai)
        (pcomp n w (mask w) A (TR (roff n (n * w) R + rpos w (mask w) (n * w) R (pg w (mask w) AI b))))
        (pcomp n w (mask w) (TRI (roff n (n * w) R + rpos w (mask w) (n * w) R (pg w (mask w) AI b))) AI) := by
  obtain ⟨hsa, hsai, γ, ha, hai, hPA, hPAI⟩ := hs
  have hz : ai[b]! = pg w (mask w) AI b := by
    rw [hai.apply hb]
    exact (hPAI ⟨b, hb⟩).symm
  have hzn : pg w (mask w) AI b < n := by rw [← hz]; exact hai.lt hb
  set z := pg w (mask w) AI b
  have hkL : L.pos[z]! < L.pts.size := (hA.pos z hzn).1 hk
  have hkE : rpos w (mask w) (n * w) R z = L.pos[z]! := hA.posE z hzn hkL
  have h32 : n < 2 ^ 32 := by omega
  rw [hz]
  refine ⟨hkE.symm, ?_⟩
  rw [← hkE]
  set k := rpos w (mask w) (n * w) R z
  have hkL' : k < L.pts.size := by rw [hkE]; exact hkL
  obtain ⟨htr, htri⟩ := hA.tr k hkL'
  obtain ⟨hPT, hPTI⟩ := hT k hk
  refine ⟨by simp [compA], by simp [compA], γ * TK k, rep_compA ha htr, ?_, prep_pcomp h32 hPA hPT, ?_⟩
  · rw [mul_inv_rev]
    exact rep_compA htri hai
  · rw [mul_inv_rev]
    exact prep_pcomp h32 hPTI hPAI

theorem rep_eq_unpack {a : Array Nat} {A : Nat} {γ : Equiv.Perm (Fin n)} (hs : a.size = n)
    (ha : Rep n a γ) (hA : PRep n w A γ) : a = unpack n w A := by
  apply Array.ext (by simp [hs, unpack])
  intro i h1 _
  have hi : i < n := hs ▸ h1
  rw [← getElem!_pos a i h1, ha.apply hi, ← hA ⟨i, hi⟩, ← unpack_get hi,
    getElem!_pos (unpack n w A) i (by simp [unpack, hi])]

end CFSG.KS.Raw.Orb

end
