module

public import Certificates.Data.Kernel.D43.TwinW
public import CFSG.Certificates.Kernel.Spor.ONVKWSound
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONW

theorem lt_chunkCnt {lo l : Nat} (hl : l < 256) (hp : lo + l < 26572) : l < chunkCnt lo := by
  unfold chunkCnt
  cases hb : Nat.blt (Nat.add lo 256) 26573
  · change l < Nat.sub 26572 lo
    rw [Nat.sub_eq]
    omega
  · exact hl

theorem pm_swap {u w : Nat} (h : pmEq u w = true) :
    bIf(Nat.beq w u, true, Nat.beq w (vneg u)) = true := by
  unfold pmEq at h
  cases h1 : Nat.beq u w
  · rw [h1] at h
    cases h2 : Nat.beq w u
    · exact h
    · rfl
  · have e := Nat.eq_of_beq_eq_true h1
    subst e
    rw [Nat.beq_refl]

theorem keyChunk_of_W {KT : Nat → Nat} {L : List Nat} {T : Nat → Nat} {c : Nat}
    (h : keyChunkW KT L T c = true) : keyChunk KT L T c = true := by
  unfold keyChunkW at h
  simp only [PackFld.strictB_eqP] at h
  obtain ⟨h1, h2⟩ := ptsV_spec _ 0 0 h
  simp only [Nat.mul_zero, Nat.add_zero] at h2
  have hc : ∀ i < chunkCnt (Nat.mul 256 c), Nat.blt (T (Nat.mul 256 c + i)) 26572 = true ∧
      canon (key KT (Nat.mul 256 c + i)) = true := fun i hi => (bAnd_iff _ _).1 (h1 i hi)
  have hf := finP_spec (fun i _ => key_lt KT _) (fun i _ => key_lt KT _) (fun i hi => (hc i hi).2) h2
  unfold keyChunk
  refine allBlk_of fun l hl => ?_
  change bIf(Nat.blt (Nat.mul 256 c + l) 26572, keyChk KT L T (Nat.mul 256 c + l), true) = true
  cases hb : Nat.blt (Nat.mul 256 c + l) 26572
  · rfl
  · have hl' : l < chunkCnt (Nat.mul 256 c) := lt_chunkCnt hl (Nat.blt_eq.mp hb)
    change keyChk KT L T (Nat.mul 256 c + l) = true
    unfold keyChk
    simp only [PackFld.strictB_eqP]
    rw [(hc l hl').1]
    exact pm_swap (hf l hl')

end CFSG.KC.D43

end
