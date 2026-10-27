module

public import Certificates.Data.Kernel.OpsF2KE16
import all CFSG.Certificates.Kernel.OpsF2KMcertSound
import all CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Co1F2Sound
import CFSG.Certificates.Kernel.F2WordSound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.SectionRank.Native
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native
open CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCover.Native
open CFSG.KC.Co1F2 (unpackR)
open CFSG.KC.F2W (vmF_lt)

theorem e16Check_of_K {d A B : Nat} {csA csB : List Char} {D : E8Data}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : e16K d A B D = true) : e16Check (ops2 d) D = true := by
  simp only [e16K, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hrx, hrh, hoh, hoh16, ht, hX2, hH, hv, hc2, hc3, hc4,
    hconj⟩ := h
  have hreg : ∀ r < D.nregs, ((ops2 d).regsOf D.seedA D.seedB D.nregs D.prog)[r]! =
      unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => mRegs_get hA hB hsA hsB hprog hexp hr
  unfold e16Check
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  rw [hreg _ hrx, hreg _ hrh, ← unpackR_powK (by omega : D.oh - 1 < 2 ^ 16)]
  simp only [← unpackR_mulF]
  refine ⟨hn, hprog, hrx, hrh, hoh, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← unpackR_powK (by norm_num), ← unpackR_idF_eq_one]
    exact eq_of_beq hX2
  · rw [← unpackR_powK (by omega), ← unpackR_idF_eq_one]
    exact eq_of_beq hH
  · rw [unit_eq, vmul_unpackR]
    exact vne_of_beq (vmF_lt _ _ _) (pw2_lt ht) hv
  · unfold commK at hc2
    exact eq_of_beq hc2
  · unfold commK at hc3
    exact eq_of_beq hc3
  · unfold commK at hc4
    exact eq_of_beq hc4
  · exact conjOK_of_conjK hconj

end CFSG.KC.OpsF2K
