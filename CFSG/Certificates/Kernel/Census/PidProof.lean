module

public import CFSG.Certificates.Kernel.Census.XsProof

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.Monster.B.Co2.Native

theorem validA_unpackP_proved {n w P : Nat} (_hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hc : canon1 n w P = true) (hv : pvalid n w P = true) :
    CFSG.RankThree.Native.validA n (unpackP n w P) = true := by
  rw [SP.validA_unpack hw hc]
  exact hv

theorem unpackP_pid_proved {n w : Nat} (hn24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) :
    unpackP n w (pid n w) = idA n ∧ canon1 n w (pid n w) = true :=
  SP.pid_good_of_le hn24 hw

theorem clog_big : clog (2 ^ 24 + 2) = 24 := by decide +kernel

theorem pid_field_big : at' 25 (pid (2 ^ 24 + 2) 25) (2 ^ 24) = 0 := by
  have hf := SP.fld_pid (n := 2 ^ 24 + 2) (w := 25) (by norm_num)
  have := CFSG.KS.PackFld.pg_of_fld hf (i := 2 ^ 24) (by rw [clog_big]; simp)
  change at' 25 (pid (2 ^ 24 + 2) 25) (2 ^ 24) = _ at this
  rw [this, clog_big]
  simp

theorem unpackP_pid_counterexample :
    unpackP (2 ^ 24 + 2) 25 (pid (2 ^ 24 + 2) 25) ≠ idA (2 ^ 24 + 2) := by
  intro h
  have h1 : (unpackP (2 ^ 24 + 2) 25 (pid (2 ^ 24 + 2) 25))[2 ^ 24]! =
      (idA (2 ^ 24 + 2))[2 ^ 24]! := by rw [h]
  rw [SP.unpackP_get] at h1
  have hlt : 2 ^ 24 < 2 ^ 24 + 2 := by norm_num
  simp only [hlt, ↓reduceIte, pid_field_big] at h1
  rw [CFSG.Monster.B.Co2.idA_get hlt] at h1
  exact absurd h1 (by norm_num)

end CFSG.KC.Census

end
