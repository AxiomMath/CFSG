module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16Sound
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQ16J2Data
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafModels
public import Certificates.Certificate320303

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem perm_mem_R_of_sylow {s : Array ℕ}
    (hs : validA 315 s = true)
    (hP : CFSG.ComponentClassification.J2Cover.inP
      (compA 315 s CFSG.ComponentClassification.J2Cover.outerArr) = true) :
    permOfArr 315 s ∈ CFSG.ComponentClassification.J2Cover.R := by
  rw [CFSG.ComponentClassification.J2Cover.mem_R_iff]
  exact Or.inr ((CFSG.ComponentClassification.J2Cover.mem_P_iff
    (rep_compA (rep_of_validA hs) CFSG.ComponentClassification.J2Cover.rep_permU)).1 hP)

theorem j2Q16_pg_get {k : ℕ} (hk : k < 3) :
    Check.j2Q16.pg[k]! = CFSG.ComponentClassification.J2Cover.sylowStrong[k]! := by
  interval_cases k <;> rfl

theorem noQ16Q16_j2_R :
    NoQ16Q16 ↥CFSG.ComponentClassification.J2Cover.R :=
  noQ16Q16_of_sylow_card CFSG.ComponentClassification.J2Cover.sylowS_le_R (k := 8) (m := 4725)
    (CFSG.ComponentClassification.J2Cover.card_sylowS.trans (by norm_num)) (by decide)
    (by rw [CFSG.ComponentClassification.J2Cover.card_R]; norm_num)
    Certificates.certificate320303

theorem autJ2NoQ16Q16_holds :
    AutJ2NoQ16Q16 :=
  autJ2NoQ16Q16_of_model noQ16Q16_j2_R

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
