module

public import Certificates.Data.Kernel.LceSHeRu
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.LceSP.LabFLab

public section

namespace CFSG.Certificates.LS

open CFSG.KC CFSG.KC.LceS CFSG.Certificates.LCE

theorem He.coneOk_sound {G : Type*} [Group G] (gen u : ℕ → G) (hu : u 0 * u 0 = 1)
    {blk WT RT ST LB : ℕ → ℕ} {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : He.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs = true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST0 : bval gen (wWord (ST 0)) (wLen (ST 0)) = u 0)
    (hST1 : bval gen (wWord (ST 1)) (wLen (ST 1)) = u 1)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : HeB.cycOK blk WT LB nf c wid R (HeB.entStk E) = true) :
    bval u (wWord E) (wLen E) = 1 :=
  CFSG.Certificates.LceP.HeL.coneOk_sound' u gen hu h hRT hST0 hST1 hc0 hwid hc

theorem Ru.coneOk_sound {G : Type*} [Group G] (gen u : ℕ → G) (hu : u 1 * u 1 = 1)
    {blk WT RT ST LB : ℕ → ℕ} {INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : Ru.coneOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs S0 S1 X0 X1 Cs = true)
    (hRT : ∀ r, wWord (RT r) < 2 ^ (8 * wLen (RT r)) ∧ bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST0 : bval gen (wWord (ST 0)) (wLen (ST 0)) = u 0)
    (hST1 : bval gen (wWord (ST 1)) (wLen (ST 1)) = u 1)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : RuB.cycOK blk WT LB nf c wid R (RuB.entStk E) = true) :
    bval u (wWord E) (wLen E) = 1 :=
  CFSG.Certificates.LceP.HeL.ruConeOk_sound' u gen hu h hRT hST0 hST1 hc0 hwid hc

theorem LabF.labOk_sound {G : Type*} [Group G] (gen w : ℕ → G)
    {blk WT RT ST LB : ℕ → ℕ} {INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 : ℕ} {Cs : List ℕ}
    (h : LabF.labOk blk WT RT ST LB INV INV8 L nC nCa nf m Hs nR nS K S0 S1 X0 X1 Cs = true)
    (hRT : ∀ r < nR, bval gen (wWord (RT r)) (wLen (RT r)) = 1)
    (hST : ∀ j < K, bval gen (wWord (ST j)) (wLen (ST j)) = w j)
    {c wid R E : ℕ} (hc0 : c < 2 ^ 20) (hwid : wid < m)
    (hc : CFSG.KC.LabF.cycOK blk WT LB nf c wid R (CFSG.KC.LabF.entStk E) = true) :
    bval w (wWord E) (wLen E) = 1 :=
  CFSG.Certificates.LceP.LabFL.labOk_sound' w gen h hRT hST hc0 hwid hc

end CFSG.Certificates.LS

end
