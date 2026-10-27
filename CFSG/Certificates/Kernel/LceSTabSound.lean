module

public import Certificates.Data.Kernel.LceSTab
public import Mathlib.GroupTheory.Index
import CFSG.Certificates.Kernel.LceSP.Main

public section

namespace CFSG.Certificates.LCE

open CFSG.KC CFSG.KC.LceS

@[expose] def letV {G : Type*} [Group G] (gen : ℕ → G) (l : ℕ) : G :=
  if l = 255 then 1 else if l % 2 = 0 then gen (l / 2) else (gen (l / 2))⁻¹

@[expose] noncomputable def bval {G : Type*} [Group G] (gen : ℕ → G) (W n : ℕ) : G :=
  ((List.range n).map fun i => letV gen (wLet W i)).prod

theorem lceOk_sound {blk WT RT ST LVs : ℕ → ℕ}
    {INV INV8 L nC nCl mLV a m Hs nR nS nf : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}
    (h : lceOk blk WT RT ST LVs INV INV8 L nC nCl mLV a m Hs nR nS nf Cs CCs S0 S1 X0 X1 = true)
    {G : Type*} [Group G] (gen : ℕ → G)
    (hrels : ∀ r < nR, bval gen (wWord (RT r)) (wLen (RT r)) = 1) :
    (Subgroup.closure ((fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < L})) ≠ 0 ∧
      (Subgroup.closure ((fun j => bval gen (wWord (ST j)) (wLen (ST j))) '' {j | j < nS})).relIndex
        (Subgroup.closure (gen '' {g | 2 * g < L})) ≤ a :=
  CFSG.Certificates.LceP.lceOk_sound' h gen hrels

end CFSG.Certificates.LCE

end
