module

public import CFSG.Certificates.Kernel.BabyMonster.VStripSound
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data3
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Data5
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Data0
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Spin

public section

namespace CFSG.KC.BM.SevenGen

open CFSG.KC.BM
open scoped Matrix

@[expose] def FactSevenGen : Prop :=
  (stripMat Seven.x = stripMat Seven.g ^ 10 ∧ stripMat Seven.y = stripMat Seven.g ^ 14 ∧
    stripMat Seven.y ^ 5 = 1 ∧ stripMat Seven.x ≠ 1) ∧
  (stripMat c * stripMat ci = 1 ∧ stripMat s2 = stripMat ci * stripMat Seven.g * stripMat c ∧
    stripMat f = stripMat ci * stripMat Seven.x * stripMat c ∧
    stripMat Seven.x * stripMat f = stripMat f * stripMat Seven.x) ∧
  (vrow (rowOf vf 0) ᵥ* stripMat Seven.x = vrow (rowOf vf 0) ∧
    vrow (rowOf vf 0) ᵥ* stripMat f ≠ vrow (rowOf vf 0)) ∧
  (stripMat Seven.g * stripMat gi = 1 ∧ stripMat s2 * stripMat s2i = 1 ∧
    stripMat ap = (stripMat Seven.g ^ 2 * stripMat s2i * stripMat Seven.g * stripMat s2i *
      stripMat Seven.g) ^ 17 ∧
    stripMat bp = (stripMat Seven.g * stripMat s2 * stripMat gi * stripMat s2 ^ 2) ^ 13) ∧
  stripMat H * stripMat Hi = 1 ∧ stripMat Seeds.A1 * stripMat H = stripMat H * stripMat ap ∧
    stripMat Seeds.A2 * stripMat H = stripMat H * stripMat bp

end CFSG.KC.BM.SevenGen

end
