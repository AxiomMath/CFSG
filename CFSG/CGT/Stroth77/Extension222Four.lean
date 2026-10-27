module

public import CFSG.CGT.Stroth77.Extension216
public import CFSG.CGT.Stroth77.Extension222

public section

namespace CFSG.CGT.Stroth77

theorem hasStrothTypeOver_t130_or_t131_of_noInvolutionsCentralizing_t331 {S : Type*} [Group S]
    [Finite S] {B C S' : Subgroup S} (D : StrothTypeData B StrothTypeIndex.t331)
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B) (hL : D.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') :
    HasStrothTypeOver D C (StrothTypeIndex.t130 3 le_rfl) ∨
      HasStrothTypeOver D C (StrothTypeIndex.t131 3 le_rfl) :=
  (hasStrothTypeOver_t130_or_t131_of_data D.t330OfT331 hBC hC hrel
    (by rw [StrothTypeData.t330OfT331_L]; exact hL) hH hcS).imp
    (·.of_gen_eq rfl rfl rfl rfl) (·.of_gen_eq rfl rfl rfl rfl)

end CFSG.CGT.Stroth77
