module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExAlt
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Leaves1
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExL5
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4ExSp4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4D4
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Defs

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk94

open CFSG.Blueprint CFSG.GH74.GLS.IVK

theorem k94Leaves_proved :
    K94Leaves where
  psp4 := k94_psp4
  ree := k94_ree
  psl4 := k94_psl4
  psu4 := k94_psu4
  psl5 := k94_psl5
  psu5 := k94_psu5
  small := k94_small
  alt := k94_alt
  spor := k94_spor
  three := k94_three

theorem k94Class_proved
    (hfilter : GH74FilterStmt) : K94Class :=
  k94Class_of_leaves Proofs2.ivk_4_7ab k94Leaves_proved hfilter

@[expose] def IVK_9_4_g4_small_G2three : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (Gs : Type) [Group Gs] (z : H),
    Gen4 H → CFSG.pRank 2 H ≤ 3 → Hyp94 H Gs z .G2 3 1 → LieModel ↥(layer H) .G2 0 3 1

theorem ivk_9_4_g4_G2three_proved
    (hfilter : GH74FilterStmt) (hsmall : IVK_9_4_g4_small_G2three) : IVK_9_4_g4_G2three := by
  intro H _ _ Gs _ z m hm hgen hrk hyp
  by_cases h5 : 5 ≤ 3 ^ m
  · exact layer_lieModel_of_k94Class Proofs2.ivk_4_7ab (k94Class_proved hfilter) h5 hgen hrk hyp
  · have hm1 : m = 1 := by
      by_contra hne
      have h2 : 2 ≤ m := by omega
      have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) h2
      omega
    subst hm1
    exact hsmall H Gs z hgen hrk hyp

end CFSG.GH74.GLS.IVK.Proofs2.Ivk94
