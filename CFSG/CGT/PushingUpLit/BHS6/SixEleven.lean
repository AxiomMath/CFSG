module

public import CFSG.CGT.PushingUpLit.BHS6.Subnormal
public import CFSG.CGT.PushingUpLit.BlocksCommute
public import CFSG.CGT.PushingUpLit.Glue.BlockInX

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

theorem six_eleven_subgroupOf (hG : CharTwo G) (hE : E ∈ btBlocksG G T) (hF : F ∈ btBlocksG G T)
    (hEs : (E.subgroupOf G).IsSubnormal) (hFs : (F.subgroupOf G).IsSubnormal) :
    E = F ∨ ⁅E, F⁆ = ⊥ := by
  by_cases hEF : E = F
  · exact Or.inl hEF
  right
  obtain ⟨g, -, hEg⟩ := hE
  obtain ⟨h, -, hFh⟩ := hF
  have hEG : E ≤ G := hEg.le
  have hFG : F ≤ G := hFh.le
  have hEchar : CharTwo E := CharTwo.of_isSubnormal hG hEG hEs
  have hFchar : CharTwo F := CharTwo.of_isSubnormal hG hFG hFs
  have hEX : InClassX ↥E := Glue.inClassX_of_isBTBlock hEg hEchar
  have hFX : InClassX ↥F := Glue.inClassX_of_isBTBlock hFh hFchar
  exact distinct_blocks_commute_of_isBlockOfInX
    (EscapingLocal.isCharacteristicP_of_charTwo hG) ⟨hEG, hEs, hEX⟩ ⟨hFG, hFs, hFX⟩ hEF

theorem six_eleven (hG : CharTwo G) (hE : E ∈ btBlocksG G T) (hF : F ∈ btBlocksG G T)
    (hEs : CFSG.Open.IsSubnormal E G) (hFs : CFSG.Open.IsSubnormal F G) :
    E = F ∨ ⁅E, F⁆ = ⊥ :=
  six_eleven_subgroupOf hG hE hF (isSubnormal_subgroupOf_of_open hEs)
    (isSubnormal_subgroupOf_of_open hFs)

end CFSG.CGT.PushingUpLit.BHS6
