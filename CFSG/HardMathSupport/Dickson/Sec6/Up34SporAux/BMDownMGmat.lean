module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMInvM
public import CFSG.YGroups.Y443.Tri.AssemblyLit
public import CFSG.Milestones.CL_LIT_Monster_existence_Griess_Conway

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.BM

open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator.YS08

section Inv

theorem noL3Comp_gmat_of_invertedByTwoA {s : Gmat} (hs : orderOf s = 3) (hinv : InvertedByTwoA s) :
    NoL3Comp (Subgroup.centralizer ({s} : Set Gmat)) := by
  haveI : Finite Gmat := generated_rational_group_finite_simple.2.2
  have hE := CFSG.Milestones.cl_lit_monster_existence_griess_conway
  haveI : Finite MGriess := hE.1.1
  let φ : Gmat ≃* MGriess :=
    (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
  have hs' : orderOf (φ s) = 3 := by rwa [MulEquiv.orderOf_eq]
  have h1 := noL3Comp_of_invertedByTwoA hE hs' (hinv.map φ)
  have h2 := noL3Comp_map_mulEquiv φ.symm h1
  rwa [CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv,
    MulEquiv.symm_apply_apply] at h2

end Inv

end CFSG.HardMathSupport.Dickson.Sec6.BM
