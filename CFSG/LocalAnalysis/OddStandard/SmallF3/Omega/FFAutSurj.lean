module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimFaith
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutBound

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ffSimOmegaAct_bijective_five (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 5) (hs : quadSign Q = 1) :
    Function.Bijective (ffSimOmegaAct hQ (by omega) : ProjSim Q →* MulAut (omegaProj hQ)) :=
  (ffSimOmegaAct_injective hQ (by omega)).bijective_of_nat_card_le
    (by
      rw [ff_natCard_projSim_five hQ hdim]
      exact ff_natCard_mulAut_omegaProj_five_le hQ hdim hs)

theorem ffSimOmegaAct_bijective_six_plus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = 1) :
    Function.Bijective (ffSimOmegaAct hQ (by omega) : ProjSim Q →* MulAut (omegaProj hQ)) :=
  (ffSimOmegaAct_injective hQ (by omega)).bijective_of_nat_card_le
    (by
      rw [ff_natCard_projSim_six_plus hQ hdim hs]
      exact ff_natCard_mulAut_omegaProj_six_plus_le hQ hdim hs)

theorem ffSimOmegaAct_bijective_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1) :
    Function.Bijective (ffSimOmegaAct hQ (by omega) : ProjSim Q →* MulAut (omegaProj hQ)) :=
  (ffSimOmegaAct_injective hQ (by omega)).bijective_of_nat_card_le
    (by
      rw [ff_natCard_projSim_six_minus hQ hdim hs]
      exact ff_natCard_mulAut_omegaProj_six_minus_le hQ hdim hs)

theorem ffSimOmegaAct_bijective (hQ : Q.Nondegenerate)
    (h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1))) :
    Function.Bijective
      (ffSimOmegaAct hQ (by rcases h with ⟨h5, -⟩ | ⟨h6, -⟩ <;> omega) :
        ProjSim Q →* MulAut (omegaProj hQ)) := by
  rcases h with ⟨h5, hs⟩ | ⟨h6, hs | hs⟩
  · exact ffSimOmegaAct_bijective_five hQ h5 hs
  · exact ffSimOmegaAct_bijective_six_plus hQ h6 hs
  · exact ffSimOmegaAct_bijective_six_minus hQ h6 hs

end CFSG.OddStandard.SmallF3.Omega
