module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4B
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IR4D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


theorem z4iData (hz : Ctx4Z t L S x₁ x₂ lam rho tau)
    (hsyl : IsSylowIn 2 (ctxQ t tau x₁ x₂ rho) (ctxCQ t tau x₁ x₂ rho))
    (hrel : (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 4) :
    ∃ (N : Subgroup ↥(ctxNQ t tau x₁ x₂ rho)) (_ : N.Normal) (V' : Subgroup G),
      S4B.Z4IData N (hz.z4iSub (ctxQ t tau x₁ x₂ rho)) (hz.z4iSub (ctxYq t tau x₁ x₂ rho))
        (hz.z4iSub (fourGrp x₁ x₂)) (hz.z4iSub V') (hz.z4iSub (baseGrp x₁ x₂))
        (hz.z4iSub (ctxKI t tau x₁ x₂ rho)) hz.z4iRho hz.z4iT hz.z4iTau hz.z4iLam := by
  obtain ⟨Ng, hN⟩ := hz.z4i_exists_odd hsyl
  obtain ⟨V', v₁, v₂, hV⟩ := hz.data_V
  exact ⟨hz.z4iSub Ng, hz.z4i_normal_N hN, V',
    S4B.Z4IData.of_parts (hz.z4iPartB hN hV hrel) (hz.z4iPartC hN hV) hz.z4iPartD⟩

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
