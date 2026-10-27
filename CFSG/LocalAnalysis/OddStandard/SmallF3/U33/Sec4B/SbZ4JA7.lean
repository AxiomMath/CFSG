module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JA6

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


theorem z4jHData (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng V' : Subgroup G} {v₁ v₂ : G}
    (hN : Z4IOdd t tau x₁ x₂ rho Ng) (hV : Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂)
    (hv₁ : v₁ ∈ ctxQ t tau x₁ x₂ rho) (hv₂ : v₂ ∈ ctxQ t tau x₁ x₂ rho)
    (hrel : (ctxCQ t tau x₁ x₂ rho).relIndex (ctxKI t tau x₁ x₂ rho) = 1)
    [(hz.z4iSub Ng).Normal] :
    S4B.ZJData ((hz.z4iSub (ctxQ t tau x₁ x₂ rho)).map (S4B.z4iπ (hz.z4iSub Ng)))
      ((hz.z4iSub (ctxYq t tau x₁ x₂ rho)).map (S4B.z4iπ (hz.z4iSub Ng)))
      ((hz.z4iSub (fourGrp x₁ x₂)).map (S4B.z4iπ (hz.z4iSub Ng)))
      ((hz.z4iSub V').map (S4B.z4iπ (hz.z4iSub Ng)))
      ((hz.z4iSub (baseGrp x₁ x₂)).map (S4B.z4iπ (hz.z4iSub Ng)))
      (S4B.z4iπ (hz.z4iSub Ng) hz.z4iRho) (S4B.z4iπ (hz.z4iSub Ng) hz.z4iT)
      (S4B.z4iπ (hz.z4iSub Ng) hz.z4iTau) (S4B.z4iπ (hz.z4iSub Ng) hz.z4iLam)
      (S4B.z4iπ (hz.z4iSub Ng) hz.z4jY) (S4B.z4iπ (hz.z4iSub Ng) hz.z4jZ)
      (S4B.z4iπ (hz.z4iSub Ng) (hz.z4jV hv₁)) (S4B.z4iπ (hz.z4iSub Ng) (hz.z4jV hv₂)) := by
  have hX := hz.z4jData hN hV hv₁ hv₂
  exact
    { toZJBase := hX.toZJBase
      K_triv := S4B.z4j_K_triv_of hX.odd_N (S4B.z4j_isPGroup_of_sq hX.Y_sq)
        (hz.z4j_K_triv_X hN hrel)
      tt_sylow := S4B.z4j_tt_sylow_of hX.odd_N (hz.z4j_cent_N_t hN) hX.t_rho hX.tau_rho hX.t_sq
        hX.tau_sq hX.t_tau hz.z4j_tt_odd
      two_pow_ten := S4B.z4j_two_pow_of hX.odd_N hz.z4j_two_pow_ten }

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
