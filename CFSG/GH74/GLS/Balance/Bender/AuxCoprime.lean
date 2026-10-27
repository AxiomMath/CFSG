module

public import CFSG.GH74.GLS.Balance.Bender.Stmts
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS

theorem bender_q43iii {p : ℕ} [Fact p.Prime] : BenderQ43iii p := by
  intro G _ _ Y A hA hAY hcop
  exact (CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization p Fact.out A Y hA hAY hcop).symm

end CFSG.GH74.GLS.Balance
