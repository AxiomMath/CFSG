module

public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
import all CFSG.RankThree.SteinbergR3ESmallReeCosetDescent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.RankThree CFSG.LocalAnalysis.ComponentInitial


theorem ree_coset_descent_of_field {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσp : orderOf σ = p) (x : ReeTag.G2.reeGamma K a)
    (hβ₁p : (MulAut.conj x * ReeTag.G2.reeGammaFieldAut K a σ) ^ p = 1) :
    ∃ δ : MulAut (ReeTag.G2.reeGamma K a),
      δ * (MulAut.conj x * ReeTag.G2.reeGammaFieldAut K a σ) * δ⁻¹ =
        ReeTag.G2.reeGammaFieldAut K a σ :=
  (CFSG.RankThree.small_Ree_coset_descent_data ha hK hp hp2 σ hσp x hβ₁p).imp fun _ h => h.1

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
