module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureB
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureBCo
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017BabyTwistPureBFi

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS CFSG.HardMathSupport.Timmesfeld.SporadicBalance


theorem babyNoPureFourAt_one_of_twoB_d0
    (hD0 : ∃ t₁ : NativeSporadic.B, BabyInv 1 t₁ ∧ ∃ D₀ : Subgroup NativeSporadic.B,
      D₀ ≤ Subgroup.centralizer ({t₁} : Set NativeSporadic.B) ∧ IsElemAbelian 3 D₀ ∧
      Nat.card D₀ = 3 ^ 4 ∧ ∃ y ∈ D₀, IsConj y (BThreeFi23.phiB (BThreeFi23.t3 0))) :
    BabyNoPureFourAt 1 :=
  babyNoPureFourAt_one_of (fun _ _ h₁ h₂ hc₁ hc₂ =>
    BabyTwistCo.co2_exists_conj_elemAbelian_four h₁ h₂ hc₁ hc₂) hD0

theorem babyNoPureFourAt_one_holds : BabyNoPureFourAt 1 :=
  babyNoPureFourAt_one_of_twoB_d0 exists_twoB_d0

end CFSG.LocalAnalysis.GLTheoremA.H1017
