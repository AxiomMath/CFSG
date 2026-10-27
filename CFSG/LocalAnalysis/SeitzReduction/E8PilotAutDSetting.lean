module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalKernel
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6CascadeFinal
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Model

omit [Finite G] in
theorem lieModel_quotient_center_E8 (hZ : center L = ⊥) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) :
    LieModel (L ⧸ center L) .E8 0 2 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hKc
  exact Or.inr (Or.inl ⟨rfl, by decide,
    ⟨Nat.prime_two, F4Pilot.one_le_of_natCard_eq_two_pow hKc, rfl⟩, K, inferInstance,
      inferInstance, hKc, ⟨(quotientCenterMulEquiv hZ).trans (e.trans
        ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
          QuotientGroup.quotientBot).symm)⟩⟩)

end Model

section Setting

theorem inf_centralizer_eq_zpowers_E8 (hset : SeitzSetting G L) {f : ℕ} {K : Type} [Field K]
    (hKc : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E8 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
  inf_centralizer_eq_zpowers_of_exceptional exceptionalHypothesisOne hset.standardSetting
    hset.center_eq_bot (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (lieModel_quotient_center_E8 hset.center_eq_bot hKc e) htC ht

end Setting

end CFSG.SeitzReduction.E8Pilot
