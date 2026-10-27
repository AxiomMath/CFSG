module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual5
import CFSG.LocalAnalysis.RankThreeUC.TheoremDNonsolvable

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81Residual6Gen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → ∀ T : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ¬ thompsonSubgroup T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) →
      (p = 3 ∨ ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) →
      ¬ normalizer (T : Set G) ≤
        normalizer ((T ⊓ centralizer (uCore M T : Set G) : Subgroup G) : Set G) →
      (∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ T → ∃ n ∈ normalizer (T : Set G),
        CFSG.Open.pRank p
          (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) ≤ 1) →
      2 ≤ CFSG.Open.pRank p (thompsonCore M T) →
      2 ≤ CFSG.Open.pRank p (CFSG.Quasithin.thompsonJ M) →
      rankThreeGamma 1 p (P : Subgroup G) ≤ M →
      (p = 3 → Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T)) →
        ¬ normalizer (T : Set G) ≤ normalizer
          ((uCore M T ⊓ centralizer (CFSG.Quasithin.thompsonJ T : Set G) : Subgroup G) :
            Set G)) →
      normalizer (T : Set G) ≤ M

theorem agl81Residual5Gen_of_residual6Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual6Gen G W) : AGL81Residual5Gen G W := by
  intro p P M hw T hT hJ hJe hTI hC hsol hN hY hCore hJM _ hN'
  obtain ⟨hp, hw'⟩ := hW p P M hw
  exact hR p P M hw T hT hJ hJe hTI hC hsol hN hY hCore hJM
    (hw'.gamma_one_le_of_residual hS hp hT hJe hC hsol) hN'

theorem agl81TheoremDGen_of_residual6Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual6Gen G W) : AGL81TheoremDGen G W :=
  agl81TheoremDGen_of_residual5Gen hS hW (agl81Residual5Gen_of_residual6Gen hS hW hR)

end CFSG.LocalAnalysis.RankThreeUC
