module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual2
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseC

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

@[expose] def AGL81Residual4Gen (G : Type) [Group G] [Finite G]
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
      (p = 3 → Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T)) →
        rankThreeGamma 1 p (P : Subgroup G) ≤ M) →
      normalizer (T : Set G) ≤ M

theorem IsWitnessGen.gamma_one_le_of_solvable_quotient (hS : StandingGen G)
    {P : Sylow 3 G} (hp : IsWitnessPrime 3 P) {M : Subgroup G} (hw : IsWitnessGen 3 P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hC : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank 3 (normalizer (C : Set G)) ≤ 1)
    (hsolv : Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) :
    rankThreeGamma 1 3 (P : Subgroup G) ≤ M := by
  rcases hw.u1 with h | ⟨hB, -⟩ | ⟨-, hc⟩
  · exact h
  · exact absurd hB (by norm_num)
  · exact absurd hc (hw.not_clauseC_of_solvable_quotient hS hp hT hJe hC hsolv)

theorem agl81Residual3Gen_of_residual4Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual4Gen G W) : AGL81Residual3Gen G W := by
  intro p P M hw T hT hJ hJe hTI hC hsol hN hY hCore hJM
  obtain ⟨hp, hw'⟩ := hW p P M hw
  refine hR p P M hw T hT hJ hJe hTI hC hsol hN hY hCore hJM ?_
  rintro rfl hsolv
  exact hw'.gamma_one_le_of_solvable_quotient hS hp hT hJe hC hsolv

theorem agl81TheoremDGen_of_residual4Gen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81Residual4Gen G W) : AGL81TheoremDGen G W :=
  agl81TheoremDGen_of_residual3Gen hS hW (agl81Residual3Gen_of_residual4Gen hS hW hR)

end CFSG.LocalAnalysis.RankThreeUC
