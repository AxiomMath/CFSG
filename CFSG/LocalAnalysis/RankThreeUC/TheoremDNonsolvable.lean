module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDResidual4

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isSolvable_of_not_isSolvable_autOn {M V : Subgroup G}
    (h : M ≤ normalizer (V : Set G))
    (hns : ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M V)) : ¬ Group.IsSolvable ↥M := by
  intro hM
  have : Group.IsSolvable ↥(M.subgroupOf (normalizer (V : Set G))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe h).toMonoidHom) (Subgroup.subgroupOfEquivOfLe h).injective
  exact hns (Group.isSolvable_of_surjective
    (f := (CFSG.Quasithin.conjAct V).subgroupMap (M.subgroupOf (normalizer (V : Set G))))
    ((CFSG.Quasithin.conjAct V).subgroupMap_surjective _))

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.gamma_one_le_of_not_isSolvable
    (hw : IsWitnessGen p P M) (hM : ¬ Group.IsSolvable ↥M) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M := by
  rcases hw.u1 with h | ⟨-, hs⟩ | ⟨-, hs, -⟩
  exacts [h, absurd hs hM, absurd hs hM]

theorem gamma_one_le_of_not_isSolvable (hw : IsWitness p P M) (hM : ¬ Group.IsSolvable ↥M) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M :=
  IsWitnessGen.gamma_one_le_of_not_isSolvable hw.toGen hM

theorem _root_.CFSG.LocalAnalysis.RankThreeUC.IsWitnessGen.gamma_one_le_of_residual
    (hS : StandingGen G) (hp : IsWitnessPrime p P) (hw : IsWitnessGen p P M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hC : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1)
    (hsol : p = 3 ∨ ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M := by
  by_cases hsolv : Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))
  · obtain rfl : p = 3 := hsol.resolve_right (not_not.mpr hsolv)
    exact hw.gamma_one_le_of_solvable_quotient hS hp hT hJe hC hsolv
  · exact hw.gamma_one_le_of_not_isSolvable
      (not_isSolvable_of_not_isSolvable_autOn (le_normalizer_uCore M T) hsolv)

theorem gamma_one_le_of_residual (hS : Standing G) (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hC : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1)
    (hsol : p = 3 ∨ ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T))) :
    rankThreeGamma 1 p (P : Subgroup G) ≤ M :=
  IsWitnessGen.gamma_one_le_of_residual hS.toGen (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen
    hT hJe hC hsol

end IsWitness

end CFSG.LocalAnalysis.RankThreeUC
