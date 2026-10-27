module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34L45c
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalHallConfinement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34_exists_maximal_not_le (hS : Setting G) (hU0 : FullCoreLocal G)
    (hK1 : KFactL34TwoSignalizer) (hp : 3 ∈ rankThreeSigmaA G)
    {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M) {x : G}
    (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsL34Normal M x J) {U : Subgroup G}
    (hU : IsElemAbelian 3 U) (hUc : Nat.card U = 3 ^ 2) (hUP : U ≤ (P : Subgroup G))
    (hxU : x ∈ U) (hUJ : U ⊓ J ≠ ⊥) :
    ∃ S₁ : Subgroup G, rankTwoMaximalInvariantTwoSubgroup U S₁ ∧ ¬ S₁ ≤ M ∧
      invariantTwoMaximalWithin U J (S₁ ⊓ J) := by
  obtain ⟨A, hA, hAM⟩ := l34l45_exists_within_not_le hS hU0 hK1 hp hM hgen hJ hU hUc hUP hxU hUJ
  obtain ⟨S₁, hAS₁, hS₁⟩ := exists_maximal_invariant_two_subgroup_containing U A hA.2.1 hA.2.2.1
  refine ⟨S₁, hS₁, fun h => hAM (hAS₁.trans h), ?_⟩
  have hUN : U ≤ normalizer (J : Set G) := fun g hg =>
    hJ.centralizer_le (mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hU.1.is_comm.comm ⟨g, hg⟩ ⟨x, hxU⟩)))
  have hSJ : S₁ ⊓ J = A := hA.2.2.2 (S₁ ⊓ J) inf_le_right (hS₁.1.to_le inf_le_left)
    (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨hS₁.2.1 hg, hUN hg⟩)
    (le_inf hAS₁ hA.1)
  rw [hSJ]
  exact hA

end CFSG.LocalAnalysis.RankThreeTheoremC
