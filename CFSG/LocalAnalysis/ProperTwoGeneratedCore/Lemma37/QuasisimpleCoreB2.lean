module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Sylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Crown
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Norm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem PartC.false_of_caseB2
    (h : Setting J Q B) {T R P : Subgroup J}
    (hc : PartC T R P (centralElt J) u) (hT : T ≤ R ⊔ P)
    (hφ : Nonempty (P ≃* QuaternionGroup 2)) (hn : PartC.CaseB2Normalized T P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hTS⟩ := hc.isPGroup.exists_le_sylow
  by_cases hST : (S : Subgroup J) = T
  · exact hc.false_of_caseB2_of_sylow h hT hφ S hST
  · exact hc.false_of_caseB2_of_normalized h hT hφ hn S hTS hST

theorem MaximalStarLift.false_of_caseB2
    (hu : MaximalStarLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) (T : Sylow 2 (quasiNormalizer u))
    (hTB : (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u))
    (hzT : z ∈ partCSylow T) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L)
    (hc : PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (partCSylow T))
    (hT : partCSylow T = partCLeft T L ⊔ partCRight T L)
    (hφ : Nonempty (partCRight T L ≃* QuaternionGroup 2)) : False :=
  hc.false_of_caseB2 h hT.le hφ (hu.caseB2Normalized h hz IH T hTB hzT hL hc hrank hT.le hφ)

theorem BadLift.exists_maximalStarLift
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J))
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) : ∃ v : J, MaximalStarLift B z v :=
  QuasisimpleCore.exists_maximalStarLift ⟨u, hu.starLift h hz IH hrank⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
