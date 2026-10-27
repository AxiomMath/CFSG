module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Main

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem MaximalStarLift.exists_partC_cases
    (hu : MaximalStarLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J)) :
    ∃ T : Sylow 2 (quasiNormalizer u),
      (T : Subgroup (quasiNormalizer u)) ≤ B.subgroupOf (quasiNormalizer u) ∧
      quasiSelf u ∈ (T : Subgroup (quasiNormalizer u)) ∧ z ∈ partCSylow T ∧
      ∃ L : Subgroup (QuasiQuotient u),
        OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L ∧
        PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) u ∧
        3 ≤ CFSG.Open.pRank 2 (partCSylow T) ∧
        ((∃ y ∈ partCSylow T, y ∉ partCLeft T L ⊔ partCRight T L ∧ y * y ∈ partCRight T L ∧
            ∃ n, 5 ≤ n ∧ Nat.card (partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) = 2 ^ n ∧
            Nonempty ((partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) ≃*
              QuaternionGroup (2 ^ (n - 2)))) ∨
          (∃ y ∈ partCSylow T, y ∉ partCLeft T L ⊔ partCRight T L ∧ y * y ∈ partCRight T L ∧
            Nat.card (partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) = 16 ∧
            Nonempty ((partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) ≃* QuaternionGroup 4) ∧
            Nonempty (partCRight T L ≃* QuaternionGroup 2))) := by
  obtain ⟨T, hTB, huT, hzT, L, hL, hP, hr⟩ := hu.toStarLift.exists_partC h hz
  refine ⟨T, hTB, huT, hzT, L, hL, hP, hr, ?_⟩
  rcases hP.cases hr with ⟨hT, n, hn, -, hφ⟩ | ⟨hT, hφ⟩ | hcases
  · exact (PartC.false_of_caseB1 h T hTB hL.normal hP hT.le hn hφ).elim
  · exact (hu.false_of_caseB2 h hz IH T hTB hzT hL hP hr hT hφ).elim
  · exact hcases

theorem BadLift.exists_maximalStarLift_partC_caseC3
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J))
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    ∃ v : J, MaximalStarLift B z v ∧ ∃ T : Sylow 2 (quasiNormalizer v),
      (T : Subgroup (quasiNormalizer v)) ≤ B.subgroupOf (quasiNormalizer v) ∧
      quasiSelf v ∈ (T : Subgroup (quasiNormalizer v)) ∧ z ∈ partCSylow T ∧
      ∃ L : Subgroup (QuasiQuotient v),
        OneComponent (quasiImage B v) (quasiCentral v) (quasiBar v) L ∧
        PartC (partCSylow T) (partCLeft T L) (partCRight T L) (centralElt J) v ∧
        3 ≤ CFSG.Open.pRank 2 (partCSylow T) ∧
        ∃ y ∈ partCSylow T, y ∉ partCLeft T L ⊔ partCRight T L ∧ y * y ∈ partCRight T L ∧
          Nat.card (partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) = 16 ∧
          Nonempty ((partCRight T L ⊔ Subgroup.zpowers y : Subgroup J) ≃* QuaternionGroup 4) ∧
          Nonempty (partCRight T L ≃* QuaternionGroup 2) := by
  obtain ⟨v, hv⟩ := hu.exists_maximalStarLift h hz IH hrank
  obtain ⟨T, hTB, hvT, hzT, L, hL, hP, hr, hcases⟩ := hv.exists_partC_cases h hz IH
  refine ⟨v, hv, T, hTB, hvT, hzT, L, hL, hP, hr, ?_⟩
  rcases hcases with ⟨y, hyT, hy, hyy, n, hn, -, hφ⟩ | hcases
  · exact (hP.false_of_caseC2_of_rank h.perfect T hr hyT hy hyy hn hφ).elim
  · exact hcases

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
