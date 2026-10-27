module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModelBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

theorem cyclicFourCenter :
    ∀ (G : Type) [Group G] [Finite G] (J P : Subgroup G), ⁅J, J⁆ = J →
      IsL34Type (J ⧸ Open.fusionZStar J) → IsSylowTwoIn P J →
      IsCyclic ↥(P ⊓ zStarIn J) → Nat.card ↥(P ⊓ zStarIn J) = 4 →
      ∀ y ∈ P, (∀ p ∈ P, p * y = y * p) → y ∈ zStarIn J := by
  intro G _ _ J P hJ hL hP hcyc h4 y hy hc
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  obtain ⟨ζe, -⟩ := exists_zeta hP hqker
  have hkcyc : IsCyclic q.ker := isCyclic_of_surjective ζe.toMonoidHom ζe.surjective
  have hk4 : Nat.card q.ker = 4 := by rw [← Nat.card_congr ζe.toEquiv, h4]
  obtain ⟨g, hg1, -⟩ := cyclic_four hk4
  have hq1 := hQ.q_eq_one_of_central ⟨g, g.2, fun h => hg1 (Subtype.ext h)⟩
    ((hT _).2 ⟨y, hy, _, rfl⟩) (e := jq J ⟨y, hP.1 hy⟩) fun e' he' => by
      obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e').1 he'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hc p hpP).symm
  rw [mem_zStarIn_iff (hP.1 hy), ← hqker]
  exact hq1

end CFSG.ComponentClassification.GrSLit.L34Facts
