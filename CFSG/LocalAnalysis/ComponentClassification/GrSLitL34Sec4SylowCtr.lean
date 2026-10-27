module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem l34SylowCenterCyclicFact :
    L34SylowCenterCyclicFact := by
  intro G _ _ J P hJ hL hP hcyc hc4 u huP hu
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg4 : orderOf g = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hc4]
  set z : G := (g : G) with hzdef
  have hz : z ∈ P ⊓ zStarIn J := g.2
  have hz2 : z * z ≠ 1 := fun h => by
    have h2 : g ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, pow_two]; exact h)
    have := orderOf_le_of_pow_eq_one (by norm_num) h2
    omega
  have hk4 : ∃ e ∈ q.ker, e * e ≠ 1 := by
    refine ⟨jq J ⟨z, hP.1 (mem_inf.mp hz).1⟩, by
      rw [hqker]; exact (mem_zStarIn_iff _).1 (mem_inf.mp hz).2, fun h => hz2 ?_⟩
    refine eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem (mem_inf.mp hz).1 (mem_inf.mp hz).1) ?_
    show jq J (⟨z, hP.1 (mem_inf.mp hz).1⟩ * ⟨z, hP.1 (mem_inf.mp hz).1⟩) = 1
    rw [map_mul]
    exact h
  have hq1 := hQ.q_eq_one_of_central hk4 ((hT _).2 ⟨u, huP, _, rfl⟩)
    (e := jq J ⟨u, hP.1 huP⟩) fun e' he' => by
      obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e').1 he'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hu p hpP)
  refine (mem_zStarIn_iff (hP.1 huP)).2 ?_
  rw [← hqker]
  exact hq1

end CFSG.ComponentClassification.GrSLit
