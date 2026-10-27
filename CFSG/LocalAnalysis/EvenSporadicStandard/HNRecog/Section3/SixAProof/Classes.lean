module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ClassesModel

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

theorem sixA_classes (h : IsF5Type a z) (hT : TableVFacts a z) (hS : S7Facts a z)
    (hx : x ∈ orb6A a a) :
    IsOrbitPartition (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} (sixASet a z x) := by
  have hnc : ¬ IsConj a z := sixA_not_isConj hT
  obtain ⟨ψ⟩ := sixA_exists_iso h hx hS
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun i => sixA_subset h hx i
  · intro c hc
    by_cases hcb : c = (a * x) ^ 3
    · exact ⟨0, by simpa [sixASet] using hcb⟩
    · rcases sixA_type_cases h hx ψ hc.1 hc.2 hcb with hA | hB | hC | hD
      · exact ⟨3, sixA_mem_P3_of_isA h hx hS ψ hc.1 hc.2 hcb hA⟩
      · exact ⟨1, sixA_mem_P1_of_isB h hx hS ψ hc.1 hc.2 hcb hB⟩
      · exact ⟨4, sixA_mem_P4_of_isC h hx hS ψ hc.1 hc.2 hcb hC⟩
      · exact ⟨2, sixA_mem_P2_of_isD h hx hS ψ hc.1 hc.2 hcb hD⟩
  · exact fun i j hij => sixA_disjoint h hx hnc i j hij
  · intro i
    exact ⟨fun k hk c hc => sixA_conj_mem h hx i hk hc, sixA_nonempty h hx hS ψ i,
      fun c hc c' hc' => sixA_transitive h hx hS hnc ψ i hc hc'⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
