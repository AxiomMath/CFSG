module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Elem
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.ModelTypes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.Translate

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

theorem sixA_type_cases (h : IsF5Type a z) (hx : x ∈ orb6A a a) (ψ : SixAIso a x) {t : G}
    (ht : t ∈ Gxy a x) (ht2 : orderOf t = 2) (htb : t ≠ (a * x) ^ 3) :
    sixAIsA (ψ.f t) ∨ sixAIsB (ψ.f t) ∨ sixAIsC (ψ.f t) ∨ sixAIsD (ψ.f t) := by
  have hty : t ∈ Gxy a (x * (a * x) ^ 3) := sixA_Gxy_le a x ht
  have hs : ψ.f t ∈ Subgroup.centralizer ({sixASigma} : Set (Sym 7)) :=
    ψ.f_mem_cent h hx ht
  obtain ⟨hs2, hs1⟩ := ψ.f_sq_of_orderOf hty ht2
  have hsσ : ψ.f t ≠ sixASigma := ψ.f_ne_sigma h hx hty htb
  exact sixA_model_cover hs hs2 hs1 hsσ

private theorem sixA_info_of_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a)
    (hnc : ¬ IsConj a z) (ψ : SixAIso a x) (i : Fin 5) {t : G}
    (hP : t ∈ sixASet a z x i) (hi : i ≠ 0) :
    t ∈ Gxy a x ∧ orderOf t = 2 ∧ t ≠ (a * x) ^ 3 ∧
      (sixAIsA (ψ.f t) ∨ sixAIsB (ψ.f t) ∨ sixAIsC (ψ.f t) ∨ sixAIsD (ψ.f t)) := by
  have hsub := sixA_subset h hx i hP
  have htb : t ≠ (a * x) ^ 3 := by
    intro he
    have h0 : t ∈ sixASet a z x 0 := by
      rw [he]
      exact Set.mem_singleton _
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 0 i fun h0i => hi h0i.symm) h0) hP
  exact ⟨hsub.1, hsub.2, htb, sixA_type_cases h hx ψ hsub.1 hsub.2 htb⟩

theorem sixA_isA_of_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (hnc : ¬ IsConj a z) (ψ : SixAIso a x) {t : G} (hP : t ∈ sixASet a z x 3) :
    sixAIsA (ψ.f t) := by
  obtain ⟨ht, ht2, htb, hcases⟩ := sixA_info_of_mem h hx hnc ψ 3 hP (by decide)
  rcases hcases with hA | hB | hC | hD
  · exact hA
  · exfalso
    have h1 := sixA_mem_P1_of_isB h hx hS ψ ht ht2 htb hB
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 1 3 (by decide)) h1) hP
  · exfalso
    have h4 := sixA_mem_P4_of_isC h hx hS ψ ht ht2 htb hC
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 4 3 (by decide)) h4) hP
  · exfalso
    have h2 := sixA_mem_P2_of_isD h hx hS ψ ht ht2 htb hD
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 2 3 (by decide)) h2) hP

theorem sixA_isB_of_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (hnc : ¬ IsConj a z) (ψ : SixAIso a x) {t : G} (hP : t ∈ sixASet a z x 1) :
    sixAIsB (ψ.f t) := by
  obtain ⟨ht, ht2, htb, hcases⟩ := sixA_info_of_mem h hx hnc ψ 1 hP (by decide)
  rcases hcases with hA | hB | hC | hD
  · exfalso
    have h3 := sixA_mem_P3_of_isA h hx hS ψ ht ht2 htb hA
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 3 1 (by decide)) h3) hP
  · exact hB
  · exfalso
    have h4 := sixA_mem_P4_of_isC h hx hS ψ ht ht2 htb hC
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 4 1 (by decide)) h4) hP
  · exfalso
    have h2 := sixA_mem_P2_of_isD h hx hS ψ ht ht2 htb hD
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 2 1 (by decide)) h2) hP

theorem sixA_isC_of_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (hnc : ¬ IsConj a z) (ψ : SixAIso a x) {t : G} (hP : t ∈ sixASet a z x 4) :
    sixAIsC (ψ.f t) := by
  obtain ⟨ht, ht2, htb, hcases⟩ := sixA_info_of_mem h hx hnc ψ 4 hP (by decide)
  rcases hcases with hA | hB | hC | hD
  · exfalso
    have h3 := sixA_mem_P3_of_isA h hx hS ψ ht ht2 htb hA
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 3 4 (by decide)) h3) hP
  · exfalso
    have h1 := sixA_mem_P1_of_isB h hx hS ψ ht ht2 htb hB
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 1 4 (by decide)) h1) hP
  · exact hC
  · exfalso
    have h2 := sixA_mem_P2_of_isD h hx hS ψ ht ht2 htb hD
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 2 4 (by decide)) h2) hP

theorem sixA_isD_of_mem (h : IsF5Type a z) (hx : x ∈ orb6A a a) (hS : S7Facts a z)
    (hnc : ¬ IsConj a z) (ψ : SixAIso a x) {t : G} (hP : t ∈ sixASet a z x 2) :
    sixAIsD (ψ.f t) := by
  obtain ⟨ht, ht2, htb, hcases⟩ := sixA_info_of_mem h hx hnc ψ 2 hP (by decide)
  rcases hcases with hA | hB | hC | hD
  · exfalso
    have h3 := sixA_mem_P3_of_isA h hx hS ψ ht ht2 htb hA
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 3 2 (by decide)) h3) hP
  · exfalso
    have h1 := sixA_mem_P1_of_isB h hx hS ψ ht ht2 htb hB
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 1 2 (by decide)) h1) hP
  · exfalso
    have h4 := sixA_mem_P4_of_isC h hx hS ψ ht ht2 htb hC
    exact (Set.disjoint_left.1 (sixA_disjoint h hx hnc 4 2 (by decide)) h4) hP
  · exact hD

end CFSG.EvenSporadicStandard.HNRecog.Section3
