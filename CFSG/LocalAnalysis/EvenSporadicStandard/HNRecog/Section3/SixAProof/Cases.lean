module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.TypesOf
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SixAProof.CasesShape

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z x : G}

theorem sixA_case_i (h : IsF5Type a z) (hT : TableVFacts a z) (hS : S7Facts a z)
    (hx : x ∈ orb6A a a) {t : G} (ht : t ∈ orb2B a z a ∩ orb2B a z x) :
    t * (a * x) ^ 3 ∈ orb2BB a z a ∩ orb2BB a z x ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 3) x ∧ IsShapeZ2TimesD8 ↥(Gxyz a t x) := by
  have hnc := sixA_not_isConj hT
  obtain ⟨ψ⟩ := sixA_exists_iso h hx hS
  have ht1 : t ∈ sixASet a z x 1 := by simpa [sixASet] using ht
  have hsub := sixA_subset h hx 1 ht1
  have htb : t ≠ (a * x) ^ 3 := by
    intro hb
    have hb0 : (a * x) ^ 3 ∈ sixASet a z x 0 := by simp [sixASet]
    have ht0 : t ∈ sixASet a z x 0 := by rw [hb]; exact hb0
    have hdisj := sixA_disjoint h hx hnc 0 1 (by decide)
    exact (Set.disjoint_left.1 hdisj ht0) ht1
  have hB := sixA_isB_of_mem h hx hS hnc ψ ht1
  have hu := sixA_mul_b_mem h hx hsub.1 hsub.2 htb
  have hfu : ψ.f ((a * x) ^ 3 * t) = sixASigma * ψ.f t :=
    ψ.f_mul_b h hx (sixA_Gxy_le a x hsub.1)
  have hD : sixAIsD (ψ.f ((a * x) ^ 3 * t)) := by
    rw [hfu]
    exact sixAIsD_of_isB hB
  have hP2 : (a * x) ^ 3 * t ∈ sixASet a z x 2 :=
    sixA_mem_P2_of_isD h hx hS ψ hu.1 hu.2.1 hu.2.2 hD
  have hcomm : t * (a * x) ^ 3 = (a * x) ^ 3 * t := sixA_comm_b_of_mem hsub.1
  refine ⟨?_, sixA_Gxyz_mul_b h hx t, sixA_shape_B h hx ψ hsub.1 hB⟩
  rw [hcomm]
  exact hP2

theorem sixA_case_ii (h : IsF5Type a z) (hT : TableVFacts a z) (hS : S7Facts a z)
    (hx : x ∈ orb6A a a) {t : G} (ht : t ∈ orb2A a a ∩ orb2B a z x) :
    t * (a * x) ^ 3 ∈ orb2B a z a ∩ orb2A a x ∧
      Gxyz a t x = Gxyz a (t * (a * x) ^ 3) x ∧ IsShapeTwoTwoTimesS3 ↥(Gxyz a t x) := by
  have hnc := sixA_not_isConj hT
  obtain ⟨ψ⟩ := sixA_exists_iso h hx hS
  have ht3 : t ∈ sixASet a z x 3 := by simpa [sixASet] using ht
  have hsub := sixA_subset h hx 3 ht3
  have htb : t ≠ (a * x) ^ 3 := by
    intro hb
    have hb0 : (a * x) ^ 3 ∈ sixASet a z x 0 := by simp [sixASet]
    have ht0 : t ∈ sixASet a z x 0 := by rw [hb]; exact hb0
    have hdisj := sixA_disjoint h hx hnc 0 3 (by decide)
    exact (Set.disjoint_left.1 hdisj ht0) ht3
  have hA := sixA_isA_of_mem h hx hS hnc ψ ht3
  have hu := sixA_mul_b_mem h hx hsub.1 hsub.2 htb
  have hfu : ψ.f ((a * x) ^ 3 * t) = sixASigma * ψ.f t :=
    ψ.f_mul_b h hx (sixA_Gxy_le a x hsub.1)
  have hC : sixAIsC (ψ.f ((a * x) ^ 3 * t)) := by
    rw [hfu]
    exact sixAIsC_of_isA hA
  have hP4 : (a * x) ^ 3 * t ∈ sixASet a z x 4 :=
    sixA_mem_P4_of_isC h hx hS ψ hu.1 hu.2.1 hu.2.2 hC
  have hcomm : t * (a * x) ^ 3 = (a * x) ^ 3 * t := sixA_comm_b_of_mem hsub.1
  refine ⟨?_, sixA_Gxyz_mul_b h hx t, sixA_shape_A h hx ψ hsub.1 hA⟩
  rw [hcomm]
  exact hP4

end CFSG.EvenSporadicStandard.HNRecog.Section3
