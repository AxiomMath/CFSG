module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvTwoI
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.InvTwoII
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.FiveE

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem gamma_mem_gamma_of_inv (H : GammaHyps a z) {t : G} (ht : IsConj a t)
    (h : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxy a t) : t ∈ gammaSet a z a :=
  (H.hOdd.self).gamma_of_inv a t (IsConj.refl a) ht h

theorem gamma_inv_of_mem (H : GammaHyps a z) {y t : G}
    (hy : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪ orb5A a a ∪
      orb6A a a) (ht : t ∈ orb2A a y) : ∃ s : G, orderOf s = 2 ∧ s ∈ Gxy a t := by
  rcases hy with ((((((hy | hy) | hy) | hy) | hy) | hy) | hy)
  · obtain ⟨s, hs, hsG⟩ := gamma_inv_one H (by simp only [Set.mem_union]; tauto) ht
    rw [mem_Gxyz] at hsG
    exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
  · obtain ⟨s, hs, hsG⟩ := gamma_inv_one H (by simp only [Set.mem_union]; tauto) ht
    rw [mem_Gxyz] at hsG
    exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
  · obtain ⟨b, hb⟩ := hy.2.2
    have hyb : y ∈ orb2A a b := H.orb2A_symm hy.1 hb.2
    rcases gamma_rows_classes H hb.1.1 hyb ht with htb | htb | htb
    · subst t
      exact ⟨b, H.orderOf_a hb.1.1,
        mem_Gxy.2 ⟨mem_Gx.2 (H.comm_of_orb2A (IsConj.refl a) hb.1), self_mem_Gx b⟩⟩
    · obtain ⟨s, hs, hsG⟩ := gamma_inv_two_i H (Or.inl hy) hb ht htb
      rw [mem_Gxyz] at hsG
      exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
    · exact gamma_inv_two_ii H hb.1 ht.1 htb
  · obtain ⟨s, hs, hsG⟩ := gamma_inv_one H (by simp only [Set.mem_union]; tauto) ht
    rw [mem_Gxyz] at hsG
    exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
  · obtain ⟨s, hs, hsG⟩ := gamma_inv_one H (by simp only [Set.mem_union]; tauto) ht
    rw [mem_Gxyz] at hsG
    exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
  · obtain ⟨s, hs, hsG⟩ := gamma_inv_one H (by simp only [Set.mem_union]; tauto) ht
    rw [mem_Gxyz] at hsG
    exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
  · have hb : (a * y) ^ 3 ∈ orb2A a a ∩ orb2A a y :=
      H.cube_mem_orb2A (IsConj.refl a) hy
    have hyb : y ∈ orb2A a ((a * y) ^ 3) := H.orb2A_symm hy.1 hb.2
    rcases gamma_rows_classes H hb.1.1 hyb ht with htb | htb | htb
    · subst t
      exact ⟨(a * y) ^ 3, H.orderOf_a hb.1.1,
        mem_Gxy.2 ⟨mem_Gx.2 (H.comm_of_orb2A (IsConj.refl a) hb.1), self_mem_Gx _⟩⟩
    · obtain ⟨s, hs, hsG⟩ := gamma_inv_two_i H (Or.inr hy) hb ht htb
      rw [mem_Gxyz] at hsG
      exact ⟨s, hs, mem_Gxy.2 ⟨hsG.1, hsG.2.2⟩⟩
    · exact gamma_inv_two_ii H hb.1 ht.1 htb

theorem gamma_mem_gamma (H : GammaHyps a z) {y t : G} (hy : y ∈ gammaSet a z a)
    (ht : t ∈ orb2A a y) : t ∈ gammaSet a z a := by
  rcases gamma_mem_gammaSet_iff.1 hy with rfl | hy | hy | hy | hy | hy | hy | hy | hy
  · exact gamma_mem_gammaSet_iff.2 (Or.inr (Or.inl ht))
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)
  · obtain ⟨y₁, hy₁, ht₁⟩ := gamma_five_E H hy ht
    have h7 : y₁ ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union] at hy₁ ⊢
      tauto
    exact gamma_mem_gamma_of_inv H ht₁.1 (gamma_inv_of_mem H h7 ht₁)
  · have h7 : y ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪
        orb5A a a ∪ orb6A a a := by
      simp only [Set.mem_union]
      tauto
    exact gamma_mem_gamma_of_inv H ht.1 (gamma_inv_of_mem H h7 ht)

end CFSG.EvenSporadicStandard.HNRecog.Section3
