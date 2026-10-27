module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Labelled
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Derived
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem rep_z_of_labelled (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    {a z : G} (h : IsF5Type a z) {z₀ b u : ↥(Gx a)}
    (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) (hz₀ : IsConj z (z₀ : G)) :
    IsConj a (a * (z₀ : G)) ∧ (z₀ : G) ∈ derivedOf (Gx a) ∧ a ∈ Qz (z₀ : G) ∧
      CFSG.Open.pCoreOf 2 (Gxy a (z₀ : G)) = Qz (z₀ : G) ⊓ Gx a ∧
      IsShapeTwoTwoSixS5 ↥(Gxy a (z₀ : G)) := by
  have hz₀C : IsExtraspecialPlusByA5WrTwo (Subgroup.centralizer ({(z₀ : G)} : Set G)) :=
    (isF5Type_of_isConj h (IsConj.refl a) hz₀).cent_z
  have hz₀2 : orderOf (z₀ : G) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hz₀
    rw [← hc]
    simpa [MulAut.conj_apply] using (MulEquiv.orderOf_eq (MulAut.conj c) z).trans h.orderOf_z
  have ha2 : orderOf a = 2 := h.orderOf_a
  have hne : a ≠ (z₀ : G) := by
    intro heq
    apply not_isConj_of_isF5Type hI h
    rw [heq]
    exact hz₀.symm
  have ha : a ∈ Gx (z₀ : G) := by
    rw [mem_Gx]
    exact (mem_Gx.1 z₀.2).symm
  have hsh : IsShapeTwoTwoSixS5 ↥(Gxy a (z₀ : G)) := isShapeTwoTwoSixS5_Gxy hF
  have haQ : a ∈ Qz (z₀ : G) :=
    mem_Qz_of_shape hC hz₀C ha (by rw [← orderOf_dvd_iff_pow_eq_one, ha2]) hsh
  exact ⟨isConj_mul_of_mem_Qz hz₀C hz₀2 ha2 hne haQ, mem_derivedOf_of_facts hF, haQ,
    pCoreOf_Gxy_eq hz₀C hz₀2 ha2 hne haQ hsh, hsh⟩

theorem fusion1_of_isF5Type (hI : TwoHSInterface) (hS : SuborbitFacts) (hC : CSideFacts)
    {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z) : Fusion1Facts a z := by
  refine ⟨odd_index_centralizer_of_isExtraspecialPlusByA5WrTwo h.orderOf_z h.cent_z, ?_, ?_⟩
  · obtain ⟨z', b', u', hF⟩ := exists_labelled_facts hI h
    rcases exists_isConj_z_of_labelled hI hS h hF with h1 | h2
    · obtain ⟨c1, c2, c3, c4, c5⟩ := rep_z_of_labelled hI hC h hF h1
      exact ⟨z', b', u', hF, h1, c1, c2, c3, c4, c5⟩
    · have hF' := TwoHSFacts.mul_left_z hF
      obtain ⟨c1, c2, c3, c4, c5⟩ := rep_z_of_labelled hI hC h hF' h2
      exact ⟨GxSelf a * z', b', u', hF', h2, c1, c2, c3, c4, c5⟩
  · intro t ht ht2 hz hat
    exact mem_derivedOf_of_isConj_z hI h ht ht2 hz hat

end CFSG.EvenSporadicStandard.HNRecog.Section3
