module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Decomp

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem s7_card_derived {a z b : G} (H : S7Hyps a z) (hb : b ∈ orb2A a a) :
    Nat.card ↥(derivedOf (Gxy a b)) = 20160 := by
  have hshape : IsShapeTwoTwoTimesA8 ↥(Gxy a b) := H.fusion3.self.shape_2A b hb
  obtain ⟨e⟩ := nonempty_mulEquiv_derivedOf_of_isShapeTwoTwoTimesA8 hshape
  rw [← Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

theorem s7_not_mem_derived {a z b c : G} (H : S7Hyps a z) (hb : b ∈ orb2A a a)
    (hc : c ∈ sSet a z b 2) : c ∉ derivedOf (Gxy a b) := by
  intro hmem
  have hc' : c ∈ sBase a b ∧ (a * c) ^ 2 = b := by simpa [sSet] using hc
  have hmemGxy : c ∈ Gxy a b :=
    Subgroup.map_subtype_le (_root_.commutator ↥(Gxy a b)) hmem
  have hca : a * c = c * a := (mem_Gx.mp (mem_Gxy.mp hmemGxy).1)
  have ha2 : a ^ 2 = 1 := s7_sq_of_isConj_a H (IsConj.refl a)
  have hc2 : c ^ 2 = 1 := s7_sq_of_isConj_a H hc'.1.1
  have hpow : (a * c) ^ 2 = 1 := by
    rw [Commute.mul_pow hca 2, ha2, hc2, mul_one]
  exact s7_ne_one_of_isConj_a H hb.1 (hc'.2 ▸ hpow)

end CFSG.EvenSporadicStandard.HNRecog.Section3
