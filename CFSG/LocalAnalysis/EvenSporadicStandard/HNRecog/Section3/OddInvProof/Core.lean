module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Three
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.OddInvProof.Five

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem oddInv_core {G : Type} [Group G] [Finite G] {a z : G} (h : IsF5Type a z)
    (hF3 : Vert Fusion3Facts a z) (hOrb : GzOrbitFacts a z) (hCls : GzClassFacts a z)
    (hNo : GzNoFacts a z) (hY4a : Y4aFacts a z) (hSGz : StructGzFacts a z)
    (hPar : ParityFacts a z) (hT5 : TableVFacts a z) {x : G} (hx : IsConj a x)
    (haz : a ∈ Gx z) (hxz : x ∈ Gx z) (hodd : Odd (orderOf (a * x))) :
    ∃ t : G, IsConj a t ∧ t ∈ Gxyz a z x := by
  by_cases hne : x = a
  · refine ⟨a, IsConj.refl a, mem_Gxyz.2 ⟨self_mem_Gx a, haz, ?_⟩⟩
    rw [hne]
    exact self_mem_Gx a
  obtain ⟨haz2, -, haQ, hxQ⟩ := oddInv_step_one h hF3 hCls hPar hT5 hx haz hxz hodd hne
  have hnc : ¬ IsConj a (a * z) := fun h' => oddInv_not_isConj hT5 (h'.trans haz2.symm)
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  have ha2 : a ^ 2 = 1 := oddInv_sq_eq_one h (IsConj.refl a)
  have hx2 : x ^ 2 = 1 := oddInv_sq_eq_one h hx
  have hua : barOf z ⟨a, haz⟩ ∉ _root_.commutator (Gbar z) :=
    oddInv_barOf_not_mem_commutator h hOrb hNo haz haQ (IsConj.refl a)
  have hux : barOf z ⟨x, hxz⟩ ∉ _root_.commutator (Gbar z) :=
    oddInv_barOf_not_mem_commutator h hOrb hNo hxz hxQ hx
  have hua2 := oddInv_barOf_sq_eq_one haz ha2
  have hux2 := oddInv_barOf_sq_eq_one hxz hx2
  let σ : ↥(Gx z) := ⟨a * x, Subgroup.mul_mem _ haz hxz⟩
  have hσbar : barOf z σ = barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩ := rfl
  have hord : orderOf (barOf z σ) = orderOf (a * x) := oddInv_orderOf_barOf σ hodd
  have hodd' : Odd (orderOf (barOf z ⟨a, haz⟩ * barOf z ⟨x, hxz⟩)) := by
    rw [← hσbar, hord]
    exact hodd
  rcases oddInv_gbar_orderOf e hua hux hua2 hux2 hodd' with h1 | h3 | h5
  · exfalso
    rw [← hσbar, hord, orderOf_eq_one_iff] at h1
    apply hne
    rw [eq_inv_of_mul_eq_one_right h1]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
  · have hcard := oddInv_gbar_card_three e hua hux hua2 hux2 h3
    rw [← hσbar, hord] at h3
    exact oddInv_three h hCls hY4a hSGz hx haz hxz haz2 hnc h3 hcard
  · have hcard := oddInv_gbar_card_five e hua hux hua2 hux2 h5
    rw [← hσbar, hord] at h5
    exact oddInv_five h hOrb hNo hSGz hx haz hxz haQ hxQ hnc h5 hcard

end CFSG.EvenSporadicStandard.HNRecog.Section3
