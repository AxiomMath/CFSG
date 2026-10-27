module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.WitTransport

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.CompatModel

private theorem orderOf_eq_four_of_sq {G : Type} [Group G] {g : G} (h : orderOf (g ^ 2) = 2) :
    orderOf g = 4 := by
  have h1 : ¬ g ^ 2 ^ 1 = 1 := by
    intro e
    rw [pow_one] at e
    rw [e, orderOf_one] at h
    exact absurd h (by norm_num)
  have h2 : g ^ 2 ^ (1 + 1) = 1 := by
    have e := pow_orderOf_eq_one (g ^ 2)
    rw [h] at e
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul]
    exact e
  simpa using orderOf_eq_prime_pow h1 h2

section Cert


theorem wit4a_holds : Wit4A := by
  intro G _ a z h x hx d hd t ht htd
  obtain ⟨hxa, hxz⟩ := hx
  obtain ⟨hdA, hdX⟩ := hd
  have hda : d ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) hdA
  have hdx : d ∈ Gx x := h.mem_Gx_of_orb2A hxa hdX
  have hadc : a * d = d * a := mem_Gx.1 hda
  have htx : x * t = t * x := mem_Gx.1 (mem_Gxyz.1 ht.1).2.2
  have hnc : a * x ≠ x * a := by
    intro e
    have ha2 : a ^ 2 = 1 := by simpa [h.typ.orderOf_a] using pow_orderOf_eq_one a
    have hx2 : x ^ 2 = 1 := by
      simpa [h.orderOf_eq_two (Or.inl hxa)] using pow_orderOf_eq_one x
    have hsq : (a * x) ^ 2 = 1 := by
      rw [Commute.mul_pow (show Commute a x from e), ha2, hx2, one_mul]
    have h2 := h.orderOf_eq_two (Or.inr hxz)
    rw [hsq, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hta : t ≠ a := fun e => hnc (by rw [e] at htx; exact htx.symm)
  have hta' : t ≠ a * d := by
    intro e
    apply hnc
    rw [e] at htx
    apply mul_right_cancel (b := d)
    calc a * x * d = a * (x * d) := mul_assoc _ _ _
      _ = a * (d * x) := by rw [mem_Gx.1 hdx]
      _ = a * d * x := (mul_assoc _ _ _).symm
      _ = x * (a * d) := htx.symm
      _ = x * a * d := (mul_assoc _ _ _).symm
  have hay : a ∈ orb2A a d := ⟨IsConj.refl a, by rw [← hadc]; exact hdA.2⟩
  have ht' : t ∈ InvIn (Gxy a d) :=
    ⟨mem_Gxy.2 ⟨(mem_Gxyz.1 ht.1).1, (mem_Gxyz.1 ht.1).2.1⟩, ht.2⟩
  obtain ⟨w, hw1, hw2, hw3, hw4, hw5⟩ := exists_vertex_in_Gx h hdA.1 hay ht' htd hta hta'
  refine ⟨w, mem_Gxy.2 ⟨(mem_Gxy.1 hw1).2, (mem_Gxy.1 hw1).1⟩, hw2, hw3, ?_, ?_, ?_⟩
  · rintro ⟨-, hzw⟩
    have h4 := orderOf_eq_four_of_sq (h.orderOf_eq_two (Or.inr hzw))
    exact not_isConj_of_isF5Type h.iface h.typ ((hw5 h4).trans hzw.symm)
  · exact fun hw => hw4 hw.2.1
  · exact fun hw => hw4 hw.2.1

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
