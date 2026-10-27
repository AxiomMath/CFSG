module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.QzMem

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem exists_orb2A_inter_orb2A (h : F5Std a z) {b : G} (hb : b ∈ orb2B a z a) :
    ∃ c : G, c ∈ orb2A a a ∧ c ∈ orb2A a b := by
  obtain ⟨hb1, hb2⟩ := hb
  have hab : a * b = b * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb1) (Or.inr hb2)
  have ha2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hz₀a : (a * b) * a = b := by
    rw [mul_assoc, ← hab, ← mul_assoc, haa, one_mul]
  have haz₀ : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have hF₀ : F5Std a (a * b) := h.of_isConj (IsConj.refl a) hb2
  have haQ : a ∈ Qz (a * b) :=
    mem_Qz_of_isConj_mul h hb2 (IsConj.refl a) (by rw [hz₀a]; exact hb1)
  have hne := (hF₀.loc.structX.self.x_struct a haQ (IsConj.refl a)).o1.1.nonempty
  rw [haz₀] at hne
  obtain ⟨c, hc⟩ := hne
  rw [Set.mem_inter_iff] at hc
  exact ⟨c, hc.1, hc.2⟩

theorem exists_orb2A_inter_orb2B (h : F5Std a z) {b : G} (hb : b ∈ orb2B a z a) :
    ∃ d : G, d ∈ orb2A a a ∧ d ∈ orb2B a z b := by
  obtain ⟨hb1, hb2⟩ := hb
  have hab : a * b = b * a :=
    h.mul_comm (Or.inl (IsConj.refl a)) (Or.inl hb1) (Or.inr hb2)
  have ha2 : a ^ 2 = 1 := by rw [← h.typ.orderOf_a]; exact pow_orderOf_eq_one a
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hz₀a : (a * b) * a = b := by
    rw [mul_assoc, ← hab, ← mul_assoc, haa, one_mul]
  have haz₀ : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have hF₀ : F5Std a (a * b) := h.of_isConj (IsConj.refl a) hb2
  have haQ : a ∈ Qz (a * b) :=
    mem_Qz_of_isConj_mul h hb2 (IsConj.refl a) (by rw [hz₀a]; exact hb1)
  have hne := (hF₀.loc.structX.self.x_struct a haQ (IsConj.refl a)).o2.1.nonempty
  rw [haz₀] at hne
  obtain ⟨d, hd⟩ := hne
  rw [Set.mem_inter_iff] at hd
  obtain ⟨hd1, hd2⟩ := hd
  exact ⟨d, hd1, ⟨hd2.1, hb2.trans hd2.2⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
