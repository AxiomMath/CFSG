module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.InvGa
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.StructGz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

theorem tableV_cover_two {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) {c : G} (hc : IsConj a c) (hord : orderOf (a * c) = 2) :
    c ∈ orb2A a a ∨ c ∈ orb2B a z a := by
  have ha2 : a ^ 2 = 1 := by rw [← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hc2 : c ^ 2 = 1 := by
    rw [← perp_orderOf_of_isConj_a h hc]; exact pow_orderOf_eq_one c
  have hac2 : (a * c) ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one (a * c)
  have hcomm : a * c = c * a := comm_of_sq_mul ha2 hc2 hac2
  have hsym : (a * c) * a = a * (a * c) := by
    calc (a * c) * a = a * (c * a) := mul_assoc a c a
      _ = a * (a * c) := by rw [← hcomm]
  have ht1 : a * c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  rcases isConj_of_commute hF1 hF2 (IsConj.refl a) hsym hac2 ht1 with h | h
  · exact Or.inl ⟨hc, h⟩
  · exact Or.inr ⟨hc, h⟩

theorem tableV_cover_four_A (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hF1 : Vert Fusion1Facts a z) (hT3 : Vert TableIIIFacts a z) {c x : G} (hc : IsConj a c)
    (hord : 2 < orderOf (a * c)) (hxz : IsConj z x) (hax : a * x = x * a)
    (hax' : IsConj a (a * x)) (hcx : c * x = x * c) (hcx' : IsConj a (c * x)) :
    c ∈ orb4A a z a := by
  have haa : a * a = 1 := by
    rw [← pow_two, ← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_z h hxz
  have haQ : a ∈ Qz x :=
    mem_Qz_of_isConj_mul hI h hF1 (IsConj.refl a) hxz hax hax'
  have hcQ : c ∈ Qz x := mem_Qz_of_isConj_mul hI h hF1 hc hxz hcx hcx'
  have hcbase : c ∈ tab3Base a x a := by
    refine ⟨hcQ, hc, ?_, ?_⟩
    · intro hca
      rw [hca, haa, orderOf_one] at hord
      omega
    · intro hcax
      have h1 : orderOf (a * c) = 2 := by
        rw [hcax]
        have : a * (a * x) = x := by rw [← mul_assoc, haa, one_mul]
        rw [this, hx2]
      rw [h1] at hord
      omega
  have hpart := (hT3 a x (IsConj.refl a) hxz).partition a haQ (IsConj.refl a)
  obtain ⟨i, hi⟩ := hpart.cover c hcbase
  fin_cases i <;> simp [tab3Set, -isConj_iff] at hi
  · exact absurd (perp_orderOf_of_isConj_a h hi.2) (by omega)
  · exact absurd (perp_orderOf_of_isConj_z h (hxz.trans hi.2)) (by omega)
  · exact ⟨hc, by rw [hi.2]; exact hxz⟩

theorem tableV_cover_four_B_six (hI : TwoHSInterface) {a z : G} (h : IsF5Type a z)
    (hT4 : TableIVFacts a z) {c x : G} {m : ℕ} (hc : IsConj a c) (hm : orderOf (a * c) = 2 * m)
    (hm2 : 2 ≤ m) (hx : x = (a * c) ^ m) (hxa : IsConj a x) (hax' : IsConj a (a * x))
    (hcx : c * x = x * c) (hcx' : IsConj a (c * x)) : c ∈ orb4B a a ∨ c ∈ orb6A a a := by
  have haa : a * a = 1 := by
    rw [← pow_two, ← h.orderOf_a]; exact pow_orderOf_eq_one a
  have hge4 : 4 ≤ orderOf (a * c) := by rw [hm]; omega
  have hne2 : orderOf (a * c) ≠ 2 := by omega
  have hxmem : x ∈ orb2A a a := ⟨hxa, hax'⟩
  have hcbase : c ∈ sBase a x := by
    refine ⟨hc, ?_, ?_, ?_⟩
    · rw [← hcx]; exact hcx'
    · intro hca
      have h1 : orderOf (a * c) = 1 := by rw [hca, haa, orderOf_one]
      rw [h1] at hge4
      omega
    · intro hcax
      have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hxa
      have h1 : orderOf (a * c) = 2 := by
        rw [hcax]
        have : a * (a * x) = x := by rw [← mul_assoc, haa, one_mul]
        rw [this, hx2]
      rw [h1] at hge4
      omega
  obtain ⟨i, hi⟩ := (hT4.partition x hxmem).cover c hcbase
  fin_cases i <;> simp [sSet, -isConj_iff] at hi
  · exact absurd (perp_orderOf_of_isConj_a h hi.2) hne2
  · exact absurd (perp_orderOf_of_isConj_z h hi.2) hne2
  · exact Or.inl ⟨hc, by rw [hi.2]; exact hxa⟩
  · exfalso
    have hsq2 : orderOf ((a * c) ^ 2) = 2 := perp_orderOf_of_isConj_z h hi.2
    have hsq_m : orderOf ((a * c) ^ 2) = m := by
      rw [orderOf_pow_of_dvd (x := a * c) (n := 2) (by norm_num)
        (by rw [hm]; exact dvd_mul_right 2 m), hm]
      omega
    have hm_eq : m = 2 := by omega
    have hxeq : x = (a * c) ^ 2 := by rw [hx, hm_eq]
    have hzx : IsConj z x := by rw [hxeq]; exact hi.2
    exact absurd (hxa.trans hzx.symm) (not_isConj_of_isF5Type hI h)
  · exfalso
    rw [hm] at hi
    omega
  · exact Or.inr ⟨hc,
      perp_orderOf_eq_six (by rw [hi.2]; exact perp_orderOf_of_isConj_a h hxa) hne2,
      by rw [hi.2]; exact hxa⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
