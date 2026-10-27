module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVProof.TableVBasic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G : Type} [Group G] {a z : G}

theorem cp_mul_self_eq_one (h : F5Std a z) {x : G}
    (hx : IsConj a x ∨ IsConj z x) : x * x = 1 := by
  have h1 := pow_orderOf_eq_one x
  rw [h.orderOf_eq_two hx] at h1
  simpa [pow_two] using h1

theorem cp_ne_self_of_orb2A (h : F5Std a z) {b : G} (hb : b ∈ orb2A a a) : b ≠ a := by
  intro hba
  have h1 : IsConj a 1 := by
    have h2 := hb.2
    rwa [hba, cp_mul_self_eq_one h (Or.inl (IsConj.refl a))] at h2
  have h3 : a = 1 := isConj_one_left.1 h1
  have h4 := h.typ.orderOf_a
  rw [h3, orderOf_one] at h4
  exact absurd h4 (by norm_num)

theorem cp_ne_three (h : F5Std a z) {b t : G} (hb : b ∈ orb2A a a)
    (ht : IsConj z t ∨ (IsConj a t ∧ IsConj z (a * t))) : t ≠ a ∧ t ≠ b ∧ t ≠ a * b := by
  have haa : a * a = 1 := cp_mul_self_eq_one h (Or.inl (IsConj.refl a))
  have hab : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · intro hta
    rcases ht with ht | ht
    · rw [hta] at ht
      exact h.not_isConj ht.symm
    · have h2 := ht.2
      rw [hta, haa] at h2
      have h3 : z = 1 := isConj_one_left.1 h2
      have h4 := h.typ.orderOf_z
      rw [h3, orderOf_one] at h4
      exact absurd h4 (by norm_num)
  · intro htb
    rw [htb] at ht
    rcases ht with ht | ht
    · exact h.not_isConj (hb.1.trans ht.symm)
    · exact h.not_isConj (hb.2.trans ht.2.symm)
  · intro htab
    rw [htab] at ht
    rcases ht with ht | ht
    · exact h.not_isConj (hb.2.trans ht.symm)
    · rw [hab] at ht
      exact h.not_isConj (hb.1.trans ht.2.symm)

theorem cp_not_comm_of_orb3A (h : F5Std a z) {x : G} (hx : x ∈ orb3A a a) : a * x ≠ x * a := by
  intro hcomm
  have ha2 : a ^ 2 = 1 := by simpa [h.typ.orderOf_a] using pow_orderOf_eq_one a
  have hx2 : x ^ 2 = 1 := by
    simpa [h.orderOf_eq_two (Or.inl hx.1)] using pow_orderOf_eq_one x
  have hc : Commute a x := hcomm
  have hsq : (a * x) ^ 2 = 1 := by
    rw [hc.mul_pow, ha2, hx2, one_mul]
  have h3 : orderOf (a * x) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [hx.2.1] at h3
  exact absurd h3 (by norm_num)

theorem cp_3A_not_AB (h : F5Std a z) {x : G} (hx : x ∈ orb3A a a) {t : G}
    (ht : t ∈ InvIn (Gxy a x)) : t ∉ orb2AB a z a := by
  intro htAB
  obtain ⟨i, hi⟩ := (h.loc.s7.self.classes x hx).cover t ht
  fin_cases i
  · have h0 : t ∈ orb2A a a ∩ orb2A a x := hi
    exact h.not_isConj (h0.1.1.trans htAB.1.symm)
  · have h0 : t ∈ orb2B a z a ∩ orb2B a z x := hi
    exact h.not_isConj (h0.1.1.trans htAB.1.symm)
  · have h0 : t ∈ orb2BB a z a ∩ orb2BB a z x := hi
    exact h.not_isConj (htAB.2.trans h0.1.2.symm)

theorem cp_sq_mem_orb2A (h : F5Std a z) {y : G} (hy : y ∈ orb4B a a) :
    (a * y) ^ 2 ∈ orb2A a a :=
  (tableV_orb4B_row h.typ hy).1

theorem cp_mul_central_class {K : Subgroup G} {b : G} (hb : ∀ k ∈ K, k * b * k⁻¹ = b)
    (hb2 : b * b = 1) {P Q : Set G} (hP : IsConjOrbit K P) (hQ : IsConjOrbit K Q)
    (hPQ : ∀ s ∈ P, s * b ∈ Q) : ∀ t ∈ Q, t * b ∈ P := by
  intro t ht
  obtain ⟨s, hs⟩ := hP.nonempty
  obtain ⟨k, hk, hkeq⟩ := hQ.transitive (s * b) (hPQ s hs) t ht
  have e : k * (s * b) * k⁻¹ = (k * s * k⁻¹) * (k * b * k⁻¹) := by group
  rw [hb k hk] at e
  have h1 : t * b = k * s * k⁻¹ := by
    calc t * b = ((k * s * k⁻¹) * b) * b := by rw [← hkeq, e]
      _ = (k * s * k⁻¹) * (b * b) := mul_assoc _ _ _
      _ = k * s * k⁻¹ := by rw [hb2, mul_one]
  rw [h1]
  exact hP.conj_mem k hk s hs

theorem cp_commute_sq_of_mem_Gxy {y k : G} (hk : k ∈ Gxy a y) :
    Commute k ((a * y) ^ 2) := by
  have hx : Commute k a := (mem_Gx.1 (mem_Gxy.1 hk).1).symm
  have hy : Commute k y := (mem_Gx.1 (mem_Gxy.1 hk).2).symm
  exact (hx.mul_right hy).pow_right 2

theorem cp_4B_cases (h : F5Std a z) {y : G} (hy : y ∈ orb4B a a) {t : G}
    (ht : t ∈ InvIn (Gxy a y)) :
    t = (a * y) ^ 2 ∨
      (t ∈ orb2A a a ∧ t ≠ (a * y) ^ 2 ∧ (a * y) ^ 2 * t ∈ orb2AB a z a) ∨
      (t ∈ orb2B a z a ∧ (a * y) ^ 2 * t ∈ orb2BB a z a) ∨
      (t ∈ orb2BB a z a ∧ (a * y) ^ 2 * t ∈ orb2B a z a) ∨
      t ∈ orb2AB a z a ∩ orb2BB a z y := by
  have hfb := h.loc.fourB.self
  have hcl := hfb.classes y hy
  have hbInv : (a * y) ^ 2 ∈ InvIn (Gxy a y) :=
    (cp_central_inv h hy.1 (k := 2) (Or.inl hy.2)).1
  have hb2 : (a * y) ^ 2 * (a * y) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one ((a * y) ^ 2)
    rw [hbInv.2] at h1
    simpa [pow_two] using h1
  have hconj : ∀ k ∈ Gxy a y, k * (a * y) ^ 2 * k⁻¹ = (a * y) ^ 2 := by
    intro k hk
    rw [(cp_commute_sq_of_mem_Gxy hk).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hcomm : (a * y) ^ 2 * t = t * (a * y) ^ 2 :=
    (cp_commute_sq_of_mem_Gxy ht.1).eq.symm
  obtain ⟨i, hi⟩ := hcl.cover t ht
  fin_cases i
  · exact Or.inl hi
  · have h1 : t ∈ orb2B a z a ∩ orb2B a z y := hi
    have h2 := (hfb.case_i y hy t h1).1
    exact Or.inr (Or.inr (Or.inl ⟨h1.1, by rw [hcomm]; exact h2.1⟩))
  · have h1 : t ∈ orb2BB a z a ∩ orb2BB a z y := hi
    have h2 := cp_mul_central_class hconj hb2 (hcl.orbit 1) (hcl.orbit 2)
      (fun s hs => (hfb.case_i y hy s hs).1) t h1
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.1, by rw [hcomm]; exact h2.1⟩)))
  · have h1 : t ∈ orb2A a a ∩ orb2B a z y := hi
    have hne : t ≠ (a * y) ^ 2 := by
      intro htb
      have h0 : t ∈ fourBSet a z y 0 := htb
      exact Set.disjoint_left.1 (hcl.disjoint 0 3 (by decide)) h0 hi
    have h2 := cp_mul_central_class hconj hb2 (hcl.orbit 4) (hcl.orbit 3)
      (fun s hs => (hfb.case_ii y hy s hs).1) t h1
    exact Or.inr (Or.inl ⟨h1.1, hne, by rw [hcomm]; exact h2.1⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
  · have h1 : t ∈ orb2A a y ∩ orb2B a z a := hi
    have h2 := cp_mul_central_class hconj hb2 (hcl.orbit 6) (hcl.orbit 5)
      (fun s hs => (hfb.case_iii y hy s hs).1) t h1
    exact Or.inr (Or.inr (Or.inl ⟨h1.2, by rw [hcomm]; exact h2.2⟩))
  · have h1 : t ∈ orb2AB a z y ∩ orb2BB a z a := hi
    have h2 := (hfb.case_iii y hy t h1).1
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.2, by rw [hcomm]; exact h2.2⟩)))

end CFSG.EvenSporadicStandard.HNRecog.Section4
