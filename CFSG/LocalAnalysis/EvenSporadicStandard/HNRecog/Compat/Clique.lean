module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFig20

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}
  {F : Fam a α} {θ : G → G'}

private theorem cp_orderOf_six {b y x : G} (hb2 : orderOf b = 2) (hx2 : orderOf x = 2)
    (hcube : (b * y) ^ 3 = x) (hyb : y ≠ b * x) : orderOf (b * y) = 6 := by
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hx2; omega
  have hxx : x * x = 1 := cp_mul_self_eq_one_of_orderOf_eq_two hx2
  have hbb : b * b = 1 := cp_mul_self_eq_one_of_orderOf_eq_two hb2
  have h6 : (b * y) ^ 6 = 1 := by
    rw [show 6 = 3 * 2 by norm_num, pow_mul, hcube, pow_two, hxx]
  have hmem : orderOf (b * y) ∈ Nat.divisors 6 :=
    Nat.mem_divisors.2 ⟨orderOf_dvd_of_pow_eq_one h6, by norm_num⟩
  have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with o1 | o2 | o3 | o6
  · exfalso
    have e : b * y = 1 := orderOf_eq_one_iff.1 o1
    rw [e, one_pow] at hcube
    exact hx1 hcube.symm
  · exfalso
    have hsq : (b * y) ^ 2 = 1 := by simpa [o2] using pow_orderOf_eq_one (b * y)
    have e : x = b * y := by rw [← hcube, pow_succ, hsq, one_mul]
    apply hyb
    calc y = b * (b * y) := by rw [← mul_assoc, hbb, one_mul]
      _ = b * x := by rw [← e]
  · exfalso
    have e : (b * y) ^ 3 = 1 := by simpa [o3] using pow_orderOf_eq_one (b * y)
    rw [hcube] at e
    exact hx1 e
  · exact o6

theorem cp_clique_3A_6A (hC : Cover4A) (hW : Wit20) (hG : Gen2A) (h : F5Std a z)
    (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x y b : G}
    (hx : x ∈ orb3A a a ∪ orb6A a a) (hb : b ∈ orb2A a a ∩ orb2A a x) (hy : y ∈ orb2A a x) :
    IsClique3 a' (θ x) (θ y) (θ (x * y)) := by
  have hc : a' ≠ 1 := cp_ne_one_of_orderOf_eq_two h'.typ.orderOf_a
  have hxA : IsConj a x := by
    rcases hx with h3 | h6
    exacts [h3.1, h6.1]
  have hbA : IsConj a b := hb.1.1
  have hbx : b ∈ Gx x := h.mem_Gx_of_orb2A hxA hb.2
  have hxb : x * b = b * x := mem_Gx.1 hbx
  have hxbA : IsConj a (b * x) := by rw [← hxb]; exact hb.2.2
  have hxb' : x ∈ orb2A a b := ⟨hxA, hxbA⟩
  have hb2 : orderOf b = 2 := h.orderOf_eq_two (Or.inl hbA)
  have hx2 : orderOf x = 2 := h.orderOf_eq_two (Or.inl hxA)
  have hxx : x * x = 1 := cp_mul_self_eq_one_of_orderOf_eq_two hx2
  have hbline : IsClique3 a' (θ b) (θ x) (θ (b * x)) :=
    IsLine.isClique3 hc
      (theta_line_one h h' hα hθ (Or.inl (Or.inl (Or.inl (Or.inl hb.1)))) hxb')
  by_cases hyb : y = b
  · rw [hyb]
    have e := hbline.swap12
    rwa [← hxb] at e
  by_cases hyb' : y = b * x
  · rw [hyb']
    have hxbx : x * (b * x) = b := by rw [← mul_assoc, hxb, mul_assoc, hxx, mul_one]
    rw [hxbx]
    exact hbline.rotate
  have hyB : y ∈ sBase b x := ⟨hbA.symm.trans hy.1, hbA.symm.trans hy.2, hyb, hyb'⟩
  have hbF : F5Std b z := h.of_isConj hbA (IsConj.refl z)
  have hx2A : x ∈ orb2A b b := ⟨hbA.symm.trans hxA, hbA.symm.trans hxbA⟩
  obtain ⟨i, hi⟩ := (hbF.loc.tableIV.self.partition x hx2A).cover y hyB
  have hyx : IsConj a (y * x) := (cp_isConj_mul_comm a x y).1 hy.2
  have hline : y ∈ orb2A a b ∪ orb2B a z b ∪ orb3A a b ∪ orb4B a b ∪ orb6A a b →
      IsClique3 a' (θ x) (θ y) (θ (x * y)) := fun hyb2 =>
    IsLine.isClique3 hc (theta_line_two h h' hα hθ hx hb hy hyb2)
  fin_cases i
  · have hi2 : IsConj b (b * y) := hi.2
    exact hline (Or.inl (Or.inl (Or.inl (Or.inl ⟨hy.1, hbA.trans hi2⟩))))
  · have hi2 : IsConj z (b * y) := hi.2
    exact hline (Or.inl (Or.inl (Or.inl (Or.inr ⟨hy.1, hi2⟩))))
  · have hi2 : (b * y) ^ 2 = x := hi.2
    exact hline (Or.inl (Or.inr ⟨hy.1, by rw [hi2]; exact hxA⟩))
  · have hi2 : IsConj z ((b * y) ^ 2) := hi.2
    exact theta_clique_two hC hW hG h h' hα hθ hx hb hy ⟨hy.1, hi2⟩
  · have hi2 : orderOf (b * y) = 3 := hi.2
    exact hline (Or.inl (Or.inl (Or.inr ⟨hy.1, hi2, x, hxb', hxA, hyx⟩)))
  · have hi2 : (b * y) ^ 3 = x := hi.2
    exact hline (Or.inr ⟨hy.1, cp_orderOf_six hb2 hx2 hi2 hyb', by rw [hi2]; exact hxA⟩)

theorem theta_clique_of_not_five_E (hC : Cover4A) (hW : Wit20) (hG : Gen2A) (h : F5Std a z)
    (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α) (hθ : IsTheta a F θ) {x y : G}
    (hx : x ∈ orb2A a a ∪ orb2B a z a ∪ orb3A a a ∪ orb4A a z a ∪ orb4B a a ∪ orb5A a a ∪
      orb6A a a)
    (hy : y ∈ orb2A a x) : IsClique3 a' (θ x) (θ y) (θ (x * y)) := by
  have hc : a' ≠ 1 := cp_ne_one_of_orderOf_eq_two h'.typ.orderOf_a
  simp only [Set.mem_union] at hx
  rcases hx with (((((h2A | h2B) | h3A) | h4A) | h4B) | h5A) | h6A
  · exact IsLine.isClique3 hc
      (theta_line_one h h' hα hθ (Or.inl (Or.inl (Or.inl (Or.inl h2A)))) hy)
  · exact IsLine.isClique3 hc
      (theta_line_one h h' hα hθ (Or.inl (Or.inl (Or.inl (Or.inr h2B)))) hy)
  · obtain ⟨b, hb⟩ := h3A.2.2
    exact cp_clique_3A_6A hC hW hG h h' hα hθ (Or.inl h3A) hb hy
  · exact IsLine.isClique3 hc (theta_line_one h h' hα hθ (Or.inl (Or.inl (Or.inr h4A))) hy)
  · exact IsLine.isClique3 hc (theta_line_one h h' hα hθ (Or.inl (Or.inr h4B)) hy)
  · exact IsLine.isClique3 hc (theta_line_one h h' hα hθ (Or.inr h5A) hy)
  · exact cp_clique_3A_6A hC hW hG h h' hα hθ (Or.inr h6A) (cp_orb6A_cube_mem h h6A) hy

theorem theta_adj_self (h : F5Std a z) (h' : F5Std a' z') (hα : IsIsoOn (Gx a) (Gx a') α)
    (hθ : IsTheta a F θ) {y : G} (hy : y ∈ orb2A a a) : θ y ∈ orb2A a' (θ a) := by
  obtain ⟨hyA, hay⟩ := hy
  have hyGa : y ∈ Gx a := h.mem_Gx_of_orb2A (IsConj.refl a) ⟨hyA, hay⟩
  have hy2 : orderOf y = 2 := h.orderOf_eq_two (Or.inl hyA)
  have hψ := F.iso y ⟨hyGa, hy2⟩
  have hyy : y ∈ Gx y := self_mem_Gx y
  have haGy : a ∈ Gx y := mem_Gx.2 (mem_Gx.1 hyGa).symm
  have hayG : a * y ∈ Gx y := (Gx y).mul_mem haGy hyy
  have hyay : y ∈ Gx (a * y) := mem_Gx.2 (mem_Gx.1 hayG).symm
  have h1 : θ y = F.app y y := hθ.eq_app y hyA y ⟨mem_Gxy.2 ⟨hyGa, hyy⟩, hy2⟩
  have h2 : θ a = F.app y a := hθ.eq_app a (IsConj.refl a) y ⟨mem_Gxy.2 ⟨hyGa, hyGa⟩, hy2⟩
  have h3 : θ (a * y) = F.app y (a * y) :=
    hθ.eq_app (a * y) hay y ⟨mem_Gxy.2 ⟨hyGa, hyay⟩, hy2⟩
  have h4 : θ (a * y) = θ a * θ y := by
    rw [h3, h1, h2]
    exact hψ.map_mul a haGy y hyy
  refine ⟨hθ.typed h h' hα hyA, ?_⟩
  rw [← h4]
  exact hθ.typed h h' hα hay

end CFSG.EvenSporadicStandard.HNRecog.Section4
