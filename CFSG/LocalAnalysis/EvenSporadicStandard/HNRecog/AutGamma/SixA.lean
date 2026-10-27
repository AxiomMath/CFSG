module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

section Dihedral

variable {a x : G}

private lemma help_inv (ha : a * a = 1) (hx : x * x = 1) :
    (a * x)⁻¹ = x * a := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right ha]

private lemma help_ar (ha : a * a = 1) : a * (a * x) = x := by
  rw [← mul_assoc a a x, ha, one_mul]

private lemma help_rx (hx : x * x = 1) : (a * x) * x = a := by
  rw [mul_assoc, hx, mul_one]

private lemma help_ar_shift (ha : a * a = 1) (hx : x * x = 1) :
    a * (a * x) = (a * x)⁻¹ * a := by
  rw [help_inv ha hx, help_ar ha]
  rw [mul_assoc, ha, mul_one]

private lemma help_ra (ha : a * a = 1) (hx : x * x = 1) :
    (a * x) * a = a * (a * x)⁻¹ := by
  calc (a * x) * a = (a * x) * (a * (a * x)) * (a * x)⁻¹ := by group
    _ = (a * x) * ((a * x)⁻¹ * a) * (a * x)⁻¹ := by rw [help_ar_shift ha hx]
    _ = a * (a * x)⁻¹ := by group

private lemma help_reflect (ha : a * a = 1) (hx : x * x = 1) :
    a * (a * x)⁻¹ * (a * x)⁻¹ = (a * x) ^ 2 * a := by
  rw [help_inv ha hx, pow_two]
  group

private lemma help_ar_pow (ha : a * a = 1) (hx : x * x = 1) (n : ℕ) :
    a * (a * x) ^ n = ((a * x) ^ n)⁻¹ * a := by
  induction n with
  | zero => simp
  | succ n ih =>
      conv_lhs => rw [pow_succ, ← mul_assoc, ih, mul_assoc]
      rw [help_ar_shift ha hx, ← mul_assoc, ← mul_inv_rev, ← pow_succ']

private lemma help_c (hx : x * x = 1) : (a * x) ^ 3 * x = (a * x) ^ 2 * a := by
  conv_lhs => rw [pow_succ]
  rw [mul_assoc, help_rx hx]

private lemma help_lhs1 (ha : a * a = 1) (hx : x * x = 1) :
    (a * x)⁻¹ * x * (a * x) = a * (a * x) ^ 3 := by
  have h1 : (a * x)⁻¹ * x * (a * x) = x * (a * x) ^ 2 := by
    rw [help_inv ha hx, pow_two]
    group
  have h2 : a * (a * x) ^ 3 = x * (a * x) ^ 2 := by
    conv_lhs => rw [pow_succ', ← mul_assoc, help_ar ha]
  exact h1.trans h2.symm

end Dihedral

theorem sixA_pow_mem_orb2A (hF : IsF5Type a z) {x : G} (hx : x ∈ orb6A a a) :
    (a * x) ^ 3 ∈ orb2A a a := by
  have hx' : IsConj a x ∧ orderOf (a * x) = 6 ∧ IsConj a ((a * x) ^ 3) := hx
  have ha : a * a = 1 := by rw [← sq, ← hF.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : x * x = 1 := mul_self_of_isConj hF hx'.1
  have hconj : IsConj a (a * (a * x) ^ 3) := by
    have h := CFSG.Monster.GMS.isConj_conj hx'.1 (a * x)⁻¹
    simpa only [inv_inv, help_lhs1 ha hx2] using h
  exact ⟨hx'.2.2, hconj⟩

theorem sixA_mul_mem_orb3A (hF : IsF5Type a z) (hL : F5Local G a z) {x : G}
    (hx : x ∈ orb6A a a) : (a * x) ^ 3 * x ∈ orb3A a a := by
  have hx' : IsConj a x ∧ orderOf (a * x) = 6 ∧ IsConj a ((a * x) ^ 3) := hx
  have ha : a * a = 1 := by rw [← sq, ← hF.orderOf_a]; exact pow_orderOf_eq_one a
  have hx2 : x * x = 1 := mul_self_of_isConj hF hx'.1
  have hord : orderOf ((a * x) ^ 4) = 3 := by
    rw [orderOf_pow' (x := a * x) (n := 4) (by norm_num), hx'.2.1]
    norm_num
  have hr6 : (a * x) ^ 6 = 1 := by rw [← hx'.2.1]; exact pow_orderOf_eq_one (a * x)
  have hcube : (a * x) ^ 3 * (a * x) ^ 3 = 1 := by
    have h33 : (3 : ℕ) + 3 = 6 := by norm_num
    rw [← pow_add, h33, hr6]
  have hinv3 : ((a * x) ^ 3)⁻¹ = (a * x) ^ 3 := inv_eq_of_mul_eq_one_right hcube
  have hcent : a * (a * x) ^ 3 = (a * x) ^ 3 * a := by
    rw [help_ar_pow ha hx2 3, hinv3]
  have hac4 : a * ((a * x) ^ 3 * x) = (a * x) ^ 4 := by
    rw [← mul_assoc, hcent]
    rw [mul_assoc ((a * x) ^ 3) a x, ← pow_succ]
  have h2b : orderOf (a * ((a * x) ^ 3 * x)) = 3 := by rw [hac4, hord]
  have hconj_c : IsConj a ((a * x) ^ 3 * x) := by
    refine isConj_iff.2 ⟨a * x, ?_⟩
    rw [help_ra ha hx2, help_c hx2]
    exact help_reflect ha hx2
  obtain ⟨t, ht3⟩ := (hL.sixA.self.classes x hx).orbit 3 |>.nonempty
  have ht3' := ht3
  simp only [sixASet] at ht3'
  have htA : t ∈ orb2A a a := ht3'.1
  have htAt : IsConj a t ∧ IsConj a (a * t) := htA
  have htGxy : t ∈ Gxy a x := ((hL.sixA.self.classes x hx).subset 3 ht3).1
  have hta : a * t = t * a := mem_Gx.1 (mem_Gxy.1 htGxy).1
  have htx : x * t = t * x := mem_Gx.1 (mem_Gxy.1 htGxy).2
  have hrt : Commute (a * x) t := by
    rw [commute_iff_eq]
    calc (a * x) * t = a * (x * t) := by group
      _ = a * (t * x) := by rw [htx]
      _ = (a * t) * x := by group
      _ = (t * a) * x := by rw [hta]
      _ = t * (a * x) := by group
  have hbt : (a * x) ^ 3 * t = t * (a * x) ^ 3 := (hrt.pow_left 3).eq
  have hbx : (a * x) ^ 3 * x = x * (a * x) ^ 3 := by
    have hxar : x = a * (a * x) := (help_ar (x := x) ha).symm
    have hcomm_a : Commute a ((a * x) ^ 3) := by
      rw [commute_iff_eq]; exact hcent
    have hcomm_r : Commute (a * x) ((a * x) ^ 3) := (Commute.refl (a * x)).pow_right 3
    have h' : Commute (a * (a * x)) ((a * x) ^ 3) := hcomm_a.mul_left hcomm_r
    have hbxl : (a * x) ^ 3 * x = (a * x) ^ 3 * (a * (a * x)) :=
      congrArg (fun y => (a * x) ^ 3 * y) hxar
    have hbxr : x * (a * x) ^ 3 = (a * (a * x)) * (a * x) ^ 3 :=
      congrArg (fun y => y * (a * x) ^ 3) hxar
    calc (a * x) ^ 3 * x = (a * x) ^ 3 * (a * (a * x)) := hbxl
      _ = (a * (a * x)) * (a * x) ^ 3 := h'.eq.symm
      _ = x * (a * x) ^ 3 := hbxr.symm
  have heq : ((a * x) ^ 3 * x) * t = x * (t * (a * x) ^ 3) := by
    calc ((a * x) ^ 3 * x) * t = (a * x) ^ 3 * (x * t) := by group
      _ = (a * x) ^ 3 * (t * x) := by rw [htx]
      _ = ((a * x) ^ 3 * t) * x := by group
      _ = (t * (a * x) ^ 3) * x := by rw [hbt]
      _ = t * ((a * x) ^ 3 * x) := by group
      _ = t * (x * (a * x) ^ 3) := by rw [hbx]
      _ = (t * x) * (a * x) ^ 3 := by group
      _ = (x * t) * (a * x) ^ 3 := by rw [← htx]
      _ = x * (t * (a * x) ^ 3) := by group
  have hcase := (hL.sixA.self.case_ii x hx) t ht3
  have htborb2A : t * (a * x) ^ 3 ∈ orb2A a x := hcase.1.2
  have hcase_conj : IsConj a (x * (t * (a * x) ^ 3)) := by
    have htmp : IsConj a (t * (a * x) ^ 3) ∧ IsConj a (x * (t * (a * x) ^ 3)) := htborb2A
    exact htmp.2
  have hconjc_t : IsConj a (((a * x) ^ 3 * x) * t) := by
    rw [heq]
    exact hcase_conj
  change IsConj a ((a * x) ^ 3 * x) ∧ orderOf (a * ((a * x) ^ 3 * x)) = 3 ∧
    (orb2A a a ∩ orb2A a ((a * x) ^ 3 * x)).Nonempty
  refine ⟨hconj_c, h2b, ?_⟩
  exact ⟨t, ⟨htA, ⟨htAt.1, hconjc_t⟩⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
