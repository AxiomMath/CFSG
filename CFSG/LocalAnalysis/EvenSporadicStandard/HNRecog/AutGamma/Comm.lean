module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Inputs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem act_mem_orb2A (hF : IsF5Type a z) (τ : Gamma a ≃g Gamma a) (hτ : act τ a = a) {x : G}
    (hx : x ∈ orb2A a a) : act τ x ∈ orb2A a a := by
  have hne : a ≠ x := by
    rintro rfl
    have h1 : IsConj a (a * a) := hx.2
    rw [mul_self_of_isConj hF (IsConj.refl a)] at h1
    exact ne_one_of_isConj hF h1 rfl
  have h := (adj_act_iff τ (IsConj.refl a) hx.1).2 ⟨hne, hx.2⟩
  rw [hτ] at h
  exact ⟨isConj_act τ hx.1, h.2⟩

theorem sq_mul_eq_one_of_comm (hF : IsF5Type a z) {y : G} (hy : IsConj a y) (hc : a * y = y * a) :
    (a * y) ^ 2 = 1 := by
  have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
  have hyy : y * y = 1 := mul_self_of_isConj hF hy
  calc (a * y) ^ 2 = (a * y) * (a * y) := sq _
    _ = a * (y * a) * y := by group
    _ = a * (a * y) * y := by rw [← hc]
    _ = (a * a) * (y * y) := by group
    _ = 1 := by rw [haa, hyy, one_mul]

theorem not_comm_of_mem_orb3A (hF : IsF5Type a z) {x : G} (hx : x ∈ orb3A a a) :
    a * x ≠ x * a := by
  intro hc
  have h := orderOf_dvd_of_pow_eq_one (sq_mul_eq_one_of_comm hF hx.1 hc)
  rw [hx.2.1] at h
  omega

theorem eq_of_odd_of_comm (hF : IsF5Type a z) {y : G} (hy : IsConj a y) (hc : a * y = y * a)
    (hodd : Odd (orderOf (a * y))) : y = a := by
  have hdvd : orderOf (a * y) ∣ 2 := orderOf_dvd_of_pow_eq_one (sq_mul_eq_one_of_comm hF hy hc)
  have hle : orderOf (a * y) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have h1 : orderOf (a * y) = 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have h2 : a * y = 1 := orderOf_eq_one_iff.mp h1
  rw [eq_inv_of_mul_eq_one_right h2]
  exact inv_eq_of_isConj hF (IsConj.refl a)

theorem comm_act_of_comm (hF : IsF5Type a z) (hL : F5Local G a z) (hlines : LinesThrough a z)
    (τ : Gamma a ≃g Gamma a) (hτ : act τ a = a) {y : G} (hy : IsConj a y)
    (hc : a * y = y * a) : a * act τ y = act τ y * a := by
  have hg : y ∈ gammaSet a z a := hL.gamma.self.eq_gamma a y (IsConj.refl a) hy
  have hsq := sq_mul_eq_one_of_comm hF hy hc
  have hdvd : orderOf (a * y) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hg
  rcases hg with ((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9)
  · rw [h1, hτ]
  · exact comm_of_adj hF (IsConj.refl a) (isConj_act τ hy) (act_mem_orb2A hF τ hτ h2).2
  · obtain ⟨b, hb, hyb⟩ := hlines.two_B y h3
    have hbb : b * b = 1 := mul_self_of_isConj hF hb.1
    have hy' : y * b * b = y := by rw [mul_assoc, hbb, mul_one]
    have hyb2 : IsConj a (y * b * b) := by rw [hy']; exact hy
    have hmul := act_mul_of_adj hF hL.lines.self τ hyb.1 hb.1 hyb2
    rw [hy'] at hmul
    have h1' := comm_of_adj hF (IsConj.refl a) (isConj_act τ hyb.1)
      (act_mem_orb2A hF τ hτ hyb).2
    have h2' := comm_of_adj hF (IsConj.refl a) (isConj_act τ hb.1) (act_mem_orb2A hF τ hτ hb).2
    rw [hmul]
    calc a * (act τ (y * b) * act τ b) = (a * act τ (y * b)) * act τ b := by group
      _ = (act τ (y * b) * a) * act τ b := by rw [h1']
      _ = act τ (y * b) * (a * act τ b) := by group
      _ = act τ (y * b) * (act τ b * a) := by rw [h2']
      _ = (act τ (y * b) * act τ b) * a := by group
  · rw [h4.2.1] at hdvd
    omega
  · have h : IsConj z 1 := by rw [← hsq]; exact h5.2
    have hz : z = 1 := isConj_one_left.1 h
    have := hF.orderOf_z
    rw [hz, orderOf_one] at this
    omega
  · have h : IsConj a 1 := by rw [← hsq]; exact h6.2
    exact absurd (isConj_one_left.1 h) (ne_one_of_isConj hF (IsConj.refl a))
  · exact absurd (eq_of_odd_of_comm hF hy hc h7.1.2.2.1) h7.1.2.1
  · exact absurd (eq_of_odd_of_comm hF hy hc h8.1.2.2.1) h8.1.2.1
  · rw [h9.2.1] at hdvd
    omega

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
