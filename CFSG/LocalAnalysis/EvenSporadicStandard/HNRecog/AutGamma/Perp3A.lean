module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Gen7
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Perp3AKinds
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutGamma.Perp3A3A

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

private theorem eq_a_of_mem_zpowers_of_isConj [Finite G] (hF : IsF5Type a z) {y : G}
    (hy : IsConj a y) (hz : y ∈ Subgroup.zpowers a) : y = a := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hmod := zpow_mod_orderOf a k
  have hord : (orderOf a : ℤ) = 2 := by rw [hF.orderOf_a]; norm_num
  rw [hord, hk] at hmod
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hmod
    exact absurd hmod.symm (ne_one_of_isConj hF hy)
  · rw [h, zpow_one] at hmod
    exact hmod.symm

theorem perpThreeA_of_f5Local [Finite G] (hF : IsF5Type a z) (hL : F5Local G a z)
    (hnc : ¬ IsConj a z) : PerpThreeA a := by
  intro x hx y hy
  have hle : Subgroup.closure (orb2A a a ∩ orb2A a x) ≤ Gx y := by
    rw [Subgroup.closure_le]
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      rcases hy.2 p hp with h | ⟨-, hpy⟩
      · simp [h]
      · exact comm_of_adj hF hp.1.1 hy.1 hpy)
  have hc : ∀ s ∈ Gxy a x, y * s = s * y := by
    intro s hs
    have hs' : s ∈ Subgroup.closure (orb2A a a ∩ orb2A a x) := by
      rw [closure_orb2A_inter_eq hF hL hx]
      exact hs
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hs')).symm
  have hyg : y ∈ gammaSet a z a := hL.gamma.self.eq_gamma a y (IsConj.refl a) hy.1
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff] at hyg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hyg with ((((((((h1 | h2) | h3) | h4) | h5) | h6) | h7) | h8) | h9)
  · exact Or.inl h1
  ·
    have hya : y ∈ Gx a := mem_Gx.mpr (comm_of_adj hF (IsConj.refl a) hy.1 h2.2)
    have hSa : Gxy a x ≤ Gx a := fun s hs => (mem_Gxy.mp hs).1
    have hyz : y ∈ Subgroup.zpowers a :=
      mem_zpowers_of_centralizes_sym7_of_f5Local hL (S := Gxy a x) hSa
        (hL.s7.self.shape x hx) hya hc
    exact Or.inl (eq_a_of_mem_zpowers_of_isConj hF hy.1 hyz)
  ·
    have hzz : z * z = 1 := by rw [← sq, ← hF.orderOf_z]; exact pow_orderOf_eq_one z
    have hsq : (a * y) * (a * y) = 1 := by
      have hpow := h3.2.pow 2
      rw [pow_two, hzz, isConj_one_right, pow_two] at hpow
      exact hpow
    have haa : a * a = 1 := mul_self_of_isConj hF (IsConj.refl a)
    have hyy : y * y = 1 := mul_self_of_isConj hF hy.1
    have h2comm : (a * y) * (y * a) = 1 := by
      calc (a * y) * (y * a) = a * (y * y) * a := by group
        _ = a * a := by rw [hyy]; group
        _ = 1 := haa
    have hcomm : a * y = y * a := mul_left_cancel (by rw [hsq, h2comm])
    have hya : y ∈ Gx a := mem_Gx.mpr hcomm
    have hSa : Gxy a x ≤ Gx a := fun s hs => (mem_Gxy.mp hs).1
    have hyz : y ∈ Subgroup.zpowers a :=
      mem_zpowers_of_centralizes_sym7_of_f5Local hL (S := Gxy a x) hSa
        (hL.s7.self.shape x hx) hya hc
    exact Or.inl (eq_a_of_mem_zpowers_of_isConj hF hy.1 hyz)
  ·
    rcases eq_or_eq_conj_of_centralizes hF hL hx h4 hc with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  ·
    exfalso
    exact (not_centralizes_of_mem_kinds hF hL hnc hx
      (Or.inl (Or.inl (Or.inl (Or.inl h5))))) hc
  ·
    exfalso
    exact (not_centralizes_of_mem_kinds hF hL hnc hx
      (Or.inl (Or.inl (Or.inl (Or.inr h6))))) hc
  ·
    exfalso
    exact (not_centralizes_of_mem_kinds hF hL hnc hx
      (Or.inl (Or.inr h7))) hc
  ·
    exfalso
    exact (not_centralizes_of_mem_kinds hF hL hnc hx (Or.inr h8)) hc
  ·
    exfalso
    exact (not_centralizes_of_mem_kinds hF hL hnc hx
      (Or.inl (Or.inl (Or.inr h9)))) hc

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
