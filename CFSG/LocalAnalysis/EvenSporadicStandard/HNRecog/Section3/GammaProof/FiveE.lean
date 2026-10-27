module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.Common

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

private theorem fiveE_orderOf_mul_two {u t : G} (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hcomm : u * t = t * u) (hne : u * t ≠ 1) : orderOf (u * t) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ hne
  have hu2 : u ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hu]
  have ht2 : t ^ 2 = 1 := by rw [← pow_orderOf_eq_one, ht]
  calc (u * t) ^ 2 = u ^ 2 * t ^ 2 := (show Commute u t from hcomm).mul_pow 2
    _ = 1 := by rw [hu2, ht2, one_mul]

private theorem fiveE_tab5Set_subset (i : Fin 5) :
    tab5Set a z i ⊆
      orb2A a a ∪ orb2B a z a ∪ orb4A a z a ∪ orb4B a a ∪ orb6A a a := by
  fin_cases i
  · intro x hx
    exact Or.inl (Or.inl (Or.inl (Or.inl hx)))
  · intro x hx
    exact Or.inl (Or.inl (Or.inl (Or.inr hx)))
  · intro x hx
    exact Or.inl (Or.inl (Or.inr hx))
  · intro x hx
    exact Or.inl (Or.inr hx)
  · intro x hx
    exact Or.inr hx

theorem gamma_five_E (H : GammaHyps a z) {y t : G} (hy : y ∈ orb5E a a) (ht : t ∈ orb2A a y) :
    ∃ y₁ ∈ orb2A a a ∪ orb2B a z a ∪ orb4A a z a ∪ orb4B a a ∪ orb6A a a,
      t ∈ orb2A a y₁ := by
  have hyodd : y ∈ oddSet a a := hy.1
  have hyord : orderOf (a * y) = 5 := hy.2.1
  have hyA : IsConj a y := hyodd.1
  have hya : y ≠ a := hyodd.2.1
  obtain ⟨t₀, ht₀A, ht₀G⟩ := hyodd.2.2.2
  have ht₀ord : orderOf t₀ = 2 := H.orderOf_a ht₀A
  have ht₀Ga : t₀ ∈ Gx a := (mem_Gxy.mp ht₀G).1
  have ht₀Gy : t₀ ∈ Gx y := (mem_Gxy.mp ht₀G).2
  have hcomm_a : a * t₀ = t₀ * a := mem_Gx.mp ht₀Ga
  have hcomm_y : y * t₀ = t₀ * y := mem_Gx.mp ht₀Gy
  have ha2 : a ^ 2 = 1 := H.sq_a (IsConj.refl a)
  have hy2 : y ^ 2 = 1 := H.sq_a hyA
  have haa : a * a = 1 := by simpa [pow_two] using ha2
  have hyy : y * y = 1 := by simpa [pow_two] using hy2
  have ht₀_ne_a : t₀ ≠ a := by
    intro h
    have hay : a * y = y * a := by
      have h' := mem_Gx.mp ht₀Gy
      rw [h] at h'
      exact h'.symm
    have hsq : (a * y) ^ 2 = 1 := by
      calc (a * y) ^ 2 = a ^ 2 * y ^ 2 := (show Commute a y from hay).mul_pow 2
        _ = 1 := by rw [ha2, hy2, one_mul]
    have hdvd : orderOf (a * y) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    rw [hyord] at hdvd
    norm_num at hdvd
  have ht₀_ne_y : t₀ ≠ y := by
    intro h
    have hay : a * y = y * a := by
      have h' := mem_Gx.mp ht₀Ga
      rw [h] at h'
      exact h'
    have hsq : (a * y) ^ 2 = 1 := by
      calc (a * y) ^ 2 = a ^ 2 * y ^ 2 := (show Commute a y from hay).mul_pow 2
        _ = 1 := by rw [ha2, hy2, one_mul]
    have hdvd : orderOf (a * y) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    rw [hyord] at hdvd
    norm_num at hdvd
  have ha_t₀_ne_one : a * t₀ ≠ 1 := by
    intro h
    refine ht₀_ne_a ?_
    have h' := congrArg (fun w => a * w) h
    simp only [mul_one] at h'
    rwa [← mul_assoc, haa, one_mul] at h'
  have hy_t₀_ne_one : y * t₀ ≠ 1 := by
    intro h
    refine ht₀_ne_y ?_
    have h' := congrArg (fun w => y * w) h
    simp only [mul_one] at h'
    rwa [← mul_assoc, hyy, one_mul] at h'
  have ha_t₀_ord : orderOf (a * t₀) = 2 :=
    fiveE_orderOf_mul_two (H.orderOf_a (IsConj.refl a)) ht₀ord hcomm_a ha_t₀_ne_one
  have hy_t₀_ord : orderOf (y * t₀) = 2 :=
    fiveE_orderOf_mul_two (H.orderOf_a hyA) ht₀ord hcomm_y hy_t₀_ne_one
  have hconj1 : IsConj (a * t₀) (y * t₀) := by
    by_contra hnc
    have hev := (H.hPar.self).even_of_not_conj y t₀ hyA ht₀ord ht₀G hnc
    rw [hyord] at hev
    obtain ⟨k, hk⟩ := hev
    omega
  have hb2B : IsConj z (a * t₀) := by
    rcases (H.hCls.self).inv_two (a * t₀) ha_t₀_ord with hA | hZ
    · exfalso
      have ht₀_mem : t₀ ∈ orb2A a a := ⟨ht₀A, hA⟩
      have haty : IsConj a (t₀ * y) := by
        have h : IsConj a (y * t₀) := hA.trans hconj1
        rwa [hcomm_y] at h
      have hyat : y ≠ a * t₀ := by
        intro h
        have h2 : orderOf (a * y) = 2 := by
          rw [h]
          rw [show a * (a * t₀) = t₀ from by rw [← mul_assoc, haa, one_mul], ht₀ord]
        rw [hyord] at h2
        norm_num at h2
      have hyS : y ∈ sBase a t₀ := ⟨hyA, haty, hya, hyat⟩
      obtain ⟨i, hi⟩ := ((H.hT4.self).partition t₀ ht₀_mem).cover y hyS
      fin_cases i
      · have hc : y ∈ sBase a t₀ ∧ IsConj a (a * y) := hi
        have h2 : orderOf (a * y) = 2 := H.orderOf_a hc.2
        rw [hyord] at h2
        norm_num at h2
      · have hc : y ∈ sBase a t₀ ∧ IsConj z (a * y) := hi
        have h2 : orderOf (a * y) = 2 := H.orderOf_z hc.2
        rw [hyord] at h2
        norm_num at h2
      · obtain ⟨h2, -⟩ := perp_orderOf_row_two H.h ht₀A hi
        rw [hyord] at h2
        norm_num at h2
      · obtain ⟨h2, -⟩ := perp_orderOf_row_three H.h hi
        rw [hyord] at h2
        norm_num at h2
      · have h2 : orderOf (a * y) = 3 := perp_orderOf_row_four hi
        rw [hyord] at h2
        norm_num at h2
      · obtain ⟨h2, -⟩ := perp_orderOf_row_five H.h ht₀A hi
        rw [hyord] at h2
        norm_num at h2
    · exact hZ
  have hcomm_yt : y * t = t * y := H.comm_of_orb2A hyA ht
  have hb_y_B : IsConj z (t₀ * y) := by
    have h : IsConj z (y * t₀) := hb2B.trans hconj1
    rwa [hcomm_y] at h
  have hty_A : IsConj a (t * y) := by
    have h : IsConj a (y * t) := ht.2
    rwa [hcomm_yt] at h
  have hnc3 : ¬ IsConj (t₀ * y) (t * y) := by
    intro hc
    exact H.not_isConj_both hty_A (hb_y_B.trans hc)
  have heven : Even (orderOf (t₀ * t)) :=
    (H.hPar t₀ z ht₀A (IsConj.refl z)).even_of_not_conj t y
      ((gamma_isConj_iff ht₀A t).mpr ht.1) (H.orderOf_a hyA)
      (mem_Gxy.mpr ⟨mem_Gx.mpr hcomm_y.symm, mem_Gx.mpr hcomm_yt.symm⟩) hnc3
  obtain ⟨y₁, hy₁b, hy₁t⟩ := gamma_common H ht₀A ht.1 heven
  have hy₁A : IsConj a y₁ := hy₁b.1
  have hcomm_t₀y₁ : t₀ * y₁ = y₁ * t₀ := H.comm_of_orb2A ht₀A hy₁b
  have ha_t₀_y₁ : ¬ IsConj (a * t₀) (y₁ * t₀) := by
    intro hc
    have hy₁t₀_A : IsConj a (y₁ * t₀) := by
      have h : IsConj a (t₀ * y₁) := hy₁b.2
      rwa [hcomm_t₀y₁] at h
    exact H.not_isConj_both hy₁t₀_A (hb2B.trans hc)
  have heven_a : Even (orderOf (a * y₁)) :=
    (H.hPar.self).even_of_not_conj y₁ t₀ hy₁A (H.orderOf_a ht₀A)
      (mem_Gxy.mpr ⟨mem_Gx.mpr hcomm_a, mem_Gx.mpr hcomm_t₀y₁.symm⟩) ha_t₀_y₁
  obtain ⟨i, hi⟩ := (H.hT5.self).partition.cover y₁ ⟨hy₁A, heven_a⟩
  exact ⟨y₁, fiveE_tab5Set_subset i hi, H.orb2A_symm ht.1 hy₁t⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
