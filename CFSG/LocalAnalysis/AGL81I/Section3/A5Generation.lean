module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

theorem a5_eq_top_of_order_three_and_five {H : Subgroup (alternatingGroup (Fin 5))}
    (h3 : ∃ x ∈ H, orderOf x = 3) (h5 : ∃ y ∈ H, orderOf y = 5) : H = ⊤ := by
  classical
  let G := alternatingGroup (Fin 5)
  have hGcard : Nat.card G = 60 := by
    dsimp [G]
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  haveI hsimple : IsSimpleGroup G := by
    dsimp [G]
    exact alternatingGroup.isSimpleGroup (by norm_num)
  have hdvd : Nat.card H ∣ 60 := by
    rw [← hGcard]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨x, hxH, hxord⟩ := h3
  obtain ⟨y, hyH, hyord⟩ := h5
  have h3dvd : 3 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H hxH
    rwa [hxord] at h
  have h5dvd : 5 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H hyH
    rwa [hyord] at h
  have h15dvd : 15 ∣ Nat.card H := by
    have hcop : Nat.Coprime 3 5 := by norm_num
    have := hcop.mul_dvd_of_dvd_of_dvd h3dvd h5dvd
    simpa using this
  have hnot15 : Nat.card H ≠ 15 := by
    intro hcard
    have hindex : H.index = 4 := by
      have h := H.index_mul_card
      rw [hcard, hGcard] at h
      omega
    have hcore_dvd : H.normalCore.index ∣ 24 := by
      have h := H.index_normalCore_dvd_factorial_index
      rw [hindex] at h
      have hfac : Nat.factorial 4 = 24 := by decide
      rwa [hfac] at h
    rcases hsimple.eq_bot_or_eq_top_of_normal H.normalCore with hbot | htop
    · have hcore_index : H.normalCore.index = 60 := by
        rw [hbot, Subgroup.index_bot, hGcard]
      rw [hcore_index] at hcore_dvd
      norm_num at hcore_dvd
    · have hle : H.normalCore ≤ H := Subgroup.normalCore_le H
      rw [htop] at hle
      have htopH : H = ⊤ := top_le_iff.mp hle
      rw [htopH, Subgroup.card_top, hGcard] at hcard
      norm_num at hcard
  have hnot30 : Nat.card H ≠ 30 := by
    intro hcard
    have hindex : H.index = 2 := by
      have h := H.index_mul_card
      rw [hcard, hGcard] at h
      omega
    haveI : H.Normal := Subgroup.normal_of_index_eq_two hindex
    rcases hsimple.eq_bot_or_eq_top_of_normal H with hbot | htop
    · rw [hbot, Subgroup.card_bot] at hcard
      norm_num at hcard
    · rw [htop, Subgroup.card_top, hGcard] at hcard
      norm_num at hcard
  have hcard_cases : Nat.card H = 15 ∨ Nat.card H = 30 ∨ Nat.card H = 60 := by
    obtain ⟨k, hk⟩ := h15dvd
    have hk4 : k ∣ 4 := by
      have h : 15 * k ∣ 60 := by
        rw [hk] at hdvd
        exact hdvd
      have h60 : (60 : ℕ) = 15 * 4 := by norm_num
      rw [h60] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have hk_cases : k = 1 ∨ k = 2 ∨ k = 4 := by
      have hkpos : 0 < k := Nat.pos_of_dvd_of_pos hk4 (by norm_num)
      have hkle : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk4
      interval_cases k <;> simp_all
    rcases hk_cases with rfl | rfl | rfl
    · left; simpa using hk
    · right; left; simpa using hk
    · right; right; simpa using hk
  rcases hcard_cases with h15 | h30 | h60
  · exact absurd h15 hnot15
  · exact absurd h30 hnot30
  · exact Subgroup.eq_top_of_card_eq H (by rw [h60, hGcard])

theorem eq_top_of_order_three_and_five_of_mulEquiv {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) {H : Subgroup X}
    (h3 : ∃ x ∈ H, orderOf x = 3) (h5 : ∃ y ∈ H, orderOf y = 5) : H = ⊤ := by
  have h3' : ∃ x ∈ H.map e.toMonoidHom, orderOf x = 3 := by
    obtain ⟨x, hxH, hxord⟩ := h3
    exact ⟨e x, Subgroup.mem_map_of_mem e.toMonoidHom hxH, by simpa using hxord⟩
  have h5' : ∃ y ∈ H.map e.toMonoidHom, orderOf y = 5 := by
    obtain ⟨y, hyH, hyord⟩ := h5
    exact ⟨e y, Subgroup.mem_map_of_mem e.toMonoidHom hyH, by simpa using hyord⟩
  have htop : H.map e.toMonoidHom = ⊤ := a5_eq_top_of_order_three_and_five h3' h5'
  have hcomap : (H.map e.toMonoidHom).comap e.toMonoidHom = H :=
    Subgroup.comap_map_eq_self_of_injective e.injective H
  rw [htop, Subgroup.comap_top] at hcomap
  exact hcomap.symm

end CFSG.LocalAnalysis.AGL81I.Section3
