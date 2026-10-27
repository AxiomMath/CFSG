module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitTwoGroupShapes
public import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open CFSG.ComponentClassification.AschbacherToolkit

section Shapes

variable {P : Type*} [Group P] [Finite P]

theorem pRank_le_two_of_dihedral_or_semidihedral
    (h : (∃ n : ℕ, 2 ≤ n ∧ Nonempty (P ≃* DihedralGroup (2 ^ (n - 1)))) ∨
      (∃ n : ℕ, 4 ≤ n ∧ Nonempty (P ≃* CFSG.Open.SemidihedralGroup n))) :
    CFSG.pRank 2 P ≤ 2 := by
  rcases h with ⟨n, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
    obtain ⟨ρ, -, hidx, -, -⟩ := exists_inverting_generators_of_dihedral e
    exact CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound
      (H := Subgroup.zpowers ρ) inferInstance hidx.le
  · obtain ⟨ρ, -, hidx, -, -⟩ := exists_inverting_generators_of_semidihedral hn e
    exact CFSG.LocalAnalysis.ComponentInitial.cyclic_index_two_rank_bound
      (H := Subgroup.zpowers ρ) inferInstance hidx.le

theorem pRank_le_two_of_card_le_four (h : Nat.card P ≤ 4) : CFSG.pRank 2 P ≤ 2 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun E _ _ => ?_
  exact (Subgroup.card_le_card_group E).trans (h.trans (by norm_num))

theorem exists_central_involution_of_isPGroup_two [Nontrivial P] (hP : IsPGroup 2 P) :
    ∃ w : P, orderOf w = 2 ∧ ∀ b : P, Commute w b := by
  have hZ : Nontrivial (Subgroup.center P) := hP.center_nontrivial
  have hZp : IsPGroup 2 (Subgroup.center P) := hP.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center P) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  refine ⟨(w : P), ?_, fun b => (Subgroup.mem_center_iff.mp w.property b).symm⟩
  rw [Subgroup.orderOf_coe]
  exact hw

end Shapes

theorem pRank_le_two_of_centralizer_card_four {G : Type} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) {t : G} (htQ : t ∈ Q) (ht : orderOf t = 2)
    (hc : Nat.card ↥(Q ⊓ Subgroup.centralizer ({t} : Set G)) = 4) : CFSG.pRank 2 ↥Q ≤ 2 := by
  set R : Subgroup G := Q ⊓ Subgroup.centralizer ({t} : Set G)
  have htR : t ∈ R := ⟨htQ, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  by_cases hexp : ∀ x ∈ R, x ^ 2 = 1
  ·
    set t' : ↥Q := ⟨t, htQ⟩
    have hmap : (Subgroup.centralizer ({t'} : Set ↥Q)).map Q.subtype = R := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy))⟩
      · rintro ⟨hxQ, hxc⟩
        exact ⟨⟨x, hxQ⟩, Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxc)), rfl⟩
    have hcard : Nat.card ↥(Subgroup.centralizer ({t'} : Set ↥Q)) = 4 := by
      rw [← hc, ← hmap, Subgroup.card_map_of_injective Q.subtype_injective]
    have hexp' : ∀ x ∈ Subgroup.centralizer ({t'} : Set ↥Q), x ^ 2 = 1 := by
      intro x hx
      have hxR : (x : G) ∈ R := hmap ▸ Subgroup.mem_map_of_mem Q.subtype hx
      exact Subtype.ext (hexp x hxR)
    exact pRank_le_two_of_dihedral_or_semidihedral (suzuki_two_group hQ hcard hexp')
  ·
    push Not at hexp
    obtain ⟨g, hgR, hg2⟩ := hexp
    have hRcyc : IsCyclic ↥R := by
      have hdvd : orderOf (⟨g, hgR⟩ : ↥R) ∣ 4 := hc ▸ orderOf_dvd_natCard _
      have hne : ¬ orderOf (⟨g, hgR⟩ : ↥R) ∣ 2 := fun h => hg2 (by
        have := orderOf_dvd_iff_pow_eq_one.mp h
        simpa using congrArg Subtype.val this)
      have h4 : orderOf (⟨g, hgR⟩ : ↥R) = 4 := by
        generalize orderOf (⟨g, hgR⟩ : ↥R) = o at hdvd hne
        have ho : o ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
        interval_cases o <;> omega
      exact isCyclic_of_orderOf_eq_card _ (h4.trans hc.symm)
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
    have : Nontrivial ↥Q := ⟨⟨⟨t, htQ⟩, 1, fun h => ht1 (congrArg Subtype.val h)⟩⟩
    obtain ⟨x, hx2, hxc⟩ := exists_central_involution_of_isPGroup_two hQ
    have hxt : (x : G) * t = t * x := congrArg Subtype.val (hxc ⟨t, htQ⟩).eq
    have hxR : (x : G) ∈ R := ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩
    have hxt' : (x : G) = t := by
      have := atMostOneInvolution_of_isCyclic (P := ↥R) ⟨x, hxR⟩ ⟨t, htR⟩
        (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]; exact hx2)
        (by rw [Subgroup.orderOf_mk]; exact ht)
      exact congrArg Subtype.val this
    have hQR : Q ≤ R := fun b hb => ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h : (x : G) * b = b * x := congrArg Subtype.val (hxc ⟨b, hb⟩).eq
      rw [hxt'] at h
      exact h.symm)⟩
    exact pRank_le_two_of_card_le_four (hc ▸ Subgroup.card_le_of_le hQR)

end CFSG.GH74.GLS.C3.Layer1.PumpRigid
