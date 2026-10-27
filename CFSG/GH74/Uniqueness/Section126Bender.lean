module

public import CFSG.GH74.Uniqueness.Section12Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M F : Subgroup X} {n i e : ℕ}

theorem BenderSub.exists_not_commute
    (hF : BenderSub Z M F n i e) {y : X} (hyF : y ∈ F)
    (hyM : y ∈ M) (hy2 : orderOf y = 2) : ∃ g ∈ F ⊓ M, g⁻¹ * y * g ≠ y := by
  obtain ⟨T, hT⟩ := hF.borel
  set π := QuotientGroup.mk' (center ↥F) with hπ
  set yq : ↥F := ⟨y, hyF⟩ with hyqdef
  have hyqB : yq ∈ (M ⊓ F).subgroupOf F := Subgroup.mem_subgroupOf.mpr ⟨hyM, hyF⟩
  have hybB : π yq ∈ normalizer ((T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) := by
    rw [← hT]
    exact Subgroup.mem_map_of_mem _ hyqB
  have hyq2 : orderOf yq = 2 := by rw [hyqdef, Subgroup.orderOf_mk]; exact hy2
  have hyb1 : π yq ≠ 1 := by
    intro h1
    have hc : yq ∈ center ↥F := (QuotientGroup.eq_one_iff yq).mp h1
    have hyP : y ∈ pPrimeCoreIn F := by
      rw [hF.core]
      exact ⟨yq, hc, rfl⟩
    have hdvd : orderOf (⟨y, hyP⟩ : pPrimeCoreIn F) ∣ Nat.card (pPrimeCoreIn F) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hy2] at hdvd
    exact (odd_card_pPrimeCoreIn F).not_two_dvd_nat hdvd
  have hyb2 : orderOf (π yq) = 2 := by
    refine orderOf_eq_prime ?_ hyb1
    rw [← map_pow, ← hyq2, pow_orderOf_eq_one, map_one]
  obtain ⟨t', hc⟩ := hF.bender.exists_benderCore T
  obtain ⟨hrcy, hrc1⟩ := hc.involution_iff.mp ⟨hybB, hyb2⟩
  have hcard : Nat.card ↥(Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F))) = 2 ^ n :=
    hc.card_center
  have hn2 : 2 ≤ n := hF.bender.two_le.2
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨z', hz'R, hz'1, hz'ne⟩ : ∃ z' ∈ Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)),
      z' ≠ 1 ∧ z' ≠ π yq := by
    by_contra hcon
    push Not at hcon
    have hsub : (Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F)) ⊆
        {1, π yq} := by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · exact Or.inr (hcon x hx hx1)
    have h2 : Set.ncard (Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) :
        Set (↥F ⧸ center ↥F)) ≤ 2 := by
      calc Set.ncard (Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F)) : Set (↥F ⧸ center ↥F))
          ≤ Set.ncard ({1, π yq} : Set (↥F ⧸ center ↥F)) :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ Set.ncard ({π yq} : Set (↥F ⧸ center ↥F)) + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    rw [← Nat.card_coe_set_eq] at h2
    have h3 : Nat.card ↥(Bender.rootCenter (T : Subgroup (↥F ⧸ center ↥F))) ≤ 2 := h2
    omega
  obtain ⟨d, hd, hdz⟩ := hc.exists_cartan_conj hrcy hrc1 hz'R hz'1
  have hdB : d ∈ ((M ⊓ F).subgroupOf F).map π := by
    rw [hT]
    exact Bender.cartan_le_borel _ _ hd
  obtain ⟨gq, hgq, hgqd⟩ := hdB
  have hgq' : (gq : X) ∈ M ⊓ F := Subgroup.mem_subgroupOf.mp hgq
  refine ⟨(gq : X), by rw [inf_comm]; exact hgq', fun heq => hz'ne ?_⟩
  have hconj : gq⁻¹ * yq * gq = yq := Subtype.ext heq
  rw [hdz, ← hgqd]
  calc (π gq)⁻¹ * π yq * π gq = π (gq⁻¹ * yq * gq) := by simp
    _ = π yq := by rw [hconj]

end CFSG.GH74.Uniqueness
