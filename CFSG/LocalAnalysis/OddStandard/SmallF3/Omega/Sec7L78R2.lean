module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L78Side

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma sec7l78_eq_one_or_eq_of_mem_zpowers_of_sq_eq_one {s u : G} (hs : s * s = 1)
    (hu : u ∈ zpowers s) : u = 1 ∨ u = s := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two, hs]
  have hku : u = s ^ (k % 2) := by
    rw [← hk]
    exact zpow_eq_zpow_emod k h2
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left; rw [hku, hk0]; simp
  · right; rw [hku, hk1]; simp

theorem sec7l78_exists_r2 [Finite G] (hP : Asc82Tab6P) {L L' P P' B D A : Subgroup G} {t s : G}
    (hsL : Sec7L78Side L P B A t) (hsL' : Sec7L78Side L' P' D A s) (hne : A ≠ zpowers t ⊔ B) :
    ∃ r₂ ∈ A, r₂ ∉ zpowers s ∧ ∀ n ∈ L' ⊓ normalizer (D : Set G), r₂ * n = n * r₂ := by
  by_contra hcon
  have hsub : ∀ u ∈ A, (∀ n ∈ L' ⊓ normalizer (D : Set G), u * n = n * u) →
      u ∈ zpowers s := by
    intro u hu huc
    by_contra hus
    exact hcon ⟨u, hu, hus, huc⟩
  have hD_le_A : D ≤ A := (le_of_eq hsL'.inf_eq.symm).trans inf_le_left
  have hDcard : Nat.card D = 2 ^ 4 := hsL'.norm.2.1.2
  let f : ↥D ⊕ ↥D → ↥A := fun p =>
    match p with
    | Sum.inl d => ⟨(d : G), hD_le_A d.2⟩
    | Sum.inr d => ⟨s * (d : G), mul_mem hsL'.c_mem (hD_le_A d.2)⟩
  have hf_surj : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨u, huA, huc, b, hbD, rfl⟩ := Sec7L78Side.decomp hP hsL' a ha
    rcases sec7l78_eq_one_or_eq_of_mem_zpowers_of_sq_eq_one
      (hsL'.A_sq s hsL'.c_mem) (hsub u huA huc) with hu1 | hus
    · refine ⟨Sum.inl ⟨b, hbD⟩, Subtype.ext ?_⟩
      dsimp [f]
      rw [hu1, one_mul]
    · refine ⟨Sum.inr ⟨b, hbD⟩, Subtype.ext ?_⟩
      dsimp [f]
      rw [hus]
  have hA_le : Nat.card A ≤ 32 := by
    have h := Nat.card_le_card_of_surjective f hf_surj
    calc Nat.card A ≤ Nat.card (↥D ⊕ ↥D) := h
      _ = Nat.card D + Nat.card D := Nat.card_sum
      _ = 2 ^ 4 + 2 ^ 4 := by rw [hDcard]
      _ = 32 := by norm_num
  have hB_le_A : B ≤ A := (le_of_eq hsL.inf_eq.symm).trans inf_le_left
  have hB_le_L : B ≤ L := (le_of_eq hsL.inf_eq.symm).trans inf_le_right
  have hcent_le : L ⊓ centralizer (L : Set G) ≤ centerIn L := by
    intro x hx
    rw [centerIn, Subgroup.mem_map]
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (mem_centralizer_iff.mp hx.2 (w : G) w.2)
  have ht_notin_B : t ∉ B := by
    intro htB
    have ht_center : t ∈ L ⊓ centralizer (L : Set G) := ⟨hB_le_L htB, hsL.c_cent⟩
    have ht_bot : t ∈ (⊥ : Subgroup G) := by
      rw [← hP.center_triv G L hsL.om]
      exact hcent_le ht_center
    have ht1 : t = 1 := Subgroup.mem_bot.mp ht_bot
    have hcord : orderOf t = 2 := hsL.c_ord
    rw [ht1] at hcord
    exact absurd hcord (by simp)
  have hT_le_A : zpowers t ⊔ B ≤ A :=
    sup_le (Subgroup.zpowers_le_of_mem hsL.c_mem) hB_le_A
  have hmem_T : t ∈ zpowers t ⊔ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hBT_lt : B < zpowers t ⊔ B := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro h
    exact ht_notin_B (by rwa [h.symm] at hmem_T)
  have hTA_lt : zpowers t ⊔ B < A := lt_of_le_of_ne hT_le_A hne.symm
  have hBcard : Nat.card B = 2 ^ 4 := hsL.norm.2.1.2
  have hBpos : 0 < Nat.card B := by rw [hBcard]; norm_num
  have hT32 : 32 ≤ Nat.card ↥(zpowers t ⊔ B) := by
    have hdiv : Nat.card B ∣ Nat.card ↥(zpowers t ⊔ B) := Subgroup.card_dvd_of_le le_sup_right
    have hlt : Nat.card B < Nat.card ↥(zpowers t ⊔ B) := Subgroup.card_lt_of_lt hBT_lt
    have h2B : 2 * Nat.card B ≤ Nat.card ↥(zpowers t ⊔ B) := by
      have h1 : 1 < Nat.card ↥(zpowers t ⊔ B) / Nat.card B :=
        (Nat.lt_div_iff_mul_lt_of_dvd (by omega) hdiv).mpr (by simpa using hlt)
      have h2 : 2 ≤ Nat.card ↥(zpowers t ⊔ B) / Nat.card B := by omega
      exact (Nat.le_div_iff_mul_le hBpos).mp h2
    calc 32 = 2 * Nat.card B := by rw [hBcard]; norm_num
      _ ≤ Nat.card ↥(zpowers t ⊔ B) := h2B
  have hA64 : 64 ≤ Nat.card A := by
    have hdiv : Nat.card ↥(zpowers t ⊔ B) ∣ Nat.card A := Subgroup.card_dvd_of_le hT_le_A
    have hlt : Nat.card ↥(zpowers t ⊔ B) < Nat.card A := Subgroup.card_lt_of_lt hTA_lt
    have hpos : 0 < Nat.card ↥(zpowers t ⊔ B) := by omega
    have h2T : 2 * Nat.card ↥(zpowers t ⊔ B) ≤ Nat.card A := by
      have h1 : 1 < Nat.card A / Nat.card ↥(zpowers t ⊔ B) :=
        (Nat.lt_div_iff_mul_lt_of_dvd (by omega) hdiv).mpr (by simpa using hlt)
      have h2 : 2 ≤ Nat.card A / Nat.card ↥(zpowers t ⊔ B) := by omega
      exact (Nat.le_div_iff_mul_le hpos).mp h2
    calc 64 = 2 * 32 := by norm_num
      _ ≤ 2 * Nat.card ↥(zpowers t ⊔ B) := by gcongr
      _ ≤ Nat.card A := h2T
  omega

end CFSG.OddStandard.SmallF3.Omega
