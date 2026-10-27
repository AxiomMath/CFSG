module

public import CFSG.Quasithin.Background.Equivariance
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open Subgroup CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_le_self (Y : Subgroup G) : thompsonJ Y ≤ Y :=
  iSup₂_le fun A hA => hA.1

theorem omegaOneCenter_le_self (Y : Subgroup G) : quasithinOmegaOneCenter Y ≤ Y :=
  (Subgroup.closure_le _).2 fun z hz => hz.1.1

omit [Finite G] in
private theorem case1_isElemAbelian_bot : IsElemAbelian 2 (⊥ : Subgroup G) :=
  CFSG.Open.isElemAbelian_bot _

private theorem case1_exists_isMaxElemAbelian (H : Subgroup G) :
    ∃ A : Subgroup G, IsMaxElemAbelian H A := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  set s := (Finset.univ : Finset (Subgroup G)).filter (fun A => A ≤ H ∧ IsElemAbelian 2 A)
    with hs
  have hbot : (⊥ : Subgroup G) ∈ s := by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, bot_le, case1_isElemAbelian_bot⟩
  obtain ⟨A, hAs, hmax⟩ := s.exists_max_image (fun A => Nat.card A) ⟨⊥, hbot⟩
  rw [hs, Finset.mem_filter] at hAs
  refine ⟨A, hAs.2.1, hAs.2.2, fun B hB hBe => hmax B ?_⟩
  rw [hs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hB, hBe⟩

omit [Finite G] in
private theorem case1_le_thompsonJ {H A : Subgroup G} (hA : IsMaxElemAbelian H A) :
    A ≤ thompsonJ H :=
  le_iSup₂_of_le A hA le_rfl

theorem thompsonJ_ne_bot_of_two_group {Y : Subgroup G} (hY : IsPGroup 2 Y) (h1 : Y ≠ ⊥) :
    thompsonJ Y ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := case1_exists_isMaxElemAbelian Y
  have h2 : 2 ∣ Nat.card Y := by
    obtain ⟨n, hn⟩ := hY.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact h1 (Subgroup.eq_bot_of_card_eq Y (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 h2
  have hZ : IsElemAbelian 2 (Subgroup.zpowers (t : G)) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have ht2 : (t : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers (t : G)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hle : Subgroup.zpowers (t : G) ≤ Y := (Subgroup.zpowers_le).mpr t.2
  have h3 := hA.2.2 _ hle hZ
  intro hJ
  have hAbot : A = ⊥ := le_bot_iff.mp (hJ ▸ case1_le_thompsonJ hA)
  rw [hAbot, Subgroup.card_bot, hcard] at h3
  omega

theorem omegaOneCenter_ne_bot_of_two_group {Y : Subgroup G} (hY : IsPGroup 2 Y) (h1 : Y ≠ ⊥) :
    quasithinOmegaOneCenter Y ≠ ⊥ := by
  have : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr h1
  have hc : Nontrivial (Subgroup.center Y) := hY.center_nontrivial
  have hcp : IsPGroup 2 (Subgroup.center Y) := hY.to_subgroup _
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
    exact not_subsingleton (Subgroup.center Y) hn.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    omega
  set g : G := ((x : Y) : G) with hg
  have hgY : g ∈ Y := (x : Y).2
  have hgC : g ∈ Subgroup.centralizer (Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨t, ht⟩)
  have hg2 : g ^ 2 = 1 := by
    have := congrArg (fun y : Subgroup.center Y => ((y : Y) : G)) hx2
    simpa using this
  have hg1 : g ≠ 1 := by
    intro h
    exact hx1 (Subtype.ext (Subtype.ext h))
  intro h
  have hmem : g ∈ quasithinOmegaOneCenter Y := Subgroup.subset_closure ⟨⟨hgY, hgC⟩, hg2⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hg1 hmem

theorem normalizer_le_normalizer_omegaOneCenter (Y : Subgroup G) :
    normalizer (Y : Set G) ≤ normalizer (quasithinOmegaOneCenter Y : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv (F := quasithinOmegaOneCenter)
    (fun φ X => by
      have h := omegaOneCenterOf_map_mulEquiv φ X
      rw [omegaOneCenterOf_eq, omegaOneCenterOf_eq] at h
      exact h) Y

theorem normalizer_le_normalizer_thompsonJ' (Y : Subgroup G) :
    normalizer (Y : Set G) ≤ normalizer (thompsonJ Y : Set G) :=
  CFSG.Quasithin.normalizer_le_normalizer_thompsonJ Y

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
