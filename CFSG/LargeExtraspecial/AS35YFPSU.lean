module

public import CFSG.LargeExtraspecial.AS35YFOut
public import CFSG.LargeExtraspecial.AS35YFIrr
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

namespace AS35YF

theorem not_four_dvd_card_outer_PG {m : ℕ} (hm : 4 ≤ m) : ¬ 4 ∣ Nat.card (Outer (PG m)) := by
  have e : PG m ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU S14.unitaryFieldData_two_one m :=
    (AS35U.pgEquiv (by omega)).trans (S14.timmesfeldPSUEquiv (by omega))
  have h := (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order
    S14.unitaryFieldData_two_one (n := m) (by omega) (by omega)).2.2.2.2.1
  rw [Nat.card_congr (equivalence e).toEquiv, h]
  intro h4
  have hg : Nat.gcd m (2 ^ 1 + 1) ∣ 3 := Nat.gcd_dvd_right _ _
  have hg' : Nat.gcd m (2 ^ 1 + 1) = 1 ∨ Nat.gcd m (2 ^ 1 + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hg
  rcases hg' with h1 | h1 <;> rw [h1] at h4 <;> norm_num at h4

theorem exists_ne_of_two_lt_card {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y} (a : Y)
    (h : 2 < Nat.card N) : ∃ x ∈ N, x ≠ 1 ∧ x ≠ a := by
  by_contra hall
  push Not at hall
  have hsub : (N : Set Y) ⊆ {1, a} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hall x hx hx1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq] at h
  have h2 : ({1, a} : Set Y).ncard ≤ 2 := by
    have := Set.ncard_insert_le 1 ({a} : Set Y)
    rwa [Set.ncard_singleton] at this
  omega

theorem le_of_card_subgroupOf_eq {H : Type*} [Group H] [Finite H] {A B : Subgroup H}
    (h : Nat.card (A.subgroupOf B) = Nat.card A) : A ≤ B := by
  rw [Setting.asc_card_subgroupOf_comm] at h
  have htop : B.subgroupOf A = ⊤ := Subgroup.card_eq_iff_eq_top _ |>.mp h
  exact Subgroup.subgroupOf_eq_top.mp htop

end AS35YF

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

variable (hst : S.Asc512Standing)
include hst

theorem asc_eq_width_of_psu (hP : S14.Asc512PbarStmt) (hS : S.SixHyp) {m : ℕ} (hm : 4 ≤ m)
    (ψ : S.LbarAsc ⧸ center S.LbarAsc ≃* PG m) (hψ : ψ '' S.EhatAsc = DG m) {g : G}
    (htD : g * S.z * g⁻¹ ∈ S.DSet) (htM : g * S.z * g⁻¹ ∈ S.M) :
    m = S.width ∧ S.PbarAsc g ≤ S.LbarAsc := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hk : 2 ≤ k := by omega
  have htE : (QuotientGroup.mk (ascTL htD htM) : S.LbarAsc ⧸ center S.LbarAsc) ∈ S.EhatAsc :=
    ⟨ascTL htD htM, S.ρ_mem_DbarAsc htD htM, rfl⟩
  have hψt : ψ (QuotientGroup.mk (ascTL htD htM)) ∈ DG (k + 2) := hψ ▸ ⟨_, htE, rfl⟩
  rw [DG_eq_isConj (by omega) v₀_ne_zero herm_v₀_v₀] at hψt
  obtain ⟨c, hc⟩ := isConj_iff.mp hψt
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : S.LbarAsc ⧸ center S.LbarAsc ≃* PG (k + 2),
      ψ' = ψ.trans (MulAut.conj c⁻¹) := ⟨_, rfl⟩
  have hψ't : ψ' (QuotientGroup.mk (ascTL htD htM)) = tq (v₀ k) := by
    rw [hψ', MulEquiv.trans_apply, MulAut.conj_apply, ← hc]
    group
  have hA := (ascImage_ascPhat hst hP hS htD htM).map ψ'
  rw [hψ't] at hA
  have hcardN : Nat.card ((S.ascPhat g).map ψ'.toMonoidHom) =
      Nat.card ((S.PbarAsc g).subgroupOf S.LbarAsc) := by
    rw [Subgroup.card_map_of_injective ψ'.injective, card_ascPhat hst hP hS htD htM]
  have hout : ¬ 4 ∣ Nat.card (Outer (S.LbarAsc ⧸ center S.LbarAsc)) := by
    rw [Nat.card_congr (equivalence ψ).toEquiv]
    exact AS35YF.not_four_dvd_card_outer_PG hm
  have hidx := asc_card_Pbar_le_two_mul hst hP hS htD htM hout
  have hPcard : Nat.card (S.PbarAsc g) = 2 ^ (2 * S.width - 3) := (hP G S hS g htD htM).2.2.1
  have hn3 := hS.three_le_width
  have h8 : 2 ^ 3 ≤ 2 ^ (2 * S.width - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hne := AS35YF.exists_ne_of_two_lt_card (N := (S.ascPhat g).map ψ'.toMonoidHom)
    (tq (v₀ k)) (by omega)
  have hN := AS35YF.card_eq_of_normalized hk hA.isPGroup hA.commute hA.normal hA.mem hne
  have hle : Nat.card ((S.PbarAsc g).subgroupOf S.LbarAsc) ≤ Nat.card (S.PbarAsc g) := by
    rw [asc_card_subgroupOf_comm]
    exact Subgroup.card_le_of_le le_top |>.trans_eq Subgroup.card_top
  rw [hcardN] at hN
  rw [hN, hPcard] at hle
  rw [hN, hPcard] at hidx
  have h1 : 2 * k + 1 ≤ 2 * S.width - 3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  have h2 : 2 * S.width - 3 ≤ 2 * k + 2 := by
    have : 2 ^ (2 * S.width - 3) ≤ 2 ^ (2 * k + 2) := by
      have e : 2 ^ (2 * k + 2) = 2 * 2 ^ (2 * k + 1) := by ring
      rw [e]
      exact hidx
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hmn : k + 2 = S.width := by omega
  refine ⟨hmn, AS35YF.le_of_card_subgroupOf_eq ?_⟩
  rw [hN, hPcard]
  congr 1
  omega

end Setting

namespace S14

open CFSG.Open Matrix in
theorem asc512InspFor_psu (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerPSU X D := by
  intro G _ _ S hS hst hfam
  obtain ⟨-, m, hm, hmodel⟩ := hfam
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 hmodel
  set ψ := φ.trans (u2Equiv m) with hψdef
  have hψ : ψ '' S.EhatAsc = DG m := by
    rw [hψdef, MulEquiv.coe_trans, Set.image_comp, hφ, image_DU]
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  obtain ⟨g, rfl⟩ := Setting.exists_conj_of_mem_DSet S ht
  have hgM := Setting.mem_M_of_mem_ESet S hS.sixFour ht.1
  obtain ⟨hmn, -⟩ := Setting.asc_eq_width_of_psu hst hP hS hm ψ hψ ht hgM
  left
  refine ⟨hmn ▸ hm, ⟨hmn ▸ ψ.trans (AS35U.pgEquiv (by omega))⟩, fun g' hg' => ?_⟩
  exact (Setting.asc_eq_width_of_psu hst hP hS hm ψ hψ hg'
    (Setting.mem_M_of_mem_ESet S hS.sixFour hg'.1)).2

end S14

end CFSG.LargeExtraspecial
