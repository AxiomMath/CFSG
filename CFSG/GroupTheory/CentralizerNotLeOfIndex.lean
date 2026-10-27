module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem centralizer_not_le_of_dvd_index {B : Subgroup X}
    {r : ℕ} [Fact r.Prime] {y : X} (hyB : y ∈ B) (hy : orderOf y = r) (hr : r ∣ B.index)
    (hBr : ¬ r ^ 2 ∣ Nat.card B) : ¬ Subgroup.centralizer ({y} : Set X) ≤ B := by
  intro hC
  let P : Subgroup X := Subgroup.zpowers y
  let C : Subgroup X := Subgroup.centralizer ({y} : Set X)
  have hPcard : Nat.card P = r := by simp [P, Nat.card_zpowers, hy]
  have hPleC : P ≤ C :=
    Subgroup.zpowers_le.mpr (by simp [C, Subgroup.mem_centralizer_singleton_iff])
  obtain ⟨R, hPR⟩ := (IsPGroup.of_card (n := 1) (by simpa using hPcard)).exists_le_sylow
  have hr2R : r ^ 2 ∣ Nat.card R := by
    refine Sylow.pow_dvd_card_of_pow_dvd_card R ?_
    simpa [pow_two, hy, ← Subgroup.index_mul_card B] using
      Nat.mul_dvd_mul hr (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyB))
  have hRnt : Nontrivial ↥(R : Subgroup X) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    nlinarith [Nat.le_of_dvd Nat.card_pos hr2R, (Fact.out : r.Prime).two_le]
  obtain ⟨k, hDcard⟩ := ((Sylow.isPGroup' R).to_le (inf_le_right : C ⊓ R ≤ R)).exists_card_eq
  have hk : k ≤ 1 := by
    by_contra hk
    exact hBr ((hDcard ▸ Nat.pow_dvd_pow r (by omega : 2 ≤ k)).trans
      (Subgroup.card_dvd_of_le (inf_le_left.trans hC)))
  have hDdvd_r : Nat.card ↥(C ⊓ R) ∣ r := by
    rw [hDcard]
    simpa using Nat.pow_dvd_pow r hk
  have hPD : P = C ⊓ R := Subgroup.eq_of_le_of_card_ge (le_inf hPleC hPR)
    (by rw [hPcard]; exact Nat.le_of_dvd (Fact.out : r.Prime).pos hDdvd_r)
  have hPRcard : Nat.card ↥(P.subgroupOf R) = r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv).trans hPcard
  have hZleC : Subgroup.map (Subgroup.subtype (R : Subgroup X))
      (Subgroup.center (R : Subgroup X)) ≤ C :=
    (Subgroup.map_mono (Subgroup.center_le_centralizer
      ({⟨y, hPR (Subgroup.mem_zpowers y)⟩} : Set ↥(R : Subgroup X)))).trans
      ((Subgroup.map_centralizer_le_centralizer_image _ _).trans (by simp [C]))
  have hcenter_le : Subgroup.center (R : Subgroup X) ≤ P.subgroupOf R := by
    have h := Subgroup.map_le_iff_le_comap.mp hZleC
    rwa [Subgroup.comap_subtype, ← Subgroup.inf_subgroupOf_left C R, inf_comm, ← hPD] at h
  have hcenter_card : Nat.card (Subgroup.center (R : Subgroup X)) = r := by
    have hdvd : Nat.card (Subgroup.center (R : Subgroup X)) ∣ r := by
      simpa [hPRcard] using Subgroup.card_dvd_of_le hcenter_le
    have hgt : 1 < Nat.card (Subgroup.center (R : Subgroup X)) :=
      Finite.one_lt_card_iff_nontrivial.mpr ((Sylow.isPGroup' R).center_nontrivial)
    exact ((Fact.out : r.Prime).dvd_iff_eq (by omega)).mp hdvd |>.symm
  have hycenter : (⟨y, hPR (Subgroup.mem_zpowers y)⟩ : ↥(R : Subgroup X)) ∈
      Subgroup.center (R : Subgroup X) := by
    rw [Subgroup.eq_of_le_of_card_ge hcenter_le (by rw [hPRcard, hcenter_card])]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)
  have hRleC : R ≤ C := by
    intro w hw
    rw [show C = Subgroup.centralizer ({y} : Set X) from rfl,
      Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg (fun t : ↥(R : Subgroup X) => (t : X))
      (Subgroup.mem_center_iff.mp hycenter (⟨w, hw⟩ : ↥(R : Subgroup X)))
  have hcardR : Nat.card (R : Subgroup X) ∣ r :=
    (Subgroup.card_dvd_of_le (le_inf hRleC le_rfl : R ≤ C ⊓ R)).trans hDdvd_r
  have hle : r ^ 2 ≤ r := Nat.le_of_dvd (Fact.out : r.Prime).pos (hr2R.trans hcardR)
  nlinarith [(Fact.out : r.Prime).two_le]

end CFSG.GroupTheory
