
module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Chk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameSylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.GH74.KGroups CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.ClassicalInvolution.Q3.TA3.Check
  CFSG.ComponentClassification.GSThmB

local notation "P45" => Equiv.Perm (Fin 45)

namespace Mo107

open Certificates.OmegaS107

theorem card_over
    {T : Subgroup P45} (hT0 : QT0.originalSubgroup ≤ T) (hTA : T ≤ QA45.originalSubgroup)
    (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T) (hwT0 : w ∉ QT0.originalSubgroup) :
    Nat.card T = 128 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT2
  have h1 : Nat.card T ∣ Nat.card QA45.originalSubgroup := Subgroup.card_dvd_of_le hTA
  have h2 : Nat.card QT0.originalSubgroup ∣ Nat.card T := Subgroup.card_dvd_of_le hT0
  have h3 : Nat.card T ≠ 64 := by
    intro h
    have heq : T = QT0.originalSubgroup :=
      (Subgroup.eq_of_le_of_card_ge hT0 (by rw [h, card_QT0])).symm
    exact hwT0 (heq ▸ hw)
  rw [card_QA45, hn] at h1
  rw [card_QT0, hn] at h2
  rw [hn] at h3 ⊢
  have hle : 2 ^ n ≤ 51840 := Nat.le_of_dvd (by norm_num) h1
  have hn16 : n < 16 := by
    by_contra h
    have : 2 ^ 16 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.1 h)
    omega
  interval_cases n <;> first | rfl | (exfalso; revert h1 h2 h3; norm_num)

theorem relIndex_over
    {T : Subgroup P45} (hT0 : QT0.originalSubgroup ≤ T) (hTA : T ≤ QA45.originalSubgroup)
    (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T) (hwT0 : w ∉ QT0.originalSubgroup) :
    (QT0.originalSubgroup.subgroupOf T).index = 2 := by
  have h := Subgroup.relIndex_mul_card (H := QT0.originalSubgroup) (K := T)
  rw [inf_eq_left.2 hT0, card_QT0, card_over hT0 hTA hT2 hw hwT0] at h
  change QT0.originalSubgroup.relIndex T = 2
  generalize QT0.originalSubgroup.relIndex T = r at h ⊢
  omega

theorem normal_over
    {T : Subgroup P45} (hT0 : QT0.originalSubgroup ≤ T) (hTA : T ≤ QA45.originalSubgroup)
    (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T) (hwT0 : w ∉ QT0.originalSubgroup) :
    ∀ g ∈ T, ∀ a ∈ QT0.originalSubgroup, g * a * g⁻¹ ∈ QT0.originalSubgroup := by
  intro g hg a ha
  have hN := Subgroup.normal_of_index_eq_two (relIndex_over hT0 hTA hT2 hw hwT0)
  have h := hN.conj_mem ⟨a, hT0 ha⟩ (Subgroup.mem_subgroupOf.2 ha) ⟨g, hg⟩
  exact Subgroup.mem_subgroupOf.1 h

theorem exists_mul_over
    {T : Subgroup P45} (hT0 : QT0.originalSubgroup ≤ T) (hTA : T ≤ QA45.originalSubgroup)
    (hT2 : IsPGroup 2 T) {w : P45} (hw : w ∈ T) (hwT0 : w ∉ QT0.originalSubgroup) {x : P45}
    (hx : x ∈ T) (hxT0 : x ∉ QT0.originalSubgroup) :
    ∃ a ∈ QT0.originalSubgroup, a * w = x := by
  have hH := relIndex_over hT0 hTA hT2 hw hwT0
  have h := (Subgroup.mul_mem_iff_of_index_two hH (a := (⟨x, hx⟩ : T)) (b := (⟨w, hw⟩ : T)⁻¹)).2
  have h1 : (⟨x, hx⟩ : T) ∈ QT0.originalSubgroup.subgroupOf T ↔ False :=
    iff_false_intro fun h => hxT0 (Subgroup.mem_subgroupOf.1 h)
  have h2 : (⟨w, hw⟩ : T)⁻¹ ∈ QT0.originalSubgroup.subgroupOf T ↔ False := by
    refine iff_false_intro fun h => hwT0 ?_
    have := (QT0.originalSubgroup.subgroupOf T).inv_mem h
    simpa using Subgroup.mem_subgroupOf.1 this
  have h3 := h (by rw [h1, h2])
  refine ⟨x * w⁻¹, Subgroup.mem_subgroupOf.1 h3, ?_⟩
  simp

end Mo107

end CFSG.OddStandard.SmallF3.Omega
