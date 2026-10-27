
module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

structure WIsoD1Parts : Prop where
  d1 : ∀ kb ∈ kbList, kbFull kb = false →
    ∀ t < 64, ∀ i < 36, ∀ t' < 64, ∀ i' < 36, repInS.contains i = false →
      repInS.contains i' = false →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 →
      wordPerm (tg t') * repPerm i' * (wordPerm (tg t') * repPerm i') = 1 →
      wordPerm (tg t) * repPerm i * (wordPerm (tg t') * repPerm i') =
        wordPerm (tg t') * repPerm i' * (wordPerm (tg t) * repPerm i) →
      ∃ a ∈ allM, ∃ b ∈ allM, eqKB kb b a = false ∧ fixKB kb t i a = true ∧
        fixKB kb t' i' a = true ∧ isInvKB kb a = true ∧ fixKB kb t i b = true ∧
        fixKB kb t' i' b = true ∧ isInvKB kb b = true

structure WIsoDParts : Prop where
  d : ∀ kb ∈ kbList, ∀ t < 64, ∀ i < 36, repInS.contains i = false →
    wordPerm (tg t) * repPerm i * (wordPerm (tg t) * repPerm i) = 1 → liftsKB kb i = true →
    ∀ k < 64, (k = 0 ∨ ((mulM (k, 0, 0) (k, 0, 0)).1 = 0 ∧ (betaYM t i (k, 0, 0)).1 = k)) →
    (∃ x, (x ∈ allM ∧ fixKB kb t i x = true ∧ isInvKB kb x = true ∧
        eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) ∧ x.1 ≠ 0 ∧ x.1 ≠ k) ∨
      (∃ a b c d, (∀ x ∈ [a, b, c, d], x ∈ allM ∧ fixKB kb t i x = true ∧
          isInvKB kb x = true ∧ eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) ∧
        eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false ∧
        eqKB kb d a = false ∧ eqKB kb d b = false ∧ eqKB kb d c = false) ∨
      (k ≠ 0 ∧ typeOf t i = expType kb ∧ (kbZero kb = true ∨ kbCyc kb = true) ∧
        (kbFull kb = true ∨ ∃ a b c, (∀ x ∈ [a, b, c], x ∈ allM ∧ fixKB kb t i x = true ∧
            isInvKB kb x = true ∧ eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) ∧
          eqKB kb b a = false ∧ eqKB kb c a = false ∧ eqKB kb c b = false))

noncomputable abbrev yPerm (t i : ℕ) : Equiv.Perm (Fin 42) := wordPerm (tg t) * repPerm i

noncomputable abbrev rhoPerm (lab : ℕ) : Equiv.Perm (Fin 42) :=
  if lab = 0 then r₂ else if lab = 1 then r₃ else r₄

structure WIsoTypeParts : Prop where
  kClass : ∀ K : AddSubgroup (ZMod 4 × ZMod 4), ∃ kb ∈ kbList, ∀ i j : ZMod 4,
    inKB kb i j = true ↔ (i, j) ∈ K
  types : ∀ t i : ℕ, typeOf t i < 3 → ∃ t' < 64, ∃ j < 36,
    yPerm t' j * yPerm t i * (yPerm t' j)⁻¹ = rhoPerm (typeOf t i)
  outer : ∀ t < 64, ∀ i < 36, repInS.contains i = false → yPerm t i * yPerm t i = 1 →
    typeOf t i < 3
  pairs : ∀ t < 64, ∀ i < 36, ∀ t' < 64, ∀ i' < 36, repInS.contains i = false →
    repInS.contains i' = false → yPerm t i * yPerm t i = 1 → yPerm t' i' * yPerm t' i' = 1 →
    yPerm t i * yPerm t' i' = yPerm t' i' * yPerm t i → yPerm t i * yPerm t' i' ∉ S →
    typeOf t i ≠ typeOf t' i'

theorem inKB_zero_iff {i j : ZMod 4} : inKB (kbOfMask 1) i j = true ↔ i = 0 ∧ j = 0 := by
  revert i j
  decide

theorem inKB_full (i j : ZMod 4) : inKB (kbOfMask 65535) i j = true := by
  revert i j
  decide

theorem eq_of_kbZero {kb : List Bool} (h : kbZero kb = true) : kb = kbOfMask 1 := by
  simpa [kbZero] using h

theorem eq_of_kbFull {kb : List Bool} (h : kbFull kb = true) : kb = kbOfMask 65535 := by
  simpa [kbFull] using h

theorem kbCyc_spec {kb : List Bool} (h : kbCyc kb = true) :
    ∃ g₁ g₂ : ZMod 4, ∀ i j : ZMod 4, ∃ m : ZMod 4, inKB kb (i - m * g₁) (j - m * g₂) = true := by
  simp only [kbCyc, List.any_eq_true, List.all_eq_true] at h
  obtain ⟨g₁, -, g₂, -, h⟩ := h
  refine ⟨g₁, g₂, fun i j => ?_⟩
  obtain ⟨m, -, hm⟩ := h i (by simp [z4]; revert i; decide) j (by simp [z4]; revert j; decide)
  exact ⟨m, hm⟩

theorem mem_outerInvs_of {t i : ℕ} (ht : t < 64) (hi : i < 36) (hS : repInS.contains i = false)
    (h2 : (comp 42 (yTab t i) (yTab t i) == idTab 42) = true) : (t, i) ∈ outerInvs := by
  simp only [outerInvs, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  rw [hS]
  simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨t, ⟨ht, h2⟩, rfl⟩

theorem lt_of_mem_outerInvs {p : ℕ × ℕ} (hp : p ∈ outerInvs) : p.1 < 64 ∧ p.2 < 36 := by
  simp only [outerInvs, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨i, hi, hp⟩ := hp
  split_ifs at hp
  · simp at hp
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hp
    exact ⟨List.mem_range.mp (List.mem_filter.mp ht).1, hi⟩

theorem mem_fixInvs {kb : List Bool} {t i : ℕ} {x : MElt} :
    x ∈ fixInvs kb t i ↔ x ∈ allM ∧ fixKB kb t i x = true ∧ isInvKB kb x = true := by
  simp [fixInvs]

theorem mem_kVals_of {t i k : ℕ} (hk : k < 64)
    (h : k = 0 ∨ ((mulM (k, 0, 0) (k, 0, 0)).1 = 0 ∧ (betaYM t i (k, 0, 0)).1 = k)) :
    k ∈ kVals t i := by
  simp only [kVals, List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true]
  exact ⟨hk, h⟩

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
