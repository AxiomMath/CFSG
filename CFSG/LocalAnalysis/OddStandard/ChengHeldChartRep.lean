module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldChartPure

public section

namespace CFSG.OddStandard.ChengHeld.M1b

open Subgroup CFSG.Open CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit.L34Facts.Real

@[expose] def kindIdx : Kind → ℕ
  | .field => 1
  | .graph => 2
  | .unitary => 3

section Rep

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}
  (d : Datum A)

open Classical in
@[expose] noncomputable def repOf (P : Pos d) (k : Kind) : Option G :=
  if h : ∃ (y : G) (hy : y ∈ d.X), Pure d P.l (kindIdx k) y hy then
    some (Classical.choose h) else none

theorem repOf_spec (P : Pos d) {k : Kind} {y : G} (h : repOf d P k = some y) :
    ∃ hy : y ∈ d.X, Pure d P.l (kindIdx k) y hy := by
  unfold repOf at h
  by_cases hex : ∃ (y : G) (hy : y ∈ d.X), Pure d P.l (kindIdx k) y hy
  · simp only [hex, dite_true, Option.some.injEq] at h
    subst h
    exact Classical.choose_spec hex
  · simp [hex] at h

theorem repOf_of_pure (P : Pos d) {k : Kind} {y : G} (hy : y ∈ d.X)
    (hp : Pure d P.l (kindIdx k) y hy) : ∃ y0, repOf d P k = some y0 := by
  have hex : ∃ (y : G) (hy : y ∈ d.X), Pure d P.l (kindIdx k) y hy := ⟨y, hy, hp⟩
  exact ⟨Classical.choose hex, by simp only [repOf, hex, dite_true]⟩

theorem repOf_mem (h : Hyp G A) (P : Pos d) {k : Kind} {y : G} (hk : repOf d P k = some y) :
    y ∈ d.X ∧ y ∉ d.QS := by
  obtain ⟨hy, hp⟩ := repOf_spec d P hk
  refine ⟨hy, not_mem_QS_of_pure d h P.isQ ?_ ?_ hp⟩ <;> cases k <;> simp [kindIdx]

theorem repOf_cover (h : Hyp G A) (P : Pos d) {y : G} (hy : y ∈ d.X) (hyQS : y ∉ d.QS) :
    ∃ (k : Kind) (y0 : G), repOf d P k = some y0 ∧ ∃ u ∈ d.QS, y = u * y0 := by
  obtain ⟨k₀, hk₀, t, ht, hreal, s, hs, hys, hp⟩ := pure_exists d P hy
  have hsQS : s ∈ d.QS := mem_sup_right hs
  have hk1 : k₀ ≠ 0 := by
    intro hk0
    subst hk0
    apply hyQS
    have hc := mem_centralizer_of_pure_zero d h P.isQ hp
    have hQ : y * s ∈ d.Q := ⟨hys, hc⟩
    have : y = y * s * s⁻¹ := by group
    rw [this]
    exact d.QS.mul_mem (mem_sup_left hQ) (d.QS.inv_mem hsQS)
  obtain ⟨k, hkk⟩ : ∃ k : Kind, kindIdx k = k₀ := by
    interval_cases k₀
    · exact absurd rfl hk1
    · exact ⟨.field, rfl⟩
    · exact ⟨.graph, rfl⟩
    · exact ⟨.unitary, rfl⟩
  rw [← hkk] at hp
  obtain ⟨y0, hy0⟩ := repOf_of_pure d P hys hp
  obtain ⟨hy0X, hp0⟩ := repOf_spec d P hy0
  have hc := pure_unique d h P.isQ.lsurj hp hp0
  refine ⟨k, y0, hy0, (y * s * y0⁻¹) * (y0 * s⁻¹ * y0⁻¹), ?_, by group⟩
  exact d.QS.mul_mem (mem_sup_left hc)
    (mem_sup_right (by simpa [mul_assoc] using d.conj_mem_S hy0X (d.S.inv_mem hs)))

end Rep

end CFSG.OddStandard.ChengHeld.M1b
