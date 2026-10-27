module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcMain
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE7
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharDataE8
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1ExcData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Timmesfeld.Steinberg
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Exc
open CFSG.RankThree.Lattice (toVec)

@[expose] def e7U2 : Fin Tag.E7.rank → ZMod 3 := ![0, 1, 0, 0, 0, 0, 0]

def e7Ord2 : List (List ℤ) :=
  [[-1, 0, -1, -1, -1, -1, -1],
   [-1, 0, -1, -1, -1, -1, 0],
   [-1, 0, -1, -1, -1, 0, 0],
   [-1, 0, -1, -1, 0, 0, 0],
   [-1, 0, -1, 0, 0, 0, 0],
   [-1, 0, 0, 0, 0, 0, 0],
   [0, 0, -1, -1, -1, -1, -1],
   [0, 0, -1, -1, -1, -1, 0],
   [0, 0, -1, -1, -1, 0, 0],
   [0, 0, -1, -1, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0],
   [0, 0, 0, -1, -1, -1, -1],
   [0, 0, 0, -1, -1, -1, 0],
   [0, 0, 0, -1, -1, 0, 0],
   [0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 0, -1, -1, -1],
   [0, 0, 0, 0, -1, -1, 0],
   [0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 0, -1, -1],
   [0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 1, 1, 1],
   [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, 1, 1, 1, 1],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0],
   [0, 0, 1, 1, 1, 0, 0],
   [0, 0, 1, 1, 1, 1, 0],
   [0, 0, 1, 1, 1, 1, 1],
   [1, 0, 0, 0, 0, 0, 0],
   [1, 0, 1, 0, 0, 0, 0],
   [1, 0, 1, 1, 0, 0, 0],
   [1, 0, 1, 1, 1, 0, 0],
   [1, 0, 1, 1, 1, 1, 0],
   [1, 0, 1, 1, 1, 1, 1]]

theorem e7_sound2 : ∀ l ∈ e7Ord2, l ∈ Tag.E7.artifactRoots ∧
    dotT e7U2 (toVec Tag.E7.rank l) = 0 := by
  decide +kernel

theorem e7_complete2 : ∀ l ∈ Tag.E7.artifactRoots, dotT e7U2 (toVec Tag.E7.rank l) = 0 →
    l ∈ e7Ord2 := by
  decide +kernel

theorem e7_ordconn2 : ∀ j : ℕ, j < (e7Ord2.map (toVec Tag.E7.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e7Ord2.map (toVec Tag.E7.rank)).getD i default)
      ((e7Ord2.map (toVec Tag.E7.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e7_nodup2 : (e7Ord2.map (toVec Tag.E7.rank)).Nodup := by decide +kernel

theorem e7_length2 : (e7Ord2.map (toVec Tag.E7.rank)).length = 6 * (6 + 1) := by decide +kernel

def e7B2 : List (List ℤ) :=
  [[1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]]

def e7N2 : ℤ := 1

theorem e7_rank2 : compRank {γ | γ ∈ e7Ord2.map (toVec Tag.E7.rank)} = 6 := by
  have hB : ∀ j : Fin 6, toVec Tag.E7.rank (e7B2.getD j []) ∈
      e7Ord2.map (toVec Tag.E7.rank) := by
    decide +kernel
  have hP : ∀ i j : Fin 6, ∑ l, toVec Tag.E7.rank (e7B2.getD i []) l *
      toVec Tag.E7.rank (e7B2.getD j []) l = if i = j then e7N2 else 0 := by
    decide +kernel
  have hrel : ∀ l ∈ e7Ord2, ∑ i, toVec Tag.E7.rank [0, 1, 0, 0, 0, 0, 0] i *
      toVec Tag.E7.rank l i = 0 := by
    decide +kernel
  have h1 : 6 ≤ compRank {γ | γ ∈ e7Ord2.map (toVec Tag.E7.rank)} :=
    le_compRank_of_cert (k := 6) (fun j => toVec Tag.E7.rank (e7B2.getD j []))
      (fun j => toVec Tag.E7.rank (e7B2.getD j [])) e7N2 (by decide) hB hP
  have h2 : compRank {γ | γ ∈ e7Ord2.map (toVec Tag.E7.rank)} + 1 ≤ Tag.E7.rank :=
    compRank_succ_le_of_relation (toVec Tag.E7.rank [0, 1, 0, 0, 0, 0, 0])
      (by decide +kernel) (by
        intro γ hγ
        obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hγ
        exact hrel l hl)
  have h3 : Tag.E7.rank = 7 := rfl
  omega


def e7OrdC13 : List (List ℤ) :=
  [[0, 0, -1, -1, -1, -1, -1],
   [0, 0, -1, -1, -1, -1, 0],
   [0, 0, -1, -1, -1, 0, 0],
   [0, 0, -1, -1, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0],
   [0, 0, 0, -1, -1, -1, -1],
   [0, 0, 0, 0, -1, -1, -1],
   [0, 0, 0, 0, 0, -1, -1],
   [0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 1, 1, 1],
   [0, 0, 0, 1, 1, 1, 1],
   [0, 0, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0],
   [0, 0, 1, 1, 1, 0, 0],
   [0, 0, 1, 1, 1, 1, 0],
   [0, 0, 1, 1, 1, 1, 1],
   [0, 0, 0, -1, -1, -1, 0],
   [0, 0, 0, 0, -1, -1, 0],
   [0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, -1, -1, 0, 0],
   [0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0]]

theorem e7OrdC13_Csub1 : ∀ γ ∈ e7OrdC13.map (toVec Tag.E7.rank),
    γ ∈ e7Ord2.map (toVec Tag.E7.rank) ∧
      dotT (vec3 (τ := .E7) (e7ThreeReps.getD 1 [])) γ = 0 := by
  decide +kernel

theorem e7OrdC13_Csub3 : ∀ γ ∈ e7OrdC13.map (toVec Tag.E7.rank),
    γ ∈ e7Ord2.map (toVec Tag.E7.rank) ∧
      dotT (vec3 (τ := .E7) (e7ThreeReps.getD 3 [])) γ = 0 := by
  decide +kernel

theorem e7OrdC13_Cconn : ∀ j : ℕ, j < (e7OrdC13.map (toVec Tag.E7.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e7OrdC13.map (toVec Tag.E7.rank)).getD i default)
      ((e7OrdC13.map (toVec Tag.E7.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e7OrdC13_nodupC : (e7OrdC13.map (toVec Tag.E7.rank)).Nodup := by decide +kernel

theorem e7OrdC13_lengthC : (e7OrdC13.map (toVec Tag.E7.rank)).length = 30 := by decide +kernel

def e7OrdC45 : List (List ℤ) :=
  [[0, 0, 0, -1, -1, -1, -1],
   [0, 0, 0, -1, -1, -1, 0],
   [0, 0, 0, -1, -1, 0, 0],
   [0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 0, -1, -1, -1],
   [0, 0, 0, 0, 0, -1, -1],
   [0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 1, 1, 1],
   [0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 0, -1, -1, 0],
   [0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 1, 0, 0]]

theorem e7OrdC45_Csub4 : ∀ γ ∈ e7OrdC45.map (toVec Tag.E7.rank),
    γ ∈ e7Ord2.map (toVec Tag.E7.rank) ∧
      dotT (vec3 (τ := .E7) (e7ThreeReps.getD 4 [])) γ = 0 := by
  decide +kernel

theorem e7OrdC45_Csub5 : ∀ γ ∈ e7OrdC45.map (toVec Tag.E7.rank),
    γ ∈ e7Ord2.map (toVec Tag.E7.rank) ∧
      dotT (vec3 (τ := .E7) (e7ThreeReps.getD 5 [])) γ = 0 := by
  decide +kernel

theorem e7OrdC45_Cconn : ∀ j : ℕ, j < (e7OrdC45.map (toVec Tag.E7.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e7OrdC45.map (toVec Tag.E7.rank)).getD i default)
      ((e7OrdC45.map (toVec Tag.E7.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e7OrdC45_nodupC : (e7OrdC45.map (toVec Tag.E7.rank)).Nodup := by decide +kernel

theorem e7OrdC45_lengthC : (e7OrdC45.map (toVec Tag.E7.rank)).length = 20 := by decide +kernel

theorem e7_Csub2 : ∀ γ ∈ e7Ord2.map (toVec Tag.E7.rank),
    γ ∈ e7Ord2.map (toVec Tag.E7.rank) ∧
      dotT (vec3 (τ := .E7) (e7ThreeReps.getD 2 [])) γ = 0 := by
  decide +kernel

theorem e7_num30 : ∀ m : ℕ, 30 ≤ m * (m - 1) → 4 ≤ m ∧ 6 + 1 < 2 * m := by
  intro m h
  by_cases hm : 4 ≤ m
  · exact ⟨hm, by omega⟩
  · exfalso
    interval_cases m <;> omega

theorem e7_num20 : ∀ m : ℕ, 20 ≤ m * (m - 1) → 4 ≤ m ∧ 6 + 1 < 2 * m := by
  intro m h
  by_cases hm : 4 ≤ m
  · exact ⟨hm, by omega⟩
  · exfalso
    interval_cases m <;> omega

theorem e7_num42 : ∀ m : ℕ, 42 ≤ m * (m - 1) → 4 ≤ m ∧ 6 + 1 < 2 * m := by
  intro m h
  by_cases hm : 4 ≤ m
  · exact ⟨hm, by omega⟩
  · exfalso
    interval_cases m <;> omega


def e8OrdC13 : List (List ℤ) :=
  [[0, 0, -1, -1, -1, -1, -1, -1],
   [0, 0, -1, -1, -1, -1, -1, 0],
   [0, 0, -1, -1, -1, -1, 0, 0],
   [0, 0, -1, -1, -1, 0, 0, 0],
   [0, 0, -1, -1, 0, 0, 0, 0],
   [0, 0, -1, 0, 0, 0, 0, 0],
   [0, 0, 0, -1, -1, -1, -1, -1],
   [0, 0, 0, 0, -1, -1, -1, -1],
   [0, 0, 0, 0, 0, -1, -1, -1],
   [0, 0, 0, 0, 0, 0, -1, -1],
   [0, 0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 0, 1, 1, 1],
   [0, 0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 1, 1, 1, 1, 1],
   [0, 0, 1, 0, 0, 0, 0, 0],
   [0, 0, 1, 1, 0, 0, 0, 0],
   [0, 0, 1, 1, 1, 0, 0, 0],
   [0, 0, 1, 1, 1, 1, 0, 0],
   [0, 0, 1, 1, 1, 1, 1, 0],
   [0, 0, 1, 1, 1, 1, 1, 1],
   [0, 0, 0, -1, -1, -1, -1, 0],
   [0, 0, 0, 0, -1, -1, -1, 0],
   [0, 0, 0, 0, 0, -1, -1, 0],
   [0, 0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, 1, 1, 1, 1, 0],
   [0, 0, 0, -1, -1, -1, 0, 0],
   [0, 0, 0, 1, 1, 1, 0, 0],
   [0, 0, 0, 0, -1, -1, 0, 0],
   [0, 0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, -1, -1, 0, 0, 0],
   [0, 0, 0, 1, 1, 0, 0, 0],
   [0, 0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0],
   [0, 0, 0, -1, 0, 0, 0, 0],
   [0, 0, 0, 1, 0, 0, 0, 0]]

theorem e8OrdC13_mem : ∀ l ∈ e8OrdC13, l ∈ Tag.E8.artifactRoots := by decide +kernel

theorem e8OrdC13_dotU : ∀ l ∈ e8OrdC13, dotT e8U (toVec Tag.E8.rank l) = 0 := by
  decide +kernel

theorem e8OrdC13_dot1 : ∀ l ∈ e8OrdC13,
    dotT (vec3 (τ := .E8) (e8ThreeReps.getD 1 [])) (toVec Tag.E8.rank l) = 0 := by
  decide +kernel

theorem e8OrdC13_dot3 : ∀ l ∈ e8OrdC13,
    dotT (vec3 (τ := .E8) (e8ThreeReps.getD 3 [])) (toVec Tag.E8.rank l) = 0 := by
  decide +kernel

theorem e8OrdC13_Csub1 : ∀ γ ∈ e8OrdC13.map (toVec Tag.E8.rank),
    γ ∈ e8Ord.map (toVec Tag.E8.rank) ∧
      dotT (vec3 (τ := .E8) (e8ThreeReps.getD 1 [])) γ = 0 := by
  intro γ hγ
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hγ
  exact ⟨List.mem_map.2 ⟨l, e8_complete l (e8OrdC13_mem l hl) (e8OrdC13_dotU l hl), rfl⟩,
    e8OrdC13_dot1 l hl⟩

theorem e8OrdC13_Csub3 : ∀ γ ∈ e8OrdC13.map (toVec Tag.E8.rank),
    γ ∈ e8Ord.map (toVec Tag.E8.rank) ∧
      dotT (vec3 (τ := .E8) (e8ThreeReps.getD 3 [])) γ = 0 := by
  intro γ hγ
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hγ
  exact ⟨List.mem_map.2 ⟨l, e8_complete l (e8OrdC13_mem l hl) (e8OrdC13_dotU l hl), rfl⟩,
    e8OrdC13_dot3 l hl⟩

theorem e8OrdC13_Cconn : ∀ j : ℕ, j < (e8OrdC13.map (toVec Tag.E8.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e8OrdC13.map (toVec Tag.E8.rank)).getD i default)
      ((e8OrdC13.map (toVec Tag.E8.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e8OrdC13_nodupC : (e8OrdC13.map (toVec Tag.E8.rank)).Nodup := by decide +kernel

theorem e8OrdC13_lengthC : (e8OrdC13.map (toVec Tag.E8.rank)).length = 42 := by decide +kernel

def e8OrdC4 : List (List ℤ) :=
  [[0, 0, 0, -1, -1, -1, -1, -1],
   [0, 0, 0, -1, -1, -1, -1, 0],
   [0, 0, 0, -1, -1, -1, 0, 0],
   [0, 0, 0, -1, -1, 0, 0, 0],
   [0, 0, 0, -1, 0, 0, 0, 0],
   [0, 0, 0, 0, -1, -1, -1, -1],
   [0, 0, 0, 0, 0, -1, -1, -1],
   [0, 0, 0, 0, 0, 0, -1, -1],
   [0, 0, 0, 0, 0, 0, 0, -1],
   [0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 1, 1],
   [0, 0, 0, 0, 0, 1, 1, 1],
   [0, 0, 0, 0, 1, 1, 1, 1],
   [0, 0, 0, 1, 0, 0, 0, 0],
   [0, 0, 0, 1, 1, 0, 0, 0],
   [0, 0, 0, 1, 1, 1, 0, 0],
   [0, 0, 0, 1, 1, 1, 1, 0],
   [0, 0, 0, 1, 1, 1, 1, 1],
   [0, 0, 0, 0, -1, -1, -1, 0],
   [0, 0, 0, 0, 0, -1, -1, 0],
   [0, 0, 0, 0, 0, 0, -1, 0],
   [0, 0, 0, 0, 0, 0, 1, 0],
   [0, 0, 0, 0, 0, 1, 1, 0],
   [0, 0, 0, 0, 1, 1, 1, 0],
   [0, 0, 0, 0, -1, -1, 0, 0],
   [0, 0, 0, 0, 1, 1, 0, 0],
   [0, 0, 0, 0, 0, -1, 0, 0],
   [0, 0, 0, 0, 0, 1, 0, 0],
   [0, 0, 0, 0, -1, 0, 0, 0],
   [0, 0, 0, 0, 1, 0, 0, 0]]

theorem e8OrdC4_mem : ∀ l ∈ e8OrdC4, l ∈ Tag.E8.artifactRoots := by decide +kernel

theorem e8OrdC4_dotU : ∀ l ∈ e8OrdC4, dotT e8U (toVec Tag.E8.rank l) = 0 := by
  decide +kernel

theorem e8OrdC4_dot4 : ∀ l ∈ e8OrdC4,
    dotT (vec3 (τ := .E8) (e8ThreeReps.getD 4 [])) (toVec Tag.E8.rank l) = 0 := by
  decide +kernel

theorem e8OrdC4_Csub4 : ∀ γ ∈ e8OrdC4.map (toVec Tag.E8.rank),
    γ ∈ e8Ord.map (toVec Tag.E8.rank) ∧
      dotT (vec3 (τ := .E8) (e8ThreeReps.getD 4 [])) γ = 0 := by
  intro γ hγ
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hγ
  exact ⟨List.mem_map.2 ⟨l, e8_complete l (e8OrdC4_mem l hl) (e8OrdC4_dotU l hl), rfl⟩,
    e8OrdC4_dot4 l hl⟩

theorem e8OrdC4_Cconn : ∀ j : ℕ, j < (e8OrdC4.map (toVec Tag.E8.rank)).length → 0 < j →
    ∃ i : ℕ, i < j ∧ iform ((e8OrdC4.map (toVec Tag.E8.rank)).getD i default)
      ((e8OrdC4.map (toVec Tag.E8.rank)).getD j default) ≠ 0 := by
  decide +kernel

theorem e8OrdC4_nodupC : (e8OrdC4.map (toVec Tag.E8.rank)).Nodup := by decide +kernel

theorem e8OrdC4_lengthC : (e8OrdC4.map (toVec Tag.E8.rank)).length = 30 := by decide +kernel

theorem e8_Csub2 : ∀ γ ∈ e8Ord.map (toVec Tag.E8.rank),
    γ ∈ e8Ord.map (toVec Tag.E8.rank) ∧
      dotT (vec3 (τ := .E8) (e8ThreeReps.getD 2 [])) γ = 0 := by
  intro γ hγ
  refine ⟨hγ, ?_⟩
  have hv : vec3 (τ := .E8) (e8ThreeReps.getD 2 []) = e8U := by
    funext i
    fin_cases i <;> decide +kernel
  rw [hv]
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hγ
  exact (e8_sound l hl).2

theorem e8_num42 : ∀ m : ℕ, 42 ≤ m * (m - 1) → 4 ≤ m ∧ 8 + 1 < 2 * m := by
  intro m h
  have h4 : 4 ≤ m := by
    by_contra hm
    interval_cases m <;> omega
  refine ⟨h4, ?_⟩
  by_contra hm
  have hm4 : m ≤ 4 := by omega
  interval_cases m <;> omega

theorem e8_num30 : ∀ m : ℕ, 30 ≤ m * (m - 1) → 4 ≤ m ∧ 8 + 1 < 2 * m := by
  intro m h
  have h4 : 4 ≤ m := by
    by_contra hm
    interval_cases m <;> omega
  refine ⟨h4, ?_⟩
  by_contra hm
  have hm4 : m ≤ 4 := by omega
  interval_cases m <;> omega

theorem e8_num72 : ∀ m : ℕ, 72 ≤ m * (m - 1) → 4 ≤ m ∧ 8 + 1 < 2 * m := by
  intro m h
  have h4 : 4 ≤ m := by
    by_contra hm
    interval_cases m <;> omega
  refine ⟨h4, ?_⟩
  by_contra hm
  have hm4 : m ≤ 4 := by omega
  interval_cases m <;> omega


section Good


theorem e7_good_e1 :
    ExcGood Tag.E7 e7U2 (vec3 (τ := .E7) (e7ThreeReps.getD 1 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 : ∀ γ, (IsRoot Tag.E7 γ ∧ dotT e7U2 γ = 0) ↔
      γ ∈ e7Ord2.map (toVec Tag.E7.rank) :=
    hord_of_checks e7U2 e7Ord2 e7_sound2 e7_complete2
  have h2 : (e7OrdC13.map (toVec Tag.E7.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inl rfl) S hq2 hAlg hρ hζ hζ' hTor e7U2
    (vec3 (τ := .E7) (e7ThreeReps.getD 1 []))
    (e7Ord2.map (toVec Tag.E7.rank)) (e7OrdC13.map (toVec Tag.E7.rank)) 6 30
    h1 e7_ordconn2 e7_nodup2 e7_length2 (by norm_num) e7_rank2 h2 e7OrdC13_Csub1
    e7OrdC13_Cconn e7OrdC13_nodupC e7OrdC13_lengthC e7_num30

theorem e7_good_e2 :
    ExcGood Tag.E7 e7U2 (vec3 (τ := .E7) (e7ThreeReps.getD 2 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 : ∀ γ, (IsRoot Tag.E7 γ ∧ dotT e7U2 γ = 0) ↔
      γ ∈ e7Ord2.map (toVec Tag.E7.rank) :=
    hord_of_checks e7U2 e7Ord2 e7_sound2 e7_complete2
  have h2 : (e7Ord2.map (toVec Tag.E7.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inl rfl) S hq2 hAlg hρ hζ hζ' hTor e7U2
    (vec3 (τ := .E7) (e7ThreeReps.getD 2 []))
    (e7Ord2.map (toVec Tag.E7.rank)) (e7Ord2.map (toVec Tag.E7.rank)) 6 42
    h1 e7_ordconn2 e7_nodup2 e7_length2 (by norm_num) e7_rank2 h2 e7_Csub2
    e7_ordconn2 e7_nodup2 e7_length2 e7_num42

theorem e7_good_two_e1_e2 :
    ExcGood Tag.E7 e7U2 (vec3 (τ := .E7) (e7ThreeReps.getD 3 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 : ∀ γ, (IsRoot Tag.E7 γ ∧ dotT e7U2 γ = 0) ↔
      γ ∈ e7Ord2.map (toVec Tag.E7.rank) :=
    hord_of_checks e7U2 e7Ord2 e7_sound2 e7_complete2
  have h2 : (e7OrdC13.map (toVec Tag.E7.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inl rfl) S hq2 hAlg hρ hζ hζ' hTor e7U2
    (vec3 (τ := .E7) (e7ThreeReps.getD 3 []))
    (e7Ord2.map (toVec Tag.E7.rank)) (e7OrdC13.map (toVec Tag.E7.rank)) 6 30
    h1 e7_ordconn2 e7_nodup2 e7_length2 (by norm_num) e7_rank2 h2 e7OrdC13_Csub3
    e7OrdC13_Cconn e7OrdC13_nodupC e7OrdC13_lengthC e7_num30

theorem e7_good_e3 :
    ExcGood Tag.E7 e7U2 (vec3 (τ := .E7) (e7ThreeReps.getD 4 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 : ∀ γ, (IsRoot Tag.E7 γ ∧ dotT e7U2 γ = 0) ↔
      γ ∈ e7Ord2.map (toVec Tag.E7.rank) :=
    hord_of_checks e7U2 e7Ord2 e7_sound2 e7_complete2
  have h2 : (e7OrdC45.map (toVec Tag.E7.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inl rfl) S hq2 hAlg hρ hζ hζ' hTor e7U2
    (vec3 (τ := .E7) (e7ThreeReps.getD 4 []))
    (e7Ord2.map (toVec Tag.E7.rank)) (e7OrdC45.map (toVec Tag.E7.rank)) 6 20
    h1 e7_ordconn2 e7_nodup2 e7_length2 (by norm_num) e7_rank2 h2 e7OrdC45_Csub4
    e7OrdC45_Cconn e7OrdC45_nodupC e7OrdC45_lengthC e7_num20

theorem e7_good_e2_e3 :
    ExcGood Tag.E7 e7U2 (vec3 (τ := .E7) (e7ThreeReps.getD 5 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 : ∀ γ, (IsRoot Tag.E7 γ ∧ dotT e7U2 γ = 0) ↔
      γ ∈ e7Ord2.map (toVec Tag.E7.rank) :=
    hord_of_checks e7U2 e7Ord2 e7_sound2 e7_complete2
  have h2 : (e7OrdC45.map (toVec Tag.E7.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inl rfl) S hq2 hAlg hρ hζ hζ' hTor e7U2
    (vec3 (τ := .E7) (e7ThreeReps.getD 5 []))
    (e7Ord2.map (toVec Tag.E7.rank)) (e7OrdC45.map (toVec Tag.E7.rank)) 6 20
    h1 e7_ordconn2 e7_nodup2 e7_length2 (by norm_num) e7_rank2 h2 e7OrdC45_Csub5
    e7OrdC45_Cconn e7OrdC45_nodupC e7OrdC45_lengthC e7_num20

theorem e7_reps_good :
    ∀ ρ < e7ThreeReps.length, vec3 (τ := .E7) (e7ThreeReps.getD ρ []) ≠ 0 →
      ∃ u : Fin 7 → ZMod 3, ExcGood Tag.E7 u
        (vec3 (τ := .E7) (e7ThreeReps.getD ρ [])) := by
  intro ρ hρ hne
  have hlen : e7ThreeReps.length = 6 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by decide +kernel) hne
  · exact ⟨e7U2, e7_good_e1⟩
  · exact ⟨e7U2, e7_good_e2⟩
  · exact ⟨e7U2, e7_good_two_e1_e2⟩
  · exact ⟨e7U2, e7_good_e3⟩
  · exact ⟨e7U2, e7_good_e2_e3⟩

theorem e8_good_e1 :
    ExcGood Tag.E8 e8U (vec3 (τ := .E8) (e8ThreeReps.getD 1 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 := hord_of_checks (τ := Tag.E8) e8U e8Ord e8_sound e8_complete
  have h2 : (e8OrdC13.map (toVec Tag.E8.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inr rfl) S hq2 hAlg hρ hζ hζ' hTor e8U
    (vec3 (τ := .E8) (e8ThreeReps.getD 1 []))
    (e8Ord.map (toVec Tag.E8.rank)) (e8OrdC13.map (toVec Tag.E8.rank)) 8 42
    h1 e8_ordconn e8_nodup e8_length (by norm_num) e8_rank h2 e8OrdC13_Csub1
    e8OrdC13_Cconn e8OrdC13_nodupC e8OrdC13_lengthC e8_num42

theorem e8_good_e2 :
    ExcGood Tag.E8 e8U (vec3 (τ := .E8) (e8ThreeReps.getD 2 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 := hord_of_checks (τ := Tag.E8) e8U e8Ord e8_sound e8_complete
  have h2 : (e8Ord.map (toVec Tag.E8.rank)) ≠ [] := by
    intro h
    have := e8_length
    rw [h] at this
    simp at this
  exact exc_component_of_data (Or.inr rfl) S hq2 hAlg hρ hζ hζ' hTor e8U
    (vec3 (τ := .E8) (e8ThreeReps.getD 2 []))
    (e8Ord.map (toVec Tag.E8.rank)) (e8Ord.map (toVec Tag.E8.rank)) 8 72
    h1 e8_ordconn e8_nodup e8_length (by norm_num) e8_rank h2 e8_Csub2
    e8_ordconn e8_nodup e8_length e8_num72

theorem e8_good_two_e1_e2 :
    ExcGood Tag.E8 e8U (vec3 (τ := .E8) (e8ThreeReps.getD 3 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 := hord_of_checks (τ := Tag.E8) e8U e8Ord e8_sound e8_complete
  have h2 : (e8OrdC13.map (toVec Tag.E8.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inr rfl) S hq2 hAlg hρ hζ hζ' hTor e8U
    (vec3 (τ := .E8) (e8ThreeReps.getD 3 []))
    (e8Ord.map (toVec Tag.E8.rank)) (e8OrdC13.map (toVec Tag.E8.rank)) 8 42
    h1 e8_ordconn e8_nodup e8_length (by norm_num) e8_rank h2 e8OrdC13_Csub3
    e8OrdC13_Cconn e8OrdC13_nodupC e8OrdC13_lengthC e8_num42

theorem e8_good_e2_e3 :
    ExcGood Tag.E8 e8U (vec3 (τ := .E8) (e8ThreeReps.getD 4 [])) := by
  intro L _ _ S hq2 hAlg hρ ζ hζ hζ' hTor
  have h1 := hord_of_checks (τ := Tag.E8) e8U e8Ord e8_sound e8_complete
  have h2 : (e8OrdC4.map (toVec Tag.E8.rank)) ≠ [] := by decide +kernel
  exact exc_component_of_data (Or.inr rfl) S hq2 hAlg hρ hζ hζ' hTor e8U
    (vec3 (τ := .E8) (e8ThreeReps.getD 4 []))
    (e8Ord.map (toVec Tag.E8.rank)) (e8OrdC4.map (toVec Tag.E8.rank)) 8 30
    h1 e8_ordconn e8_nodup e8_length (by norm_num) e8_rank h2 e8OrdC4_Csub4
    e8OrdC4_Cconn e8OrdC4_nodupC e8OrdC4_lengthC e8_num30

theorem e8_reps_good :
    ∀ ρ < e8ThreeReps.length, vec3 (τ := .E8) (e8ThreeReps.getD ρ []) ≠ 0 →
      ∃ u : Fin 8 → ZMod 3, ExcGood Tag.E8 u
        (vec3 (τ := .E8) (e8ThreeReps.getD ρ [])) := by
  intro ρ hρ hne
  have hlen : e8ThreeReps.length = 5 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by decide +kernel) hne
  · exact ⟨e8U, e8_good_e1⟩
  · exact ⟨e8U, e8_good_e2⟩
  · exact ⟨e8U, e8_good_two_e1_e2⟩
  · exact ⟨e8U, e8_good_e2_e3⟩

end Good

end CFSG.LocalAnalysis.GLTheoremA.S262

end
