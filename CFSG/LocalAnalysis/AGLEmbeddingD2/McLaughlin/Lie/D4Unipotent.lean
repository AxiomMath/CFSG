module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Lie.D4Levi

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem
open scoped commutatorElement

variable {F : Type} [Field F]

noncomputable abbrev simpleUnipotent (F : Type) [Field F] : Subgroup (spinGroup (quadPlus 4 F)) :=
  ⨆ i : Fin 4, (plusDatum 4 F three_le_four).rootGroup (Pi.single i 1)

theorem range_longRoot_le_of_comm {V : Subgroup (spinGroup (quadPlus 4 F))} {i j k : Fin 4}
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (s t u : Bool)
    (h1 : ((plusFrame 4 F three_le_four).longRoot hij s t).range ≤ V)
    (h2 : ((plusFrame 4 F three_le_four).longRoot hjk (!t) u).range ≤ V) :
    ((plusFrame 4 F three_le_four).longRoot hik s u).range ≤ V := by
  rintro _ ⟨c, rfl⟩
  have h := (plusFrame 4 F three_le_four).commutator_longRoot_longRoot hij hjk hik s t u
    (Multiplicative.toAdd c) 1
  rw [mul_one, ofAdd_toAdd] at h
  rw [← h, commutatorElement_def]
  exact V.mul_mem (V.mul_mem (V.mul_mem (h1 ⟨_, rfl⟩) (h2 ⟨_, rfl⟩)) (V.inv_mem (h1 ⟨_, rfl⟩)))
    (V.inv_mem (h2 ⟨_, rfl⟩))

theorem range_le_simple {i j : Fin 4} (hij : i ≠ j) (s t : Bool) (k : Fin 4)
    (h : toStdD 4 (Pi.single k 1) = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ((plusFrame 4 F three_le_four).longRoot hij s t).range ≤ simpleUnipotent F := by
  rw [← plusRootGroup_eq three_le_four hij s t h]
  exact le_iSup (fun i : Fin 4 => (plusDatum 4 F three_le_four).rootGroup (Pi.single i 1)) k

section Roots

theorem r01 : ((plusFrame 4 F three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 1) true false).range ≤ simpleUnipotent F :=
  range_le_simple _ _ _ 0 (by decide)

theorem r12 : ((plusFrame 4 F three_le_four).longRoot (by decide : (1 : Fin 4) ≠ 2) true false).range ≤ simpleUnipotent F :=
  range_le_simple _ _ _ 1 (by decide)

theorem r23 : ((plusFrame 4 F three_le_four).longRoot (by decide : (2 : Fin 4) ≠ 3) true false).range ≤ simpleUnipotent F :=
  range_le_simple _ _ _ 2 (by decide)

theorem r23p : ((plusFrame 4 F three_le_four).longRoot (by decide : (2 : Fin 4) ≠ 3) true true).range ≤ simpleUnipotent F :=
  range_le_simple _ _ _ 3 (by decide)

theorem r02 : ((plusFrame 4 F three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 2) true false).range ≤ simpleUnipotent F :=
  range_longRoot_le_of_comm (by decide : (0 : Fin 4) ≠ 1) (by decide) _ true false false r01 r12

theorem r13 : ((plusFrame 4 F three_le_four).longRoot (by decide : (1 : Fin 4) ≠ 3) true false).range ≤ simpleUnipotent F :=
  range_longRoot_le_of_comm (by decide : (1 : Fin 4) ≠ 2) (by decide) _ true false false r12 r23

theorem r13p : ((plusFrame 4 F three_le_four).longRoot (by decide : (1 : Fin 4) ≠ 3) true true).range ≤ simpleUnipotent F :=
  range_longRoot_le_of_comm (by decide : (1 : Fin 4) ≠ 2) (by decide) _ true false true r12 r23p

theorem r03 : ((plusFrame 4 F three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 3) true false).range ≤ simpleUnipotent F :=
  range_longRoot_le_of_comm (by decide : (0 : Fin 4) ≠ 1) (by decide) _ true false false r01 r13

theorem r03p : ((plusFrame 4 F three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 3) true true).range ≤ simpleUnipotent F :=
  range_longRoot_le_of_comm (by decide : (0 : Fin 4) ≠ 1) (by decide) _ true false true r01 r13p

theorem r12p : ((plusFrame 4 F three_le_four).longRoot (by decide : (1 : Fin 4) ≠ 2) true true).range ≤ simpleUnipotent F := by
  have h32 : ((plusFrame 4 F three_le_four).longRoot (by decide : (3 : Fin 4) ≠ 2) true true).range ≤ simpleUnipotent F := by
    rw [(plusFrame 4 F three_le_four).range_longRoot_swap (by decide : (2 : Fin 4) ≠ 3)]
    exact r23p
  exact range_longRoot_le_of_comm (by decide : (1 : Fin 4) ≠ 3) (by decide) _ true false true r13
    h32

theorem r02p : ((plusFrame 4 F three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 2) true true).range ≤ simpleUnipotent F :=
  range_longRoot_le_of_comm (by decide : (0 : Fin 4) ≠ 1) (by decide) _ true false true r01 r12p

theorem r01p : ((plusFrame 4 F three_le_four).longRoot (by decide : (0 : Fin 4) ≠ 1) true true).range ≤ simpleUnipotent F := by
  have h21 : ((plusFrame 4 F three_le_four).longRoot (by decide : (2 : Fin 4) ≠ 1) true true).range ≤ simpleUnipotent F := by
    rw [(plusFrame 4 F three_le_four).range_longRoot_swap (by decide : (1 : Fin 4) ≠ 2)]
    exact r12p
  exact range_longRoot_le_of_comm (by decide : (0 : Fin 4) ≠ 2) (by decide) _ true false true r02
    h21

theorem range_le_simple_of_lt {i j : Fin 4} (hij : i ≠ j) (hlt : i < j) (s t : Bool)
    (hpos : 0 < 3 * (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 0 +
      2 * (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 1 +
      (Pi.single i (boolSign s) + Pi.single j (boolSign t) : Fin 4 → ℤ) 2) :
    ((plusFrame 4 F three_le_four).longRoot hij s t).range ≤ simpleUnipotent F := by
  fin_cases i <;> fin_cases j <;> simp at hlt <;> cases s <;> cases t <;>
    simp [boolSign] at hpos
  all_goals first
    | exact r01 | exact r12 | exact r23 | exact r23p | exact r02 | exact r13 | exact r13p
    | exact r03 | exact r03p | exact r12p | exact r02p | exact r01p

end Roots

theorem ht_eq_toStdD (γ : Fin 4 → ℤ) :
    ht γ = 3 * toStdD 4 γ 0 + 2 * toStdD 4 γ 1 + toStdD 4 γ 2 := by
  simp only [ht, toStdD, Fin.sum_univ_four]
  norm_num
  ring

theorem posUnipotent_plusDatum_four :
    posUnipotent (plusDatum 4 F three_le_four) =
      ⨆ i : Fin 4, (plusDatum 4 F three_le_four).rootGroup (Pi.single i 1) := by
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, hpos⟩ := hγ
    change (plusFrame 4 F three_le_four).longRootGroup (toStdD 4 γ) ≤ simpleUnipotent F
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun s => iSup_le fun t =>
      iSup_le fun h => ?_
    have hpos' : 0 < 3 * toStdD 4 γ 0 + 2 * toStdD 4 γ 1 + toStdD 4 γ 2 := by
      rw [← ht_eq_toStdD γ]
      exact hpos
    rw [h] at hpos'
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact range_le_simple_of_lt hij hlt s t hpos'
    · rw [← (plusFrame 4 F three_le_four).range_longRoot_swap hij s t]
      refine range_le_simple_of_lt hij.symm hlt t s ?_
      have e : (Pi.single j (boolSign t) + Pi.single i (boolSign s) : Fin 4 → ℤ) =
          Pi.single i (boolSign s) + Pi.single j (boolSign t) := add_comm _ _
      rw [e]
      exact hpos'
  · exact iSup_le fun i => rootGroup_le_posUnipotent
      ((RootSystem.ofCartan (plusDatum 4 F three_le_four).isFiniteType
        (plusDatum 4 F three_le_four).divisible).single_mem i)
      (ht_single_pos (D := plusDatum 4 F three_le_four) i)

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
