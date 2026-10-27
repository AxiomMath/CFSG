module

public import Certificates.Certificate131300

public section

namespace CFSG.HardMathSupport.Foote.E27.Fi24

open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27.OrbitF3
open scoped Matrix

@[expose] def K : Subgroup (GL (Fin 10) (ZMod 3)) := Subgroup.closure {g | g ∈ [XU, YU]}

theorem XU_mem : XU ∈ K := Subgroup.subset_closure (by simp)

theorem YU_mem : YU ∈ K := Subgroup.subset_closure (by simp)

theorem coe_XU : (XU : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 XRows := rfl

theorem coe_YU : (YU : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 YRows := rfl

theorem coe_XU_inv : ((XU⁻¹ : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
    rowsMat 3 10 XiRows := rfl

theorem coe_YU_inv : ((YU⁻¹ : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
    rowsMat 3 10 YiRows := rfl

theorem ncard_orbit_v :
    (MulAction.orbit K (⟨rowsVec 3 10 base⟩ : RowVD 10)).ncard = 12672 :=
  Certificates.certificate131300

@[expose] def letterU : ℤ → GL (Fin 10) (ZMod 3)
  | 1 => XU
  | 2 => YU
  | -1 => XU⁻¹
  | _ => YU⁻¹

@[expose] def letterRows : ℤ → List (List ℕ)
  | 1 => XRows
  | 2 => YRows
  | -1 => XiRows
  | _ => YiRows

theorem coe_letterU (l : ℤ) :
    ((letterU l : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
      rowsMat 3 10 (letterRows l) := by
  unfold letterU letterRows
  split <;> rfl

theorem letterU_mem (l : ℤ) : letterU l ∈ K := by
  unfold letterU
  split
  · exact XU_mem
  · exact YU_mem
  · exact inv_mem XU_mem
  · exact inv_mem YU_mem

@[expose] def wordU (w : List ℤ) : GL (Fin 10) (ZMod 3) := (w.map letterU).prod

@[expose] def wordRowsF (w : List ℤ) : List (List ℕ) := (w.map letterRows).foldl (lmulD 10) (lidD 10)

theorem coe_wordU (w : List ℤ) :
    ((wordU w : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
      rowsMat 3 10 (wordRowsF w) := by
  refine coe_prod_eq_rowsMat_one _ _ ?_
  induction w with
  | nil => exact List.Forall₂.nil
  | cons l w ih => exact List.Forall₂.cons (coe_letterU l) ih

theorem wordU_mem (w : List ℤ) : wordU w ∈ K :=
  list_prod_mem fun g hg => by
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp hg
    exact letterU_mem l

@[expose] def wa : List ℤ :=
  [-1, 2, -1, -2, 1, 2, 1, 1, 2, 2, -1, 2, -1, -2, -1, -1, 2, -1, 2, 1, 2, 2, 1, 2, 1, -2, 1]

@[expose] def wb : List ℤ :=
  [-1, -1, 2, 1, 2, -1, -2, 1, 2, 1, -2, -2, -1, -1, 2, -1, 2, -1, -2, -1, -2, -2, -1, -2, 1, -2,
    -2, -1, -1, -1, 2, 2, 2, 1, -2, -1, 2, 1, -2, -2, -1, -2]

@[expose] def wc : List ℤ :=
  [-1, -1, 2, 1, 2, -1, -2, 1, 2, 1, -2, -2, -1, -1, 2, 2, -1, -1, -1, -2, -1, 2, 1, 2, 1, 1, 2, 2,
    -1, 2, 1, 2, 1, -2, 1, 2, 1, 1, 1, 2, 1, -2, -1]

@[expose] def u₁ : List ℕ := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0]

@[expose] def u₂ : List ℕ := [0, 0, 2, 0, 0, 2, 1, 0, 0, 0]

@[expose] def ARows : List (List ℕ) :=
  [[1, 2, 2, 1, 2, 0, 2, 0, 1, 1], [1, 1, 2, 1, 2, 1, 0, 1, 0, 1],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 2, 0, 2, 0, 1, 2, 2, 1, 1],
    [2, 1, 0, 2, 1, 1, 1, 0, 0, 2], [2, 0, 0, 0, 0, 0, 0, 2, 1, 0],
    [2, 0, 0, 0, 0, 2, 1, 2, 1, 0], [1, 1, 0, 2, 0, 0, 1, 0, 1, 2],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [2, 2, 0, 1, 0, 0, 2, 1, 2, 2]]

@[expose] def BRows : List (List ℕ) :=
  [[1, 1, 0, 1, 1, 2, 1, 1, 2, 0], [0, 2, 0, 0, 2, 1, 2, 1, 1, 2],
    [0, 0, 0, 0, 0, 2, 1, 0, 2, 0], [2, 0, 0, 2, 1, 1, 0, 0, 1, 0],
    [0, 1, 1, 1, 0, 0, 1, 0, 1, 0], [2, 1, 1, 2, 1, 2, 2, 2, 0, 0],
    [2, 1, 0, 2, 1, 0, 1, 2, 2, 0], [2, 2, 2, 1, 1, 2, 1, 1, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [1, 1, 2, 2, 0, 2, 2, 2, 1, 0]]

@[expose] def CRows : List (List ℕ) :=
  [[0, 2, 1, 1, 2, 1, 0, 0, 1, 0], [1, 2, 1, 2, 2, 1, 2, 1, 2, 1],
    [0, 0, 2, 1, 2, 2, 1, 0, 2, 1], [0, 0, 0, 0, 2, 2, 2, 0, 1, 1],
    [0, 0, 0, 2, 0, 2, 2, 0, 0, 1], [0, 0, 1, 2, 2, 1, 1, 1, 0, 0],
    [0, 0, 1, 2, 0, 0, 0, 0, 1, 0], [0, 0, 1, 1, 2, 2, 1, 1, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 2, 2, 0, 1, 1, 1, 2, 0]]

theorem wordRowsF_wa : wordRowsF wa = ARows := by decide +kernel

theorem wordRowsF_wb : wordRowsF wb = BRows := by decide +kernel

theorem wordRowsF_wc : wordRowsF wc = CRows := by decide +kernel

theorem rows_facts :
    lvecMul 3 10 base ARows = base ∧ lvecMul 3 10 base BRows = base ∧
    lvecMul 3 10 base CRows = base ∧ lpowD 10 ARows 3 = lidD 10 ∧ lpowD 10 BRows 3 = lidD 10 ∧
    lpowD 10 CRows 3 = lidD 10 ∧ rowsMat 3 10 ARows ≠ 1 ∧
    lmulD 10 ARows BRows = lmulD 10 BRows ARows ∧ lmulD 10 ARows CRows = lmulD 10 CRows ARows ∧
    lmulD 10 BRows CRows = lmulD 10 CRows BRows ∧ lvecMul 3 10 u₁ ARows = u₁ ∧
    lvecMul 3 10 u₁ BRows ≠ u₁ ∧ lvecMul 3 10 u₂ ARows = u₂ ∧ lvecMul 3 10 u₂ BRows = u₂ ∧
    lvecMul 3 10 u₂ CRows ≠ u₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem coe_a : ((wordU wa : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
    rowsMat 3 10 ARows := by rw [coe_wordU, wordRowsF_wa]

theorem coe_b : ((wordU wb : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
    rowsMat 3 10 BRows := by rw [coe_wordU, wordRowsF_wb]

theorem coe_c : ((wordU wc : GL (Fin 10) (ZMod 3)) : Matrix (Fin 10) (Fin 10) (ZMod 3)) =
    rowsMat 3 10 CRows := by rw [coe_wordU, wordRowsF_wc]

theorem pow_three_of_rows {s : GL (Fin 10) (ZMod 3)} {Rw : List (List ℕ)}
    (hc : (s : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 Rw) (h : lpowD 10 Rw 3 = lidD 10) :
    s ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hc, ← rowsMat_lpowD, h, rowsMat_lidD, Units.val_one]

theorem comm_of_rows {s t : GL (Fin 10) (ZMod 3)} {Rs Rt : List (List ℕ)}
    (hs : (s : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 Rs)
    (ht : (t : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 Rt) (hRs : Rs.length = 10)
    (hRt : Rt.length = 10) (h : lmulD 10 Rs Rt = lmulD 10 Rt Rs) : s * t = t * s := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hs, ht, ← rowsMat_lmulD hRs, ← rowsMat_lmulD hRt, h]

theorem fix_of_rows {s : GL (Fin 10) (ZMod 3)} {Rs : List (List ℕ)} {u : List ℕ}
    (hs : (s : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 Rs) (h : lvecMul 3 10 u Rs = u) :
    rowsVec 3 10 u ᵥ* (s : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsVec 3 10 u := by
  rw [hs, ← rowsVec_lvecMul, h]

theorem not_fix_of_rows {s : GL (Fin 10) (ZMod 3)} {Rs : List (List ℕ)} {u : List ℕ}
    (hs : (s : Matrix (Fin 10) (Fin 10) (ZMod 3)) = rowsMat 3 10 Rs) (hu : ValidD 10 u)
    (h : lvecMul 3 10 u Rs ≠ u) :
    rowsVec 3 10 u ᵥ* (s : Matrix (Fin 10) (Fin 10) (ZMod 3)) ≠ rowsVec 3 10 u := by
  rw [hs, ← rowsVec_lvecMul]
  exact fun e => h (rowsVec_injD (validD_lvecMul u Rs) hu e)

theorem three_pow_five_dvd_card_K : 3 ^ 5 ∣ Nat.card K := by
  obtain ⟨hfa, hfb, hfc, ha3, hb3, hc3, ha1, hab, hac, hbc, h1a, h1b, h2a, h2b, h2c⟩ := rows_facts
  have hcard := card_eq_mul_card_stabilizer K (⟨rowsVec 3 10 base⟩ : RowVD 10)
  rw [ncard_orbit_v] at hcard
  have hu₁ : ValidD 10 u₁ := ⟨rfl, by decide⟩
  have hu₂ : ValidD 10 u₂ := ⟨rfl, by decide⟩
  have hl : ARows.length = 10 ∧ BRows.length = 10 ∧ CRows.length = 10 := ⟨rfl, rfl, rfl⟩
  have h27 := twentySeven_dvd_card_stabilizer (K := K) (w := ⟨rowsVec 3 10 base⟩)
    (wordU_mem wa) (wordU_mem wb) (wordU_mem wc) (fix_of_rows coe_a hfa)
    (fix_of_rows coe_b hfb) (fix_of_rows coe_c hfc)
    (pow_three_of_rows coe_a ha3) (pow_three_of_rows coe_b hb3) (pow_three_of_rows coe_c hc3)
    (fun h => ha1 (by rw [← coe_a, h, Units.val_one]))
    (comm_of_rows coe_a coe_b hl.1 hl.2.1 hab) (comm_of_rows coe_a coe_c hl.1 hl.2.2 hac)
    (comm_of_rows coe_b coe_c hl.2.1 hl.2.2 hbc) (rowsVec 3 10 u₁) (rowsVec 3 10 u₂)
    (fix_of_rows coe_a h1a) (not_fix_of_rows coe_b hu₁ h1b)
    (fix_of_rows coe_a h2a) (fix_of_rows coe_b h2b) (not_fix_of_rows coe_c hu₂ h2c)
  rw [hcard, show (3 : ℕ) ^ 5 = 27 * 9 by norm_num, show (12672 : ℕ) = 9 * 1408 by norm_num,
    ← mul_assoc]
  exact Dvd.dvd.mul_right (Nat.mul_dvd_mul h27 (dvd_refl 9)) 1408

end CFSG.HardMathSupport.Foote.E27.Fi24
