module

public import CFSG.HardMathSupport.Foote.E27.OrbitF3

public section

namespace CFSG.HardMathSupport.Foote.E27.Fi23

open CFSG.Monster.B.Pinned CFSG.HardMathSupport.Foote.E27.OrbitF3
open scoped Matrix

@[expose] def XRows : List (List ℕ) :=
  [[1, 0, 0, 0, 2, 0, 0, 1], [0, 1, 0, 0, 0, 1, 2, 2], [0, 0, 1, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 1, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def YRows : List (List ℕ) :=
  [[2, 2, 1, 0, 1, 2, 1, 2], [1, 0, 2, 1, 0, 0, 1, 1], [2, 1, 1, 2, 1, 1, 2, 1],
    [2, 1, 2, 1, 1, 1, 0, 0], [0, 2, 0, 1, 2, 0, 0, 0], [1, 0, 2, 0, 2, 0, 1, 2],
    [1, 1, 2, 0, 1, 1, 2, 1], [1, 2, 2, 1, 0, 1, 2, 1]]

@[expose] def XiRows : List (List ℕ) :=
  [[1, 0, 0, 0, 1, 0, 0, 2], [0, 1, 0, 0, 0, 2, 1, 1], [0, 0, 1, 0, 0, 0, 0, 2],
    [0, 0, 0, 1, 2, 2, 2, 0], [0, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 0, 1]]

@[expose] def YiRows : List (List ℕ) :=
  [[1, 0, 1, 1, 0, 2, 2, 0], [0, 0, 0, 0, 1, 0, 1, 2], [2, 0, 0, 1, 1, 2, 0, 1],
    [2, 0, 0, 0, 2, 0, 0, 2], [2, 0, 0, 0, 0, 0, 2, 0], [2, 0, 1, 0, 1, 1, 2, 0],
    [1, 2, 2, 0, 0, 2, 2, 0], [1, 2, 0, 0, 2, 1, 2, 2]]

theorem X_mul_inv : rowsMat 3 8 XRows * rowsMat 3 8 XiRows = 1 := by decide +kernel
theorem X_inv_mul : rowsMat 3 8 XiRows * rowsMat 3 8 XRows = 1 := by decide +kernel
theorem Y_mul_inv : rowsMat 3 8 YRows * rowsMat 3 8 YiRows = 1 := by decide +kernel
theorem Y_inv_mul : rowsMat 3 8 YiRows * rowsMat 3 8 YRows = 1 := by decide +kernel

@[expose] def XU : GL (Fin 8) (ZMod 3) :=
  ⟨rowsMat 3 8 XRows, rowsMat 3 8 XiRows, X_mul_inv, X_inv_mul⟩

@[expose] def YU : GL (Fin 8) (ZMod 3) :=
  ⟨rowsMat 3 8 YRows, rowsMat 3 8 YiRows, Y_mul_inv, Y_inv_mul⟩

@[expose] def K : Subgroup (GL (Fin 8) (ZMod 3)) := Subgroup.closure {g | g ∈ [XU, YU]}

theorem XU_mem : XU ∈ K := Subgroup.subset_closure (by simp)

theorem YU_mem : YU ∈ K := Subgroup.subset_closure (by simp)

@[expose] def base : List ℕ := [0, 0, 0, 0, 0, 0, 0, 1]

theorem orbit_facts : ((bfsD 8 [XRows, YRows] 20 (1 <<< lcode base) [base] []).length == 288 &&
    orbitOKD 8 [XRows, YRows] (bfsD 8 [XRows, YRows] 20 (1 <<< lcode base) [base] [])) =
      true := by
  decide +kernel

theorem ncard_orbit_v : (MulAction.orbit K (⟨rowsVec 3 8 base⟩ : RowVD 8)).ncard = 288 := by
  have h := orbit_facts
  rw [Bool.and_eq_true, beq_iff_eq] at h
  rw [← h.1]
  refine ncard_orbit_of_bfs (gens := [XU, YU]) (rows := [XRows, YRows]) rfl ?_ ⟨rfl, by decide⟩ 20
    h.2
  intro i h₁ h₂
  have : i = 0 ∨ i = 1 := by simp at h₁; omega
  rcases this with rfl | rfl <;> rfl

@[expose] def sU : GL (Fin 8) (ZMod 3) :=
  [YU, YU, XU, YU⁻¹, YU⁻¹, YU⁻¹, XU, YU⁻¹, YU⁻¹, XU, YU].prod

@[expose] def sRowsF : List (List ℕ) :=
  [YRows, YRows, XRows, YiRows, YiRows, YiRows, XRows, YiRows, YiRows, XRows, YRows].foldl
    (lmulD 8) (lidD 8)

theorem coe_sU : (sU : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 sRowsF :=
  coe_prod_eq_rowsMat_one _ _ (by simp only [List.forall₂_cons, List.Forall₂.nil, and_true]; exact
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem sU_mem : sU ∈ K := by
  unfold sU
  apply list_prod_mem
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact XU_mem | exact YU_mem | exact inv_mem YU_mem

theorem rows_facts :
    lvecMul 3 8 base XRows = base ∧ lvecMul 3 8 base sRowsF = base ∧
    lpowD 8 XRows 3 = lidD 8 ∧ lpowD 8 sRowsF 3 = lidD 8 ∧
    lmulD 8 XRows sRowsF = lmulD 8 sRowsF XRows ∧ rowsMat 3 8 XRows ≠ 1 ∧
    rowsMat 3 8 sRowsF ≠ 1 ∧ rowsMat 3 8 sRowsF ≠ rowsMat 3 8 XRows ∧
    rowsMat 3 8 sRowsF ≠ rowsMat 3 8 (lpowD 8 XRows 2) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem pow_three_of_rows {s : GL (Fin 8) (ZMod 3)} {Rw : List (List ℕ)}
    (hc : (s : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 Rw) (h : lpowD 8 Rw 3 = lidD 8) :
    s ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hc, ← rowsMat_lpowD, h, rowsMat_lidD, Units.val_one]

theorem sRowsF_length : sRowsF.length = 8 := by decide +kernel

theorem coe_XU : (XU : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 XRows := rfl

theorem three_pow_four_dvd_card_K : 3 ^ 4 ∣ Nat.card K := by
  obtain ⟨hfX, hfs, hX3, hs3, hcomm, hX1, hs1, hsX, hsX2⟩ := rows_facts
  have hcard := card_eq_mul_card_stabilizer K (⟨rowsVec 3 8 base⟩ : RowVD 8)
  rw [ncard_orbit_v] at hcard
  have hfix : ∀ (g : GL (Fin 8) (ZMod 3)) (Rw : List (List ℕ)),
      (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsMat 3 8 Rw → lvecMul 3 8 base Rw = base →
      rowsVec 3 8 base ᵥ* (g : Matrix (Fin 8) (Fin 8) (ZMod 3)) = rowsVec 3 8 base := by
    intro g Rw hg h
    rw [hg, ← rowsVec_lvecMul, h]
  have h9 := nine_dvd_card_stabilizer (K := K) (w := ⟨rowsVec 3 8 base⟩) XU_mem sU_mem
    (hfix XU XRows coe_XU hfX) (hfix sU sRowsF coe_sU hfs) (pow_three_of_rows coe_XU hX3)
    (pow_three_of_rows coe_sU hs3)
    (fun h => hX1 (by rw [← coe_XU, h, Units.val_one]))
    (by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_sU, coe_XU,
        ← rowsMat_lmulD (d := 8) (A := XRows) rfl,
        ← rowsMat_lmulD (d := 8) (A := sRowsF) sRowsF_length, hcomm])
    (fun h => hs1 (by rw [← coe_sU, h, Units.val_one]))
    (fun h => hsX (by rw [← coe_sU, h, coe_XU]))
    (fun h => hsX2 (by rw [← coe_sU, h, Units.val_pow_eq_pow_val, coe_XU, rowsMat_lpowD]))
  rw [hcard, show (3 : ℕ) ^ 4 = 9 * 9 by norm_num, show (288 : ℕ) = 9 * 32 by norm_num,
    ← mul_assoc]
  exact Dvd.dvd.mul_right (Nat.mul_dvd_mul h9 (dvd_refl 9)) 32

end CFSG.HardMathSupport.Foote.E27.Fi23
