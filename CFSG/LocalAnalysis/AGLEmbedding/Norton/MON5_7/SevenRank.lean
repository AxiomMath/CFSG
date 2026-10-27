module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.RankThreeIndep
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.RankThreeLemmas
public import CFSG.Monster.Generated.FiniteSimple
public import Certificates.Certificate125210
public import Certificates.Certificate125211
public import Certificates.Certificate125212

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native


theorem sevenOrder_check : agreeAll sevenOrderPairs = true := Certificates.certificate125210

theorem sevenCommAct_check : agreeAll sevenCommPairs = true ∧ agreeAll sevenActPairs = true :=
  Certificates.certificate125211

theorem sevenMove_check :
    EdgeNoncomm.moveCheck dW (aV ()) = true ∧ EdgeNoncomm.moveCheck zW (aV ()) = true ∧
      (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeWord k) (aV ())) = true :=
  Certificates.certificate125212

theorem gw_powL_eq (k : ℕ) (w : List Native.Gen) : gw (powL k w) = gw w ^ k :=
  Subtype.ext (wordLin_powL k w)

@[expose] noncomputable def tG : Gmat := gw tW

@[expose] noncomputable def dG : Gmat := gw dW

@[expose] noncomputable def zG : Gmat := gw zW

@[expose] noncomputable def eG : Gmat := gw eW

theorem dG_pow : dG ^ 7 = 1 := by
  have := agreeAll_sound sevenOrder_check (powL 7 dW, []) (by simp [sevenOrderPairs])
  simpa [gw_powL_eq, gw_nil, dG] using this

theorem zG_pow : zG ^ 7 = 1 := by
  have := agreeAll_sound sevenOrder_check (powL 7 zW, []) (by simp [sevenOrderPairs])
  simpa [gw_powL_eq, gw_nil, zG] using this

theorem eG_pow : eG ^ 7 = 1 := by
  have := agreeAll_sound sevenOrder_check (powL 7 eW, []) (by simp [sevenOrderPairs])
  simpa [gw_powL_eq, gw_nil, eG] using this

theorem dG_zG_comm : dG * zG = zG * dG := by
  have := agreeAll_sound sevenCommAct_check.1 (dW ++ zW, zW ++ dW) (by simp [sevenCommPairs])
  simpa [gw_append, dG, zG] using this.symm

theorem dG_eG_comm : dG * eG = eG * dG := by
  have := agreeAll_sound sevenCommAct_check.1 (dW ++ eW, eW ++ dW) (by simp [sevenCommPairs])
  simpa [gw_append, dG, eG] using this.symm

theorem zG_eG_comm : zG * eG = eG * zG := by
  have := agreeAll_sound sevenCommAct_check.1 (zW ++ eW, eW ++ zW) (by simp [sevenCommPairs])
  simpa [gw_append, zG, eG] using this.symm

theorem tG_sq : tG * tG = 1 := by
  have := agreeAll_sound sevenCommAct_check.2 (tW ++ tW, []) (by simp [sevenActPairs])
  simpa [gw_append, gw_nil, tG] using this

theorem tG_dG : tG * dG * tG = dG := by
  have h := agreeAll_sound sevenCommAct_check.2 (tW ++ dW, dW ++ tW) (by simp [sevenActPairs])
  have h' : dG * tG = tG * dG := by simpa [gw_append, dG, tG] using h
  calc tG * dG * tG = (tG * dG) * tG := rfl
    _ = (dG * tG) * tG := by rw [h']
    _ = dG * (tG * tG) := by rw [mul_assoc]
    _ = dG := by rw [tG_sq, mul_one]

theorem tG_zG : tG * zG * tG = zG⁻¹ := by
  have h := agreeAll_sound sevenCommAct_check.2 (tW ++ zW ++ tW ++ zW, [])
    (by simp [sevenActPairs])
  have h' : zG * (tG * zG * tG) = 1 := by
    simpa [gw_append, gw_nil, tG, zG, mul_assoc] using h
  exact (inv_eq_of_mul_eq_one_right h').symm

theorem tG_eG : tG * eG * tG = eG⁻¹ := by
  have h := agreeAll_sound sevenCommAct_check.2 (tW ++ eW ++ tW ++ eW, [])
    (by simp [sevenActPairs])
  have h' : eG * (tG * eG * tG) = 1 := by
    simpa [gw_append, gw_nil, tG, eG, mul_assoc] using h
  exact (inv_eq_of_mul_eq_one_right h').symm

theorem dG_ne_one : dG ≠ 1 := gw_ne_one_of_moveCheck sevenMove_check.1

theorem zG_ne_one : zG ≠ 1 := gw_ne_one_of_moveCheck sevenMove_check.2.1

theorem eG_ne_zG_pow (k : ℕ) : eG ≠ zG ^ k := by
  intro h
  set j := k % 7 with hj
  have hlt : j < 7 := Nat.mod_lt _ (by norm_num)
  have hE : eG = zG ^ j := by rw [h, pow_eq_pow_mod k zG_pow]
  have hmem : sevenNeWord j ∈ (List.range 7).map sevenNeWord :=
    List.mem_map.2 ⟨j, List.mem_range.2 hlt, rfl⟩
  have hmove : EdgeNoncomm.moveCheck (sevenNeWord j) (aV ()) = true := by
    have := sevenMove_check.2.2
    rw [List.all_eq_true] at this
    exact this j (List.mem_range.2 hlt)
  have hne := gw_ne_one_of_moveCheck hmove
  apply hne
  rw [sevenNeWord, gw_append, gw_powL_eq]
  show eG * zG ^ ((7 - j) % 7) = 1
  rw [hE, ← pow_add]
  have : (j + (7 - j) % 7) % 7 = 0 := by omega
  rw [pow_eq_pow_mod _ zG_pow, this, pow_zero]

theorem seven_indep : ∀ c : Fin 3 → ZMod 7,
    ((List.finRange 3).map fun k => (![dG, zG, eG] : Fin 3 → Gmat) k ^ (c k).val).prod = 1 →
      c = 0 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  indep_of_involution (by norm_num) dG zG eG tG dG_pow zG_pow eG_pow dG_ne_one zG_ne_one
    zG_eG_comm tG_sq tG_dG tG_zG tG_eG eG_ne_zG_pow

theorem three_le_pRank_seven_gmat : 3 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup Gmat) := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  refine CFSG.AGLEmbedding.le_pRank_of_indep (Nat.prime_seven) (n := 3) ![dG, zG, eG] ?_ ?_
    seven_indep (H := ⊤) (fun _ => Subgroup.mem_top _)
  · intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact dG_zG_comm
    · exact dG_eG_comm
    · exact dG_zG_comm.symm
    · rfl
    · exact zG_eG_comm
    · exact dG_eG_comm.symm
    · exact zG_eG_comm.symm
    · rfl
  · intro i
    fin_cases i
    · exact dG_pow
    · exact zG_pow
    · exact eG_pow

end CFSG.AGLEmbedding.Norton.MON5_7
