module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.SevenRank
public import Certificates.Certificate125220
public import Certificates.Certificate125221
public import Certificates.Certificate125222
public import Certificates.Certificate125223

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native


theorem sevenX_check : agreeAll sevenXPairs = true := Certificates.certificate125220

theorem sevenYI_check : agreeAll sevenYPairs = true ∧ agreeAll sevenIPairs = true :=
  Certificates.certificate125221

theorem sevenG_check : agreeAll sevenGPairs = true := Certificates.certificate125222

theorem sevenNe_check :
    (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeXWord k) (aV ())) = true ∧
      (List.range 7).all (fun k => EdgeNoncomm.moveCheck (sevenNeYWord k) (aV ())) = true :=
  Certificates.certificate125223

@[expose] noncomputable def xG : Gmat := gw xW

@[expose] noncomputable def y7G : Gmat := gw yW

@[expose] noncomputable def iG : Gmat := gw iW

@[expose] noncomputable def gG : Gmat := gw gW

theorem xG_pow : xG ^ 7 = 1 := by
  have := agreeAll_sound sevenX_check (powL 7 xW, []) (by simp [sevenXPairs])
  simpa [gw_powL_eq, gw_nil, xG] using this

theorem dG_xG_comm : dG * xG = xG * dG := by
  have := agreeAll_sound sevenX_check (xW ++ dW, dW ++ xW) (by simp [sevenXPairs])
  simpa [gw_append, dG, xG] using this

theorem zG_xG_comm : zG * xG = xG * zG := by
  have := agreeAll_sound sevenX_check (xW ++ zW, zW ++ xW) (by simp [sevenXPairs])
  simpa [gw_append, zG, xG] using this

theorem xG_tG_comm : xG * tG = tG * xG := by
  have := agreeAll_sound sevenX_check (tW ++ xW, xW ++ tW) (by simp [sevenXPairs])
  simpa [gw_append, tG, xG] using this

theorem eG_xG : eG * xG = zG ^ 3 * xG * eG := by
  have := agreeAll_sound sevenX_check (xW ++ eW, eW ++ xW ++ powL 3 zW) (by simp [sevenXPairs])
  simpa [gw_append, gw_powL_eq, eG, xG, zG, mul_assoc] using this

theorem y7G_eq : y7G = eG * eG * xG := by
  simp [y7G, yW, gw_append, eG, xG, mul_assoc]

theorem y7G_pow : y7G ^ 7 = 1 := by
  have := agreeAll_sound sevenYI_check.1 (powL 7 yW, []) (by simp [sevenYPairs])
  simpa [gw_powL_eq, gw_nil, y7G] using this

theorem dG_iG_comm : dG * iG = iG * dG := by
  have := agreeAll_sound sevenYI_check.2 (iW ++ dW, dW ++ iW) (by simp [sevenIPairs])
  simpa [gw_append, dG, iG] using this

theorem yG_iG_comm : y7G * iG = iG * y7G := by
  have := agreeAll_sound sevenYI_check.2 (iW ++ yW, yW ++ iW) (by simp [sevenIPairs])
  simpa [gw_append, y7G, iG] using this

theorem gG_dG : gG * dG = xG ^ 3 * dG * gG := by
  have := agreeAll_sound sevenG_check (dW ++ gW, gW ++ dW ++ powL 3 xW) (by simp [sevenGPairs])
  simpa [gw_append, gw_powL_eq, gG, dG, xG, mul_assoc] using this

theorem gG_xG : gG * xG = xG ^ 6 * dG ^ 3 * gG := by
  have := agreeAll_sound sevenG_check (xW ++ gW, gW ++ powL 3 dW ++ powL 6 xW)
    (by simp [sevenGPairs])
  simpa [gw_append, gw_powL_eq, gG, dG, xG, mul_assoc] using this

theorem xG_ne_dG_pow (k : ℕ) : xG ≠ dG ^ k := by
  intro h
  set j := k % 7 with hj
  have hlt : j < 7 := Nat.mod_lt _ (by norm_num)
  have hE : xG = dG ^ j := by rw [h, pow_eq_pow_mod k dG_pow]
  have hmove : EdgeNoncomm.moveCheck (sevenNeXWord j) (aV ()) = true := by
    have := sevenNe_check.1
    rw [List.all_eq_true] at this
    exact this j (List.mem_range.2 hlt)
  apply gw_ne_one_of_moveCheck hmove
  rw [sevenNeXWord, gw_append, gw_powL_eq]
  show xG * dG ^ ((7 - j) % 7) = 1
  rw [hE, ← pow_add]
  have : (j + (7 - j) % 7) % 7 = 0 := by omega
  rw [pow_eq_pow_mod _ dG_pow, this, pow_zero]

theorem yG_ne_dG_pow (k : ℕ) : y7G ≠ dG ^ k := by
  intro h
  set j := k % 7 with hj
  have hlt : j < 7 := Nat.mod_lt _ (by norm_num)
  have hE : y7G = dG ^ j := by rw [h, pow_eq_pow_mod k dG_pow]
  have hmove : EdgeNoncomm.moveCheck (sevenNeYWord j) (aV ()) = true := by
    have := sevenNe_check.2
    rw [List.all_eq_true] at this
    exact this j (List.mem_range.2 hlt)
  apply gw_ne_one_of_moveCheck hmove
  rw [sevenNeYWord, gw_append, gw_powL_eq]
  show y7G * dG ^ ((7 - j) % 7) = 1
  rw [hE, ← pow_add]
  have : (j + (7 - j) % 7) % 7 = 0 := by omega
  rw [pow_eq_pow_mod _ dG_pow, this, pow_zero]

end CFSG.AGLEmbedding.Norton.MON5_7
