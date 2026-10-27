module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Wit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Can

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def Idata.ofUnit (hF : Nat.card F = 9) (i : Fˣ) (hi : orderOf i = 4) : Idata F where
  i := (i : F)
  sq := sq_eq_neg_one_of_orderOf hi
  three := by
    have := (unitaryFieldData_of_card hF).charP
    exact_mod_cast CharP.cast_eq_zero F 3

section Wreath

variable (hF : Nat.card F = 9) (d : Idata F)

@[expose] def tM (i : F) : Matrix (Fin 3) (Fin 3) F := !![-i, 0, 0; 0, 1, 0; 0, 0, i]

@[expose] def wM (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem tM_unitary : ((tM d.i).map (· ^ 3))ᵀ * tM d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem tM_det : (tM d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [tM, Matrix.det_fin_three]
  grind

theorem wM_unitary : ((wM F).map (· ^ 3))ᵀ * wM F = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals norm_num

theorem wM_det : (wM F).det = 1 := by
  simp [wM, Matrix.det_fin_three]

@[expose] noncomputable def tEl : StatedSU 3 3 F := mkSU hF (tM d.i) (tM_unitary d) (tM_det d)

@[expose] noncomputable def wEl : StatedSU 3 3 F := mkSU hF (wM F) wM_unitary wM_det

variable {hF d}

theorem coe_tEl : ((tEl hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = tM d.i := rfl
theorem coe_wEl : ((wEl hF : StatedSU 3 3 F) : GL (Fin 3) F).val = wM F := rfl
theorem coe_inv_wEl :
    (((wEl hF)⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F).val = ((wM F).map (· ^ 3))ᵀ := rfl

theorem wEl_mul_self : wEl hF * wEl hF = 1 := by
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_wEl, Subgroup.coe_one, Units.val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_three]

theorem wEl_inv : (wEl hF)⁻¹ = wEl hF := inv_eq_of_mul_eq_one_right wEl_mul_self

theorem sEl_mul_tEl_comm : sEl hF d * tEl hF d = tEl hF d * sEl hF d := by
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_sEl, coe_tEl]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sM, tM, Matrix.mul_apply, Fin.sum_univ_three]

theorem wEl_conj_sEl : (wEl hF)⁻¹ * sEl hF d * wEl hF = tEl hF d := by
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_inv_wEl, coe_sEl, coe_wEl, coe_tEl]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, sM, tM, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals norm_num

theorem wEl_conj_tEl : (wEl hF)⁻¹ * tEl hF d * wEl hF = sEl hF d := by
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_inv_wEl, coe_tEl, coe_wEl, coe_sEl]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [wM, sM, tM, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals norm_num

theorem sM_eq_diagonal (i : F) : sM i = diagonal ![-i, i, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sM]

theorem tM_eq_diagonal (i : F) : tM i = diagonal ![-i, 1, i] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [tM]

end Wreath

theorem offdiag_zero_of_commute_diagonal {a b c : F} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {M : Matrix (Fin 3) (Fin 3) F} (h : M * diagonal ![a, b, c] = diagonal ![a, b, c] * M) :
    M 0 1 = 0 ∧ M 0 2 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 := by
  have e : ∀ j k, M j k * (![a, b, c] k) = (![a, b, c] j) * M j k := fun j k => by
    have := congrFun (congrFun h j) k
    simpa [Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have key : ∀ j k, ![a, b, c] j ≠ ![a, b, c] k → M j k = 0 := fun j k hjk => by
    have h1 : M j k * (![a, b, c] k - ![a, b, c] j) = 0 := by linear_combination e j k
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd (sub_eq_zero.1 h2).symm hjk
  exact ⟨key 0 1 (by simpa using hab), key 0 2 (by simpa using hac), key 1 0 (by simpa using hab.symm),
    key 1 2 (by simpa using hbc), key 2 0 (by simpa using hac.symm),
    key 2 1 (by simpa using hbc.symm)⟩

theorem neg_i_ne_i (d : Idata F) : -d.i ≠ d.i := by
  intro h
  have hi := d.sq
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have h2 : (2 : F) * d.i = 0 := by linear_combination -h
  have : d.i * d.i = 0 := by
    have h4 : (2 : F) = -1 := by linear_combination h3
    rw [h4] at h2
    have : d.i = 0 := by linear_combination -h2
    rw [this]
    ring
  grind

theorem neg_i_ne_one (d : Idata F) : -d.i ≠ 1 := by
  intro h
  have hi := d.sq
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  grind

theorem i_ne_one (d : Idata F) : d.i ≠ 1 := by
  intro h
  have hi := d.sq
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  grind

section Can1

variable (hF : Nat.card F = 9) (d : Idata F)

@[expose] noncomputable def S0 : Subgroup (StatedSU 3 3 F) :=
  Subgroup.closure {sEl hF d, tEl hF d, wEl hF}

variable {hF d}

theorem sEl_mem_S0 : sEl hF d ∈ S0 hF d := Subgroup.subset_closure (Set.mem_insert _ _)

theorem tEl_mem_S0 : tEl hF d ∈ S0 hF d :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem wEl_mem_S0 : wEl hF ∈ S0 hF d :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem tau0_matrix : ((tau0 hF : StatedSU 3 3 F) : GL (Fin 3) F).val = diagonal ![1, -1, -1] :=
  coe_tauLine_e0 (h := unitaryFieldData_of_card hF) (hF := hF) (L₀ := Pt hF 0) Pt_zero_val

theorem sq_sEl_tEl : (sEl hF d * tEl hF d) ^ 2 = tau0 hF := by
  have hi := d.sq
  have h3 := d.three
  apply eq_of_matrix
  rw [pow_two, coe_mul_matrix, coe_mul_matrix, coe_sEl, coe_tEl, tau0_matrix]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [sM, tM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem tau0_mem_S0 : tau0 hF ∈ S0 hF d := by
  rw [← sq_sEl_tEl (hF := hF) (d := d)]
  exact pow_mem (mul_mem sEl_mem_S0 tEl_mem_S0) 2

theorem S0_le_centralizer_tau0 : S0 hF d ≤ Subgroup.centralizer {tau0 hF} := by
  rw [S0, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, tau0_matrix]
  rcases hg with rfl | rfl | rfl
  · rw [coe_sEl]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [sM, Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [coe_tEl]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [tM, Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [coe_wEl]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [wM, Matrix.mul_apply, Matrix.diagonal_apply]

theorem tau0_mem_canZ : tau0 hF ∈ canZ (S0 hF d) :=
  ⟨tau0_mem_S0, Subgroup.mem_centralizer_iff.2 fun y hy => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (S0_le_centralizer_tau0 hy)
    exact this⟩

theorem canK1_le_K1 : canK1 (S0 hF d) ≤ K1 hF := by
  intro g hg
  have h1 : tau0 hF * g = g * tau0 hF := Subgroup.mem_centralizer_iff.1 hg (tau0 hF) tau0_mem_canZ
  exact Subgroup.mem_centralizer_singleton_iff.2 h1.symm

theorem K1_le_canK1 : K1 hF ≤ canK1 (S0 hF d) := by
  intro g hg
  obtain ⟨A, hAu, hgA⟩ := (mem_centralizer_tauLine_iff (h := unitaryFieldData_of_card hF)
    (hF := hF) (L₀ := Pt hF 0) Pt_zero_val g).1 hg
  refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
  have hzc : z ∈ Subgroup.centralizer (S0 hF d : Set (StatedSU 3 3 F)) := hz.2
  have hzs : sEl hF d * z = z * sEl hF d := Subgroup.mem_centralizer_iff.1 hzc _ sEl_mem_S0
  have hzw : wEl hF * z = z * wEl hF := Subgroup.mem_centralizer_iff.1 hzc _ wEl_mem_S0
  have hs : ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-d.i, d.i, 1] =
      diagonal ![-d.i, d.i, 1] * ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hzs
    simp only [coe_mul_matrix, coe_sEl, sM_eq_diagonal] at this
    exact this.symm
  obtain ⟨h01, h02, h10, h12, h20, h21⟩ :=
    offdiag_zero_of_commute_diagonal (neg_i_ne_i d) (neg_i_ne_one d) (i_ne_one d) hs
  have hw : ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1 =
      ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 := by
    have := congrArg (fun g : StatedSU 3 3 F =>
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2) hzw
    simp [coe_wEl, wM, Matrix.mul_apply, Fin.sum_univ_three, h10, h12] at this
    exact this.symm
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, hgA]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, h01, h02, h10, h12, h20, h21, hw, mul_comm]

theorem canK1_eq_K1 : canK1 (S0 hF d) = K1 hF := le_antisymm canK1_le_K1 K1_le_canK1

end Can1

end CFSG.QuasithinUnique.Vol2Native.L239.U33
