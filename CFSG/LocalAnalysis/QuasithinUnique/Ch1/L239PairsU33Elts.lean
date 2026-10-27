module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Geo

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.U33

open Matrix CFSG.Assembly.LowTwoRank CFSG.LinearGroups.UnitaryThreeOverNine
  CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F]

@[expose] def cM (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

theorem cM_unitary : ((cM F).map (· ^ 3))ᵀ * cM F = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cM, Matrix.mul_apply, Fin.sum_univ_three]

theorem cM_det : (cM F).det = 1 := by
  simp [cM, Matrix.det_fin_three]

variable (hF : Nat.card F = 9)

@[expose] noncomputable def cEl : StatedSU 3 3 F := mkSU hF (cM F) cM_unitary cM_det

variable {hF}

theorem coe_cEl : ((cEl hF : StatedSU 3 3 F) : GL (Fin 3) F).val = cM F := rfl

theorem cM_mulVec_ev (j : Fin 3) : cM F *ᵥ ev F j = ev F (j + 1) := by
  fin_cases j <;> ext k <;> fin_cases k <;> simp [cM, ev_apply, Matrix.mulVec, dotProduct]

theorem cEl_pow_three : cEl hF ^ 3 = 1 := by
  apply eq_of_matrix
  rw [pow_succ, pow_two, coe_mul_matrix, coe_mul_matrix, coe_cEl, Subgroup.coe_one, Units.val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [cM, Matrix.mul_apply, Fin.sum_univ_three]

theorem cEl_ne_one : cEl hF ≠ 1 := by
  intro h
  have := congrArg (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) h
  simp [coe_cEl, cM] at this

theorem orderOf_cEl : orderOf (cEl hF) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime cEl_pow_three cEl_ne_one

theorem cEl_mem_stab0 : cEl hF ∈ stab0 hF := by
  refine mem_stab0_of_monomial fun j => ⟨j + 1, 1, one_ne_zero, ?_⟩
  rw [coe_cEl, cM_mulVec_ev, one_smul]

theorem lineAct_cEl (j : Fin 3) : lineAct hF (cEl hF) (Pt hF j) = Pt hF (j + 1) :=
  lineAct_Pt_eq hF one_ne_zero (by rw [coe_cEl, cM_mulVec_ev, one_smul])

structure Idata (F : Type) [Field F] where
  i : F
  sq : i ^ 2 = -1
  three : (3 : F) = 0

section Block

variable (hF : Nat.card F = 9) (d : Idata F)

@[expose] def gM (i : F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, 0; 0, 1 + i, 1 + i; 0, -(1 - i), 1 - i]

@[expose] def aM (i : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, i, 0; 0, 0, -i]

@[expose] def m1M (i : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, -i; 0, -i, 0]

@[expose] def m2M (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, 0, -1; 0, 1, 0]

theorem gM_unitary : ((gM d.i).map (· ^ 3))ᵀ * gM d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem gM_det : (gM d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [gM, Matrix.det_fin_three]
  grind

theorem aM_unitary : ((aM d.i).map (· ^ 3))ᵀ * aM d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [aM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem aM_det : (aM d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [aM, Matrix.det_fin_three]
  grind

theorem m1M_unitary : ((m1M d.i).map (· ^ 3))ᵀ * m1M d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [m1M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem m1M_det : (m1M d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [m1M, Matrix.det_fin_three]
  grind

theorem m2M_unitary : ((m2M F).map (· ^ 3))ᵀ * m2M F = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [m2M, Matrix.mul_apply, Fin.sum_univ_three]
  all_goals norm_num

theorem m2M_det : (m2M F).det = 1 := by
  simp [m2M, Matrix.det_fin_three]

theorem i_ne_zero : d.i ≠ 0 := by
  intro h
  have hi := d.sq
  rw [h] at hi
  norm_num at hi

theorem one_add_i_ne_zero : 1 + d.i ≠ 0 := by
  intro h
  have hi := d.sq
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  grind

theorem one_sub_i_ne_zero : 1 - d.i ≠ 0 := by
  intro h
  have hi := d.sq
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  grind

include d in
theorem neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  exact h1 (by linear_combination h3 + h)

theorem mulVec_ev (M : Matrix (Fin 3) (Fin 3) F) (j : Fin 3) : M *ᵥ ev F j = fun k => M k j := by
  ext k
  fin_cases j <;> simp [ev_apply, Matrix.mulVec, dotProduct]

@[expose] noncomputable def gEl : StatedSU 3 3 F := mkSU hF (gM d.i) (gM_unitary d) (gM_det d)

@[expose] noncomputable def aEl : StatedSU 3 3 F := mkSU hF (aM d.i) (aM_unitary d) (aM_det d)

@[expose] noncomputable def m1El : StatedSU 3 3 F := mkSU hF (m1M d.i) (m1M_unitary d) (m1M_det d)

@[expose] noncomputable def m2El : StatedSU 3 3 F := mkSU hF (m2M F) m2M_unitary m2M_det

variable {hF d}

theorem coe_gEl : ((gEl hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = gM d.i := rfl
theorem coe_aEl : ((aEl hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = aM d.i := rfl
theorem coe_m1El : ((m1El hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = m1M d.i := rfl
theorem coe_m2El : ((m2El hF : StatedSU 3 3 F) : GL (Fin 3) F).val = m2M F := rfl
theorem coe_inv_aEl :
    (((aEl hF d)⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F).val = ((aM d.i).map (· ^ 3))ᵀ := rfl
theorem coe_inv_m1El :
    (((m1El hF d)⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F).val = ((m1M d.i).map (· ^ 3))ᵀ := rfl

theorem gEl_pow_three : gEl hF d ^ 3 = 1 := by
  have hi := d.sq
  have h3 := d.three
  apply eq_of_matrix
  rw [pow_succ, pow_two, coe_mul_matrix, coe_mul_matrix, coe_gEl, Subgroup.coe_one, Units.val_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem gEl_ne_one : gEl hF d ≠ 1 := by
  intro h
  have := congrArg (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp only [coe_gEl, gM, Subgroup.coe_one, Units.val_one] at this
  simp at this
  exact i_ne_zero d this

theorem orderOf_gEl : orderOf (gEl hF d) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime gEl_pow_three gEl_ne_one

theorem lineAct_gEl_zero : lineAct hF (gEl hF d) (Pt hF 0) = Pt hF 0 := by
  refine lineAct_Pt_eq hF one_ne_zero ?_
  rw [coe_gEl, mulVec_ev, one_smul]
  ext k
  fin_cases k <;> simp [gM, ev_apply]

theorem lineAct_aEl_zero : lineAct hF (aEl hF d) (Pt hF 0) = Pt hF 0 := by
  refine lineAct_Pt_eq hF one_ne_zero ?_
  rw [coe_aEl, mulVec_ev, one_smul]
  ext k
  fin_cases k <;> simp [aM, ev_apply]

theorem gEl_not_mem_stab0 : gEl hF d ∉ stab0 hF := by
  intro hg
  obtain ⟨k, hk⟩ := exists_lineAct_Pt_of_mem_stab0 hg 1
  have hv : (gM d.i) *ᵥ ev F 1 ∈ (Pt hF k).1 := by
    rw [← hk, lineAct_val]
    exact Submodule.mem_map.2 ⟨ev F 1, Submodule.mem_span_singleton_self _, by
      rw [Matrix.toLin'_apply, coe_gEl]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hv
  rw [mulVec_ev] at hc
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  fin_cases k
  · simp [gM, ev_apply] at h1
    exact one_add_i_ne_zero d h1.symm
  · simp [gM, ev_apply] at h2
    exact one_sub_i_ne_zero d (by linear_combination -h2.symm)
  · simp [gM, ev_apply] at h1
    exact one_add_i_ne_zero d h1.symm

theorem aEl_mem_stab0 : aEl hF d ∈ stab0 hF := by
  refine mem_stab0_of_monomial fun j => ?_
  rw [coe_aEl, mulVec_ev]
  fin_cases j
  · exact ⟨0, 1, one_ne_zero, by ext k; fin_cases k <;> simp [aM, ev_apply]⟩
  · exact ⟨1, d.i, i_ne_zero d, by ext k; fin_cases k <;> simp [aM, ev_apply]⟩
  · exact ⟨2, -d.i, neg_ne_zero.2 (i_ne_zero d), by ext k; fin_cases k <;> simp [aM, ev_apply]⟩

theorem m1El_mem_stab0 : m1El hF d ∈ stab0 hF := by
  refine mem_stab0_of_monomial fun j => ?_
  rw [coe_m1El, mulVec_ev]
  fin_cases j
  · exact ⟨0, 1, one_ne_zero, by ext k; fin_cases k <;> simp [m1M, ev_apply]⟩
  · exact ⟨2, -d.i, neg_ne_zero.2 (i_ne_zero d), by ext k; fin_cases k <;> simp [m1M, ev_apply]⟩
  · exact ⟨1, -d.i, neg_ne_zero.2 (i_ne_zero d), by ext k; fin_cases k <;> simp [m1M, ev_apply]⟩

theorem m2El_mem_stab0 : m2El hF ∈ stab0 hF := by
  refine mem_stab0_of_monomial fun j => ?_
  rw [coe_m2El, mulVec_ev]
  fin_cases j
  · exact ⟨0, 1, one_ne_zero, by ext k; fin_cases k <;> simp [m2M, ev_apply]⟩
  · exact ⟨2, 1, one_ne_zero, by ext k; fin_cases k <;> simp [m2M, ev_apply]⟩
  · exact ⟨1, -1, neg_ne_zero.2 one_ne_zero, by ext k; fin_cases k <;> simp [m2M, ev_apply]⟩

theorem comm_aEl_gEl :
    aEl hF d * gEl hF d * (aEl hF d)⁻¹ * (gEl hF d)⁻¹ = m1El hF d := by
  apply commutatorElement_eq_of_mul
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_m1El, coe_gEl, coe_aEl, coe_inv_aEl]
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [m1M, gM, aM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem comm_m1El_gEl :
    m1El hF d * gEl hF d * (m1El hF d)⁻¹ * (gEl hF d)⁻¹ = m2El hF := by
  apply commutatorElement_eq_of_mul
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_m2El, coe_gEl, coe_m1El, coe_inv_m1El]
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [m2M, gM, m1M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

include d in
theorem m2El_sq_ne_one : m2El hF ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp [pow_two, coe_m2El, m2M, Matrix.mul_apply, Fin.sum_univ_three] at this
  exact neg_one_ne_one d this

@[expose] def sM (i : F) : Matrix (Fin 3) (Fin 3) F := !![-i, 0, 0; 0, i, 0; 0, 0, 1]

@[expose] def u1M (i : F) : Matrix (Fin 3) (Fin 3) F := !![-i, 0, 0; 0, -1, 0; 0, 0, -i]

@[expose] def u2M (i : F) : Matrix (Fin 3) (Fin 3) F := !![1, 0, 0; 0, -i, 0; 0, 0, i]

variable (hF d)

theorem sM_unitary : ((sM d.i).map (· ^ 3))ᵀ * sM d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [sM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem sM_det : (sM d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [sM, Matrix.det_fin_three]
  grind

theorem u1M_unitary : ((u1M d.i).map (· ^ 3))ᵀ * u1M d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [u1M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u1M_det : (u1M d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [u1M, Matrix.det_fin_three]
  grind

theorem u2M_unitary : ((u2M d.i).map (· ^ 3))ᵀ * u2M d.i = 1 := by
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;> simp [u2M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u2M_det : (u2M d.i).det = 1 := by
  have hi := d.sq
  have h3 := d.three
  simp [u2M, Matrix.det_fin_three]
  grind

@[expose] noncomputable def sEl : StatedSU 3 3 F := mkSU hF (sM d.i) (sM_unitary d) (sM_det d)

@[expose] noncomputable def u1El : StatedSU 3 3 F := mkSU hF (u1M d.i) (u1M_unitary d) (u1M_det d)

@[expose] noncomputable def u2El : StatedSU 3 3 F := mkSU hF (u2M d.i) (u2M_unitary d) (u2M_det d)

variable {hF d}

theorem coe_sEl : ((sEl hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = sM d.i := rfl
theorem coe_u1El : ((u1El hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = u1M d.i := rfl
theorem coe_u2El : ((u2El hF d : StatedSU 3 3 F) : GL (Fin 3) F).val = u2M d.i := rfl
theorem coe_inv_sEl :
    (((sEl hF d)⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F).val = ((sM d.i).map (· ^ 3))ᵀ := rfl
theorem coe_inv_u1El :
    (((u1El hF d)⁻¹ : StatedSU 3 3 F) : GL (Fin 3) F).val = ((u1M d.i).map (· ^ 3))ᵀ := rfl

theorem comm_sEl_cEl : sEl hF d * cEl hF * (sEl hF d)⁻¹ * (cEl hF)⁻¹ = u1El hF d := by
  apply commutatorElement_eq_of_mul
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_u1El, coe_cEl, coe_sEl, coe_inv_sEl]
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [u1M, cM, sM, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem comm_u1El_cEl : u1El hF d * cEl hF * (u1El hF d)⁻¹ * (cEl hF)⁻¹ = u2El hF d := by
  apply commutatorElement_eq_of_mul
  apply eq_of_matrix
  rw [coe_mul_matrix, coe_mul_matrix, coe_mul_matrix, coe_u2El, coe_cEl, coe_u1El, coe_inv_u1El]
  have hi := d.sq
  have h3 := d.three
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [u2M, cM, u1M, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u2El_sq_ne_one : u2El hF d ^ 2 ≠ 1 := by
  intro h
  have := congrArg (fun g : StatedSU 3 3 F => ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp [pow_two, coe_u2El, u2M, Matrix.mul_apply, Fin.sum_univ_three] at this
  have hi := d.sq
  have h3 := d.three
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  grind

theorem sEl_mem_stab0 : sEl hF d ∈ stab0 hF := by
  refine mem_stab0_of_monomial fun j => ?_
  rw [coe_sEl, mulVec_ev]
  fin_cases j
  · exact ⟨0, -d.i, neg_ne_zero.2 (i_ne_zero d), by ext k; fin_cases k <;> simp [sM, ev_apply]⟩
  · exact ⟨1, d.i, i_ne_zero d, by ext k; fin_cases k <;> simp [sM, ev_apply]⟩
  · exact ⟨2, 1, one_ne_zero, by ext k; fin_cases k <;> simp [sM, ev_apply]⟩

theorem lineAct_sEl (j : Fin 3) : lineAct hF (sEl hF d) (Pt hF j) = Pt hF j := by
  fin_cases j
  · exact lineAct_Pt_eq hF (neg_ne_zero.2 (i_ne_zero d)) (by
      rw [coe_sEl, mulVec_ev]; ext k; fin_cases k <;> simp [sM, ev_apply])
  · exact lineAct_Pt_eq hF (i_ne_zero d) (by
      rw [coe_sEl, mulVec_ev]; ext k; fin_cases k <;> simp [sM, ev_apply])
  · exact lineAct_Pt_eq hF one_ne_zero (by
      rw [coe_sEl, mulVec_ev, one_smul]; ext k; fin_cases k <;> simp [sM, ev_apply])

end Block

end CFSG.QuasithinUnique.Vol2Native.L239.U33
