module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving

section Dihedral

open CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

private def diagGL (ω : Fˣ) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Units.mk (Matrix.diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F)])
    (Matrix.diagonal ![((ω⁻¹ : Fˣ) : F), (ω : F)])
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal])
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.diagonal])

private def antiGL : Matrix.GeneralLinearGroup (Fin 2) F :=
  Units.mk !![0, -1; 1, 0] !![0, 1; -1, 0]
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two])
    (by ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two])

private lemma diagGL_mem (ω : Fˣ) : diagGL ω ∈ StatedSL 2 F := by
  refine Subgroup.subset_closure ?_
  show (Matrix.diagonal ![(ω : F), ((ω⁻¹ : Fˣ) : F)]).det = 1
  simp [Matrix.det_diagonal, Fin.prod_univ_two]

private lemma antiGL_mem : (antiGL : Matrix.GeneralLinearGroup (Fin 2) F) ∈ StatedSL 2 F := by
  refine Subgroup.subset_closure ?_
  show (!![(0 : F), -1; 1, 0]).det = 1
  simp [Matrix.det_fin_two_of]

private def diagHom : Fˣ →* Matrix.GeneralLinearGroup (Fin 2) F where
  toFun := diagGL
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.diagonal]
  map_mul' ω η := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagGL, Matrix.mul_apply, Matrix.diagonal, mul_comm]

end Dihedral

theorem exists_dihedral_seven_psl2 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 8) :
    ∃ u t : CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F),
      u * u = 1 ∧ u ≠ 1 ∧ orderOf t = 7 ∧ u * t * u⁻¹ = t⁻¹ := by
  open CFSG.Assembly.LowTwoRank in
  obtain ⟨ω, hω⟩ : ∃ ω : Fˣ, orderOf ω = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact exists_prime_orderOf_dvd_card' (G := Fˣ) 7 (by simp [Nat.card_units, hF])
  have hω7 : ω ^ 7 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  let uH : StatedSL 2 F := ⟨antiGL, antiGL_mem⟩
  let tH : StatedSL 2 F := ⟨diagGL ω, diagGL_mem ω⟩
  refine ⟨QuotientGroup.mk uH, QuotientGroup.mk tH, ?_, ?_, ?_, ?_⟩
  ·
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rw [StatedScalars, MonoidHom.mem_range]
    refine ⟨-1, Units.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uH, antiGL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar]
  ·
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h
    obtain ⟨c, hc⟩ := h
    have h01 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 1) hc
    simp [uH, antiGL, Matrix.GeneralLinearGroup.scalar] at h01
  ·
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    apply orderOf_eq_prime
    · have h7 : tH ^ 7 = 1 := by
        apply Subtype.ext
        change diagGL ω ^ 7 = 1
        show diagHom ω ^ 7 = 1
        rw [← map_pow, hω7, map_one]
      rw [← QuotientGroup.mk_pow, h7, QuotientGroup.mk_one]
    · intro h
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
        MonoidHom.mem_range] at h
      obtain ⟨c, hc⟩ := h
      have h00 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F) 0 0) hc
      have h11 := congrArg (fun g : Matrix.GeneralLinearGroup (Fin 2) F =>
        (g : Matrix (Fin 2) (Fin 2) F) 1 1) hc
      simp [tH, diagGL, Matrix.GeneralLinearGroup.scalar] at h00 h11
      have hinv : ω = ω⁻¹ := Units.ext (h00.symm.trans (h11.trans (Units.val_inv_eq_inv_val ω).symm))
      have hsq : ω * ω = ω * ω⁻¹ := congrArg (ω * ·) hinv
      rw [mul_inv_cancel] at hsq
      have hdvd : orderOf ω ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
      rw [hω] at hdvd
      norm_num at hdvd
  ·
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv]
    congr 1
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uH, tH, antiGL, diagGL, Matrix.mul_apply, Matrix.diagonal,
        Matrix.vecHead, Matrix.vecTail]

end CFSG.HardMathSupport.Meierfrankenfeld.Proving
