module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenFrame
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtMu
public import CFSG.GH74.Generic.BProg.B2.GenLocU4ExtCore

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
  CFSG.ClassicalInvolution.Phan CFSG.GH74.Generic.BProg.B2.GenLocU4Aux CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups

namespace GenLocU4Out

variable {K : Type} [Field K] {p f : ℕ}

@[expose] def Y2 : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![1, -1]

@[expose] def J2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def J2' : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, 0]

theorem Y2_mul : (Y2 : Matrix (Fin 2) (Fin 2) K) * Y2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y2, Matrix.mul_apply, Matrix.diagonal]

theorem J2_mul : (J2 : Matrix (Fin 2) (Fin 2) K) * J2' = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, J2', Matrix.mul_apply, Fin.sum_univ_two]

theorem J2_mul' : (J2' : Matrix (Fin 2) (Fin 2) K) * J2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, J2', Matrix.mul_apply, Fin.sum_univ_two]

theorem Y2_map (hq : Odd (p ^ f)) : (Y2 : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)) = Y2 := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y2, Matrix.diagonal, zero_pow hq0, Odd.neg_pow hq]

theorem J2_map (hq : Odd (p ^ f)) : (J2 : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)) = J2 := by
  have hq0 : p ^ f ≠ 0 := hq.pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, zero_pow hq0, Odd.neg_pow hq]

theorem Y2_unitary (hq : Odd (p ^ f)) :
    ((Y2 : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * Y2 = 1 := by
  rw [Y2_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y2, Matrix.mul_apply, Matrix.diagonal]

theorem J2_unitary (hq : Odd (p ^ f)) :
    ((J2 : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * J2 = 1 := by
  rw [J2_map hq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J2, Matrix.mul_apply, Fin.sum_univ_two]

theorem Y2_eq : (Y2 : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Y2, Matrix.diagonal]

theorem J_sq_matrix (X : Matrix (Fin 2) (Fin 2) K) : (J2 : Matrix (Fin 2) (Fin 2) K) * (J2 * X * J2') * J2' = X := by
  rw [Matrix.eta_fin_two X]
  simp only [J2, J2', Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem YJ_comm_matrix (X : Matrix (Fin 2) (Fin 2) K) :
    (Y2 : Matrix (Fin 2) (Fin 2) K) * (J2 * X * J2') * Y2 = J2 * (Y2 * X * Y2) * J2' := by
  rw [Matrix.eta_fin_two X, Y2_eq]
  simp only [J2, J2', Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

section Auts

variable [Finite K] [Fact p.Prime] [CharP K p]

@[expose] noncomputable def cU2 (h : UnitaryFieldData p f K) (M : GL (Fin 2) K)
    (hM : M ∈ primeFormUnitary h (idGram K 2)) : MulAut (Su K p f 2) :=
  (GenLocU3Blk.suEquiv h 2).trans ((KFU.conjSU h ⟨M, hM⟩).trans (GenLocU3Blk.suEquiv h 2).symm)

theorem coe_cU2 (h : UnitaryFieldData p f K) (M : GL (Fin 2) K) (hM : M ∈ primeFormUnitary h (idGram K 2))
    (x : Su K p f 2) :
    (((cU2 h M hM x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (M : Matrix (Fin 2) (Fin 2) K) * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((M⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have : ((cU2 h M hM x : Su K p f 2) : GL (Fin 2) K) = M * (x : GL (Fin 2) K) * M⁻¹ := rfl
  rw [this]
  simp only [Units.val_mul]


@[expose] def Ygl : GL (Fin 2) K := ⟨Y2, Y2, Y2_mul, Y2_mul⟩

@[expose] def Jgl : GL (Fin 2) K := ⟨J2, J2', J2_mul, J2_mul'⟩

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem Ygl_mem (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) :
    (Ygl : GL (Fin 2) K) ∈ primeFormUnitary h (idGram K 2) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  exact Y2_unitary hq

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem Jgl_mem (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) :
    (Jgl : GL (Fin 2) K) ∈ primeFormUnitary h (idGram K 2) := by
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  exact J2_unitary hq

@[expose] noncomputable def aY (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) : MulAut (Su K p f 2) :=
  cU2 h Ygl (Ygl_mem h hq)

@[expose] noncomputable def bJ (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) : MulAut (Su K p f 2) :=
  cU2 h Jgl (Jgl_mem h hq)

theorem coe_aY (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) (x : Su K p f 2) :
    (((aY h hq x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Y2 * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y2 := by
  rw [aY, coe_cU2]
  rfl

theorem coe_bJ (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) (x : Su K p f 2) :
    (((bJ h hq x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      J2 * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * J2' := by
  rw [bJ, coe_cU2]
  rfl

theorem aY_sq (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) : aY h hq * aY h hq = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
  show (((aY h hq (aY h hq x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_aY, coe_aY]
  show _ = (((x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  calc Y2 * (Y2 * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y2) * Y2
      = (Y2 * Y2) * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (Y2 * Y2) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Y2_mul, Matrix.one_mul, Matrix.mul_one]

theorem bJ_sq (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) : bJ h hq * bJ h hq = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
  show (((bJ h hq (bJ h hq x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_bJ, coe_bJ]
  show _ = (((x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  exact J_sq_matrix _

theorem aY_bJ_comm (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) : aY h hq * bJ h hq = bJ h hq * aY h hq := by
  refine MulEquiv.ext fun x => Subtype.ext (Units.ext ?_)
  show (((aY h hq (bJ h hq x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    (((bJ h hq (aY h hq x) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  rw [coe_aY, coe_bJ, coe_bJ, coe_aY]
  exact YJ_comm_matrix _


omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem pow_pow_card (h : UnitaryFieldData p f K) (x : K) : (x ^ (p ^ f)) ^ (p ^ f) = x := by
  have := h.bar_bar x
  simpa [h.bar_apply] using this

@[expose] noncomputable def diagEl (h : UnitaryFieldData p f K) {ε : K} (hε : ε ^ (p ^ f) * ε = 1) : Su K p f 2 :=
  su2Mk (p := p) (f := f) !![ε, 0; 0, ε ^ (p ^ f)]
    (by rw [Matrix.det_fin_two_of]; linear_combination hε)
    (by
      have hq0 : p ^ f ≠ 0 := (pow_pos h.prime.pos f).ne'
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, zero_pow hq0, pow_pow_card h] <;>
        linear_combination hε)

theorem coe_diagEl (h : UnitaryFieldData p f K) {ε : K} (hε : ε ^ (p ^ f) * ε = 1) :
    (((diagEl h hε : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![ε, 0; 0, ε ^ (p ^ f)] := rfl

theorem aY_ne_one (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) (h2 : (2 : K) ≠ 0) : aY h hq ≠ 1 := by
  intro h1
  have hdet : (J2 : Matrix (Fin 2) (Fin 2) K).det = 1 := by simp [J2, Matrix.det_fin_two_of]
  let x : Su K p f 2 := su2Mk (p := p) (f := f) J2 hdet (J2_unitary hq)
  have e := congrArg (fun φ : MulAut (Su K p f 2) =>
    (((φ x : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 1) h1
  simp only [MulAut.one_apply] at e
  rw [coe_aY, coe_su2Mk] at e
  apply h2
  simp [Y2_eq, J2, Matrix.mul_apply, Fin.sum_univ_two] at e
  linear_combination -e

theorem bJ_ne_one (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {ε : K} (hε : ε ^ (p ^ f) * ε = 1)
    (hε2 : ε * ε ≠ 1) : bJ h hq ≠ 1 := by
  intro h1
  have e := congrArg (fun φ : MulAut (Su K p f 2) =>
    (((φ (diagEl h hε) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  simp only [MulAut.one_apply] at e
  rw [coe_bJ, coe_diagEl] at e
  apply hε2
  simp [J2, J2', Matrix.mul_apply, Fin.sum_univ_two] at e
  rw [e] at hε
  exact hε

theorem aYbJ_ne_one (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) {ε : K} (hε : ε ^ (p ^ f) * ε = 1)
    (hε2 : ε * ε ≠ 1) : aY h hq * bJ h hq ≠ 1 := by
  intro h1
  have e := congrArg (fun φ : MulAut (Su K p f 2) =>
    (((φ (diagEl h hε) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  simp only [MulAut.one_apply, MulAut.mul_apply] at e
  rw [coe_aY, coe_bJ, coe_diagEl] at e
  apply hε2
  simp [Y2_eq, J2, J2', Matrix.mul_apply, Fin.sum_univ_two] at e
  rw [e] at hε
  exact hε


theorem aY_not_inner (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    (h : UnitaryFieldData p f K) (hq : Odd (p ^ f)) (h2 : (2 : K) ≠ 0) (s : Su K p f 2) :
    MulAut.conj s ≠ aY h hq := by
  have h5 := GenLocU4ExtCore.five_le_of_mod_four hK hq4
  refine GenLocU4Gen.conj_ne_of_det hK hp2 (by omega) Ygl (Y2_unitary hq) (aY h hq) ?_ ?_ s
  · intro g
    rw [coe_aY]
    rfl
  · intro lam hlam
    have hdet : ((Ygl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = -1 := by
      simp [Ygl, Y2, Matrix.det_diagonal]
    rw [hdet]
    intro hsq
    exact GenLocU4ExtMu.not_isSqM_neg_one hq4 h2 ⟨lam, by rw [pow_succ]; exact hlam, hsq⟩


theorem su2_gen_of_three
    (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq4 : p ^ f % 4 = 1)
    {G : Type} [Group G] (φ : Su K p f 2 →* G) (Γ : Subgroup G)
    (hI : ∀ x : Su K p f 2, Y2 * ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Y2 → φ x ∈ Γ)
    (hII : ∀ x : Su K p f 2, ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)) =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) → φ x ∈ Γ)
    (hIII : ∀ x : Su K p f 2, Y2 * (((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f))) * Y2 =
      ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) → φ x ∈ Γ) :
    ∀ x, φ x ∈ Γ := by
  have hp : p.Prime := Fact.out
  have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h5 := GenLocU4ExtCore.five_le_of_mod_four hK hq4
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  obtain ⟨ε, hε, hε2⟩ := GenLocU4Gen.exists_unit_scalar_sq_ne_one hK (by omega : 3 ≤ p ^ f)
  have haa := aY_sq h hq
  have hbb := bJ_sq h hq
  have hab := aY_bJ_comm h hq
  have ha1 := aY_ne_one h hq h2
  have hb1 := bJ_ne_one h hq hε hε2
  have hab1 := aYbJ_ne_one h hq hε hε2
  have hne : aY h hq ≠ bJ h hq := fun he => hab1 (by rw [← he]; exact haa)
  let V : Subgroup (MulAut (Su K p f 2)) := FourGroup.kleinFourOf (aY h hq) (bJ h hq) haa hbb hab
  have hVea : CFSG.IsElementaryAbelian 2 ↥V := FourGroup.isElementaryAbelian_kleinFourOf
  have hVcard : Nat.card ↥V = 4 := FourGroup.card_kleinFourOf ha1 hb1 hne
  have hrank : pRank 2 ↥V = 2 := by
    have h1 := GenLocBasic.card_eq_two_pow_pRank_type hVea
    rw [hVcard] at h1
    exact (Nat.pow_right_injective (le_refl 2) (by simpa using h1.symm : 2 ^ pRank 2 ↥V = 2 ^ 2))
  let β : ↥V →* MulAut (Su K p f 2) := V.subtype
  have haV : aY h hq ∈ V := FourGroup.left_mem_kleinFourOf
  have hmix : ¬ β.range ≤ (MulAut.conj : Su K p f 2 →* MulAut (Su K p f 2)).range := by
    intro hle
    obtain ⟨s, hs⟩ := hle ⟨⟨aY h hq, haV⟩, rfl⟩
    exact aY_not_inner hp2 hK hq4 h hq h2 s hs
  have hgam : gammaAct β = ⊤ :=
    GenLocU4Gen.gammaAct_su2_mixed_rank2 hp2 hK h5 ⟨hVea, Or.inl hrank⟩ hrank β (Or.inr hmix)
  have hnontriv : ∀ E : Subgroup ↥V, pRank 2 ↥V - 1 ≤ pRank 2 ↥E → ∃ e ∈ E, e ≠ 1 := by
    intro E hE
    have hidx := (GenLocBasic.adm_iff_index hVea E).1 hE
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
    rw [hbot, Subgroup.index_bot, hVcard] at hidx
    omega
  have hle : gammaAct β ≤ Γ.comap φ := by
    refine iSup₂_le fun E hE w0 hw0 => ?_
    have hw0' := (GenLocBasic.mem_fixedIn_map β E w0).1 hw0
    obtain ⟨e, heE, he1⟩ := hnontriv E hE
    have hfix : (e : MulAut (Su K p f 2)) w0 = w0 := hw0' e heE
    show φ w0 ∈ Γ
    set X : Matrix (Fin 2) (Fin 2) K := ((w0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) with hX
    have hbar : X.map (· ^ (p ^ f)) = J2 * X * J2' := GenLocU4Gen.su2_map_bar w0
    rcases FourGroup.mem_kleinFourOf.1 e.2 with h1 | h1 | h1 | h1
    · exact absurd (Subtype.ext h1) he1
    · rw [h1] at hfix
      refine hI w0 ?_
      have e1 := congrArg (fun w : Su K p f 2 => ((w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hfix
      simp only [coe_aY] at e1
      calc Y2 * X = Y2 * X * (Y2 * Y2) := by rw [Y2_mul, Matrix.mul_one]
        _ = (Y2 * X * Y2) * Y2 := by simp only [Matrix.mul_assoc]
        _ = X * Y2 := by rw [e1]
    · rw [h1] at hfix
      refine hII w0 ?_
      have e1 := congrArg (fun w : Su K p f 2 => ((w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hfix
      simp only [coe_bJ] at e1
      rw [hbar]
      exact e1
    · rw [h1] at hfix
      refine hIII w0 ?_
      have e1 := congrArg (fun w : Su K p f 2 => ((w : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) hfix
      simp only [MulAut.mul_apply, coe_aY, coe_bJ] at e1
      rw [hbar]
      exact e1
  intro x
  exact hle (hgam ▸ Subgroup.mem_top x)

end Auts

end GenLocU4Out

end CFSG.GH74.Generic.BProg.B2
