module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.PSUTwoAux.Outer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoCount

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryFrame CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

@[expose] noncomputable def basisUnitary (b : Fin n → Fin n → K) (hb : IsOrthonormalFamily h b) :
    primeFormUnitary h (idGram K n) :=
  ⟨⟨frameMat b, frameAdj h b, mul_eq_one_comm.mp (frameAdj_mul_frameMat hb),
    frameAdj_mul_frameMat hb⟩, by
    rw [mem_primeFormUnitary, idGram, Units.val_one, Matrix.mul_one]
    exact frameAdj_mul_frameMat hb⟩

theorem exists_diagonalize (hq : ℓ ^ f = 2) {M : primeFormUnitary h (idGram K n)}
    (hM : M ^ 3 = 1) :
    ∃ (T D : primeFormUnitary h (idGram K n)) (c : Fin n → K), M = T * D * T⁻¹ ∧
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal c := by
  classical
  obtain ⟨b, c, hb, hbc⟩ := exists_eigenbasis hq hM
  set T := basisUnitary b hb with hT
  have hMT : ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat b =
      frameMat b * Matrix.diagonal c := by
    ext i k
    have := congrFun (hbc k) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, frameMat, Matrix.of_apply, Matrix.diagonal_apply, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [this]
    ring
  refine ⟨T, T⁻¹ * M * T, c, by group, ?_⟩
  change frameAdj h b * ((M : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * frameMat b = _
  rw [Matrix.mul_assoc, hMT, ← Matrix.mul_assoc, frameAdj_mul_frameMat hb, Matrix.one_mul]

theorem pow_three_eq_one_of_commute_order_eleven (hq : ℓ ^ f = 2)
    {g M : primeFormUnitary h (idGram K 6)} (hgM : g * M = M * g) (hg : g ^ 11 = 1) (hg1 : g ≠ 1)
    {c₀ : Kˣ} (hM3 : (M : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c₀) :
    M ^ 3 = 1 := by
  classical
  have hfin := h.finite
  have hK : Nat.card K = 4 := CFSG.HardMathSupport.Timmesfeld.CrossChar.card_eq_four h hq
  set gm : Matrix (Fin 6) (Fin 6) K := ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hgm
  set Mm : Matrix (Fin 6) (Fin 6) K := ((M : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hMm
  have hg11 : gm ^ 11 = 1 := by
    have := congrArg (fun x : primeFormUnitary h (idGram K 6) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hg
    simpa [gm, Units.val_pow_eq_pow_val] using this
  have hgne : gm ≠ 1 := by
    intro h1
    apply hg1
    apply Subtype.ext
    apply Units.ext
    simpa [gm] using h1
  have hcomm : gm * Mm = Mm * gm := by
    have := congrArg (fun x : primeFormUnitary h (idGram K 6) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hgM
    simpa [gm, Mm] using this
  obtain ⟨F, hFmem, hFdim⟩ := finrank_fixed_eq_one hK gm hg11 hgne
  have hFM : ∀ v ∈ F, Mm *ᵥ v ∈ F := by
    intro v hv
    rw [hFmem] at hv ⊢
    rw [mulVec_mulVec, hcomm, ← mulVec_mulVec, hv]
  obtain ⟨v₀, hv₀ne, hv₀⟩ := finrank_eq_one_iff'.1 hFdim
  obtain ⟨μ, hμ⟩ := hv₀ ⟨Mm *ᵥ (v₀ : Fin 6 → K), hFM v₀ v₀.2⟩
  have hMv : Mm *ᵥ (v₀ : Fin 6 → K) = μ • (v₀ : Fin 6 → K) := by
    have := congrArg Subtype.val hμ
    exact this.symm
  have hv₀ne' : (v₀ : Fin 6 → K) ≠ 0 := fun h0 => hv₀ne (Subtype.ext h0)
  have hMinj : Function.Injective Mm.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (M : GL (Fin 6) K).isUnit
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hv₀ne'
    apply hMinj
    rw [hMv, zero_smul, mulVec_zero]
  have hμ3 : μ ^ 3 = 1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.pow_three_eq_one h hq hμ0
  have hMpow : ∀ k : ℕ, (Mm ^ k) *ᵥ (v₀ : Fin 6 → K) = μ ^ k • (v₀ : Fin 6 → K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hMv, smul_smul, pow_succ]
  have hM3m : Mm ^ 3 = (c₀ : K) • (1 : Matrix (Fin 6) (Fin 6) K) := by
    have := congrArg (fun x : GL (Fin 6) K => (x : Matrix (Fin 6) (Fin 6) K)) hM3
    simpa [Mm, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar, scalar_apply,
      Matrix.smul_one_eq_diagonal] using this
  have hc₀ : (c₀ : K) = 1 := by
    have h1 := hMpow 3
    rw [hM3m, smul_mulVec, one_mulVec, hμ3, one_smul] at h1
    have h2 : ((c₀ : K) - 1) • (v₀ : Fin 6 → K) = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hv₀ne'
  apply Subtype.ext
  rw [Subgroup.coe_pow, hM3, show c₀ = 1 from Units.ext hc₀, map_one]
  rfl

@[expose] def coordSub (c : Fin n → K) (a : K) : Submodule K (Fin n → K) where
  carrier := {v | ∀ i, c i ≠ a → v i = 0}
  add_mem' := fun {u v} hu hv i hi => by simp [hu i hi, hv i hi]
  zero_mem' := fun i _ => rfl
  smul_mem' := fun r v hv i hi => by simp [hv i hi]

theorem finrank_coordSub [Finite K] [DecidableEq K] (hK : Nat.card K = 4) (c : Fin n → K) (a : K) :
    Module.finrank K (coordSub c a) = Fintype.card {i // c i = a} := by
  classical
  have e : coordSub c a ≃ ({i // c i = a} → K) :=
    { toFun := fun v i => v.1 i.1
      invFun := fun w => ⟨fun j => if h : c j = a then w ⟨j, h⟩ else 0, fun i hi => by simp [hi]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext j
        by_cases h : c j = a
        · simp [h]
        · simp [h, v.2 j h]
      right_inv := fun w => by
        funext i
        simp [i.2] }
  have h1 : Nat.card (coordSub c a) = 4 ^ Module.finrank K (coordSub c a) :=
    natCard_submodule hK _
  have h2 : Nat.card ({i // c i = a} → K) = 4 ^ Fintype.card {i // c i = a} := by
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card]
  rw [Nat.card_congr e, h2] at h1
  exact (Nat.pow_right_injective (by norm_num) h1).symm

theorem entry_eq_zero_of_commute_diagonal {c : Fin n → K} {X : Matrix (Fin n) (Fin n) K}
    (hX : X * Matrix.diagonal c = Matrix.diagonal c * X) {i j : Fin n} (hij : c i ≠ c j) :
    X i j = 0 := by
  have h1 := congrFun (congrFun hX i) j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, ite_mul, zero_mul, Finset.sum_ite_eq'] at h1
  have h2 : X i j * (c j - c i) = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hij

theorem mulVec_mem_coordSub {c : Fin n → K} {X : Matrix (Fin n) (Fin n) K}
    (hX : X * Matrix.diagonal c = Matrix.diagonal c * X) (a : K) {v : Fin n → K}
    (hv : v ∈ coordSub c a) : X *ᵥ v ∈ coordSub c a := by
  intro i hi
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : c j = a
  · rw [entry_eq_zero_of_commute_diagonal hX (by rw [hj]; exact hi), zero_mul]
  · rw [hv j hj, mul_zero]

theorem exists_diag_form [DecidableEq K] (hq : ℓ ^ f = 2)
    {g M : primeFormUnitary h (idGram K 6)} (hgM : g * M = M * g) (hg : g ^ 11 = 1) (hg1 : g ≠ 1)
    {c₀ : Kˣ} (hM3 : (M : GL (Fin 6) K) ^ 3 = GeneralLinearGroup.scalar (Fin 6) c₀)
    (hMs : ∀ c : Kˣ, (M : GL (Fin 6) K) ≠ GeneralLinearGroup.scalar (Fin 6) c) :
    ∃ (T D : primeFormUnitary h (idGram K 6)) (i₀ : Fin 6) (ν μ : K), ν ≠ μ ∧ M = T * D * T⁻¹ ∧
      ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        Matrix.diagonal (fun i => if i = i₀ then μ else ν) := by
  classical
  have hfin := h.finite
  have hK : Nat.card K = 4 := CFSG.HardMathSupport.Timmesfeld.CrossChar.card_eq_four h hq
  have hM3' : M ^ 3 = 1 := pow_three_eq_one_of_commute_order_eleven hq hgM hg hg1 hM3
  obtain ⟨T, D, c, hMTD, hDmat⟩ := exists_diagonalize hq hM3'
  set gt : primeFormUnitary h (idGram K 6) := T⁻¹ * g * T with hgt
  have hgtD : gt * D = D * gt := by
    have h1 : g * (T * D * T⁻¹) = (T * D * T⁻¹) * g := by rw [← hMTD]; exact hgM
    calc gt * D = T⁻¹ * (g * (T * D * T⁻¹)) * T := by rw [hgt]; group
      _ = T⁻¹ * ((T * D * T⁻¹) * g) * T := by rw [h1]
      _ = D * gt := by rw [hgt]; group
  have hgt11 : gt ^ 11 = 1 := by
    have : gt ^ 11 = T⁻¹ * g ^ 11 * T⁻¹⁻¹ := by
      rw [hgt, show T⁻¹ * g * T = T⁻¹ * g * T⁻¹⁻¹ by rw [inv_inv], conj_pow]
    rw [this, hg]; group
  have hgt1 : gt ≠ 1 := by
    intro h1
    apply hg1
    have : g = T * gt * T⁻¹ := by rw [hgt]; group
    rw [this, h1]; group
  set Gt : Matrix (Fin 6) (Fin 6) K := ((gt : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hGt
  have hGtcomm : Gt * Matrix.diagonal c = Matrix.diagonal c * Gt := by
    rw [← hDmat]
    have := congrArg (fun x : primeFormUnitary h (idGram K 6) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hgtD
    simpa [Gt] using this
  have hGt11 : Gt ^ 11 = 1 := by
    have := congrArg (fun x : primeFormUnitary h (idGram K 6) =>
      ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hgt11
    simpa [Gt, Units.val_pow_eq_pow_val] using this
  have hGt1 : Gt ≠ 1 := by
    intro h1
    apply hgt1
    apply Subtype.ext
    apply Units.ext
    simpa [Gt] using h1
  obtain ⟨j, hj⟩ : ∃ j, Gt *ᵥ Pi.single j (1 : K) ≠ Pi.single j 1 := by
    by_contra hcon
    push Not at hcon
    apply hGt1
    ext i k
    have := congrFun (hcon k) i
    simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  set a := c j with ha
  have hmem : (Pi.single j (1 : K) : Fin 6 → K) ∈ coordSub c a := by
    intro i hi
    have : i ≠ j := fun h' => hi (by rw [h'])
    simp [Pi.single_apply, this]
  have hm : Module.finrank K (coordSub c a) ≤ 6 := by
    have := Submodule.finrank_le (coordSub c a)
    simpa [Module.finrank_fin_fun] using this
  have h5 := five_le_finrank_of_ne hK Gt hGt11 (coordSub c a)
    (fun v hv => mulVec_mem_coordSub hGtcomm a hv) hm ⟨_, hmem, hj⟩
  rw [finrank_coordSub hK c a] at h5
  have hle : Fintype.card {i // c i = a} ≤ 6 := by
    simpa using Fintype.card_subtype_le (fun i : Fin 6 => c i = a)
  have hne6 : Fintype.card {i // c i = a} ≠ 6 := by
    intro h6
    have hall : ∀ i, c i = a := by
      by_contra hcon
      push Not at hcon
      obtain ⟨i, hi⟩ := hcon
      have := Fintype.card_subtype_lt (p := fun i : Fin 6 => c i = a) hi
      simp at this
      omega
    have ha0 : a ≠ 0 := by
      intro h0
      have hD0 : ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 0 := by
        rw [hDmat]
        ext i k
        simp [Matrix.diagonal_apply, hall i, h0]
      have hu : IsUnit ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := (D : GL (Fin 6) K).isUnit
      rw [hD0] at hu
      exact not_isUnit_zero hu
    apply hMs (Units.mk0 a ha0)
    have hDs : (D : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) (Units.mk0 a ha0) := by
      apply Units.ext
      rw [hDmat, CFSG.HardMathSupport.Timmesfeld.CrossChar.scalar_coe_eq_smul_one,
        Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      exact hall i
    have hMg : (M : GL (Fin 6) K) =
        (T : GL (Fin 6) K) * (D : GL (Fin 6) K) * (T : GL (Fin 6) K)⁻¹ :=
      congrArg Subtype.val hMTD
    rw [hMg, hDs, ← GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]
  have h5' : Fintype.card {i // c i = a} = 5 := by omega
  have hcompl : Fintype.card {i // ¬ c i = a} = 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, h5']
  obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.1 hcompl
  have hother : ∀ i, i ≠ i₀ → c i = a := by
    intro i hi
    by_contra hcon
    exact hi (congrArg Subtype.val (huniq ⟨i, hcon⟩))
  refine ⟨T, D, i₀, a, c i₀, fun hh => hi₀ hh.symm, hMTD, ?_⟩
  rw [hDmat]
  congr 1
  funext i
  by_cases hi : i = i₀
  · simp [hi]
  · simp [hi, hother i hi]

end CFSG.HardMathSupport.Dickson.Sec6.I923
