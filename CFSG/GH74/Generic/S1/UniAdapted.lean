module

public import CFSG.GH74.Generic.S1.UniDescent
public import CFSG.GH74.Generic.S1.UniForms

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem cT_fromBlocks (h : UnitaryFieldData p f F) {m n : Type}
    (A : Matrix m m F) (B : Matrix m n F) (C : Matrix n m F) (D : Matrix n n F) :
    cT h (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (cT h A) (cT h C) (cT h B) (cT h D) := by
  simp [cT, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem adapted_sym (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) {g : GL (Fin 4) F}
    (hu : cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1)
    (hgg : (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F).map h.bar = 1)
    (hsq : ∃ u : F, u ^ (p ^ f + 1) = 1 ∧ u * u = (g : Matrix (Fin 4) (Fin 4) F).det) :
    ∃ P : GL (Fin 4) F, cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat ∧
      (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F).map h.bar =
        (P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) ((1 : F) • 1) := by
  classical
  have hfinF : Finite F := h.finite
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨P₀, hdet₀, hP₀⟩ := exists_fixed_basis h h2 hgg
  have hu1 : cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) =
      (1 : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by rw [one_smul]; exact hu
  obtain ⟨hbar, hsym⟩ := gram_bar h (Or.inl rfl) hu1 hP₀
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 4) (Fin 4) F, S₀ = cT h P₀ * P₀ := ⟨_, rfl⟩
  rw [← hS₀] at hbar hsym
  have hbar' : S₀.map h.bar = S₀ := by rw [hbar, one_smul]
  have hsym' : S₀ᵀ = S₀ := by rw [hsym, one_smul]
  obtain ⟨S', hS'⟩ := exists_fixedField_matrix h hbar'
  have hι : Function.Injective h.fixedField.subtype := Subtype.val_injective
  have hS'sym : S'ᵀ = S' := by
    apply Matrix.map_injective hι
    show S'ᵀ.map h.fixedField.subtype = S'.map h.fixedField.subtype
    rw [Matrix.transpose_map, hS', hsym']
  have hdetS : S₀.det ≠ 0 := by
    have hdetcT : (cT h P₀).det = h.bar P₀.det := by
      rw [cT, Matrix.det_transpose]
      exact (RingHom.map_det (h.bar : F →+* F) P₀).symm
    rw [hS₀, Matrix.det_mul, hdetcT]
    exact mul_ne_zero ((map_ne_zero h.bar).2 hdet₀.ne_zero) hdet₀.ne_zero
  have hdetι : h.fixedField.subtype S'.det = S₀.det := by
    have := RingHom.map_det h.fixedField.subtype S'
    rw [RingHom.mapMatrix_apply, hS'] at this
    exact this
  have hdetS' : S'.det ≠ 0 := by
    intro h0
    apply hdetS
    rw [← hdetι, h0, map_zero]
  obtain ⟨s₀, hs₀⟩ := det_gram_square h hP₀ hsq
  rw [← hS₀] at hs₀
  have hsq' : IsSquare S'.det := ⟨s₀, hι (by rw [hdetι, map_mul]; exact hs₀.symm)⟩
  have hodd : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact (h.prime.odd_of_ne_two hp2).pow
  have : Finite h.fixedField := inferInstance
  obtain ⟨N', hN'⟩ := exists_hyp_conj hodd hS'sym hdetS' hsq'
  let Nm : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := N'.map h.fixedField.subtype
  have hNmbar : Nm.map h.bar = Nm := map_fixedField_bar h N'
  have hcTNm : cT h Nm = Nmᵀ := by rw [cT, hNmbar]
  let P' : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := P₀ * Nm
  have hG : cT h P' * P' = Matrix.fromBlocks 0 1 1 0 := by
    have e1 : cT h P' * P' = Nmᵀ * S₀ * Nm := by
      rw [show P' = P₀ * Nm from rfl, cT_mul, hcTNm, hS₀]
      simp only [Matrix.mul_assoc]
    rw [e1, ← hS']
    have e2 : (N'ᵀ * S' * N').map h.fixedField.subtype = Matrix.fromBlocks 0 1 1 0 := by
      rw [hN']
      simp [Matrix.fromBlocks_map]
    rw [← e2]
    simp only [Matrix.map_mul, Matrix.transpose_map, Nm]
  let Qd : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    Matrix.fromBlocks 1 0 0 ((1 : F) • (1 : Matrix (Fin 2) (Fin 2) F))
  have hQd : Qd = 1 := by simp [Qd, Matrix.fromBlocks_one]
  have hg : (g : Matrix (Fin 4) (Fin 4) F) * P'.map h.bar = P' * Qd := by
    rw [hQd, Matrix.mul_one, show P' = P₀ * Nm from rfl, Matrix.map_mul, hNmbar,
      ← Matrix.mul_assoc, hP₀]
  obtain ⟨P, hP1, hP2⟩ := adapted_finish h P' hG hg
  exact ⟨P, hP1, hP2⟩

theorem adapted_skew (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) {g : GL (Fin 4) F}
    (hu : cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1)
    (hgg : (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F).map h.bar =
      (-1 : F) • 1) :
    ∃ (P : GL (Fin 4) F) (s : F), s ≠ 0 ∧
      cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat ∧
      (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F).map h.bar =
        s • ((P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) ((-1 : F) • 1)) := by
  classical
  have hfinF : Finite F := h.finite
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  have hm1F : (-1 : F) ∈ h.fixedField := h.mem_fixedField.mpr (by simp)
  have hne : (⟨-1, hm1F⟩ : h.fixedField) ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    simp at this
  obtain ⟨b, hb⟩ := (unitary_field_norm h).2.1 (Units.mk0 _ hne)
  have hbN : h.norm (b : F) = -1 :=
    congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : F)) hb
  have hb0 : (b : F) ≠ 0 := b.ne_zero
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : Matrix (Fin 4) (Fin 4) F, g₁ = (b : F) • (g : Matrix (Fin 4) (Fin 4) F) :=
    ⟨_, rfl⟩
  have hmapsmul : ∀ (x : F) (M : Matrix (Fin 4) (Fin 4) F), (x • M).map h.bar = h.bar x • M.map h.bar :=
    fun x M => by ext i j; simp
  have hg₁g₁ : g₁ * g₁.map h.bar = 1 := by
    rw [hg₁, hmapsmul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgg, smul_smul]
    have : (b : F) * h.bar (b : F) * (-1) = 1 := by
      rw [show (b : F) * h.bar (b : F) = h.norm (b : F) from rfl, hbN]; norm_num
    rw [this, one_smul]
  have hug₁ : cT h g₁ * g₁ = (-1 : F) • (1 : Matrix (Fin 4) (Fin 4) F) := by
    rw [hg₁, cT_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hu]
    have : h.bar (b : F) * (b : F) = -1 := by
      rw [mul_comm (h.bar (b : F)), show (b : F) * h.bar (b : F) = h.norm (b : F) from rfl, hbN]
    rw [this]
  obtain ⟨P₀, hdet₀, hP₀⟩ := exists_fixed_basis h h2 hg₁g₁
  obtain ⟨hbar, hsym⟩ := gram_bar h (Or.inr rfl) hug₁ hP₀
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Matrix (Fin 4) (Fin 4) F, S₀ = cT h P₀ * P₀ := ⟨_, rfl⟩
  rw [← hS₀] at hbar hsym
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have ht0 : c₀ - h.bar c₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc₀)
  obtain ⟨t, htdef⟩ : ∃ t : F, t = c₀ - h.bar c₀ := ⟨_, rfl⟩
  rw [← htdef] at ht0
  have hbt : h.bar t = -t := by rw [htdef, map_sub, h.bar_bar, neg_sub]
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Matrix (Fin 4) (Fin 4) F, A₀ = t⁻¹ • S₀ := ⟨_, rfl⟩
  have hA₀bar : A₀.map h.bar = A₀ := by
    rw [hA₀, hmapsmul, hbar, map_inv₀, hbt, smul_smul, inv_neg, neg_mul_neg, mul_one]
  have hA₀sym : A₀ᵀ = -A₀ := by
    rw [hA₀, Matrix.transpose_smul, hsym, smul_smul, mul_neg_one, neg_smul]
  have hι : Function.Injective h.fixedField.subtype := Subtype.val_injective
  obtain ⟨A', hA'⟩ := exists_fixedField_matrix h hA₀bar
  have hA'sym : A'ᵀ = -A' := by
    apply Matrix.map_injective hι
    show A'ᵀ.map h.fixedField.subtype = (-A').map h.fixedField.subtype
    rw [Matrix.transpose_map, hA', hA₀sym]
    ext i j
    simp [← hA']
  have hdetA : A₀.det ≠ 0 := by
    have hdetcT : (cT h P₀).det = h.bar P₀.det := by
      rw [cT, Matrix.det_transpose]
      exact (RingHom.map_det (h.bar : F →+* F) P₀).symm
    rw [hA₀, Matrix.det_smul, hS₀, Matrix.det_mul, hdetcT]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ht0))
      (mul_ne_zero ((map_ne_zero h.bar).2 hdet₀.ne_zero) hdet₀.ne_zero)
  have hdetA' : A'.det ≠ 0 := by
    intro h0
    apply hdetA
    have := RingHom.map_det h.fixedField.subtype A'
    rw [h0, map_zero, RingHom.mapMatrix_apply, hA'] at this
    exact this.symm
  have h2K : (2 : h.fixedField) ≠ 0 := by
    intro h0
    apply h2
    exact congrArg Subtype.val h0
  obtain ⟨N', hN'⟩ := exists_alt_conj h2K hA'sym hdetA'
  let Nm : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := N'.map h.fixedField.subtype
  have hNmbar : Nm.map h.bar = Nm := map_fixedField_bar h N'
  have hcTNm : cT h Nm = Nmᵀ := by rw [cT, hNmbar]
  let P'' : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := P₀ * Nm
  have hG'' : cT h P'' * P'' = Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) F)
      (-(t • (1 : Matrix (Fin 2) (Fin 2) F))) (t • 1) 0 := by
    have e1 : cT h P'' * P'' = Nmᵀ * S₀ * Nm := by
      rw [show P'' = P₀ * Nm from rfl, cT_mul, hcTNm, hS₀]
      simp only [Matrix.mul_assoc]
    have hS₀t : S₀ = t • A₀ := by rw [hA₀, smul_smul, mul_inv_cancel₀ ht0, one_smul]
    have e2 : Nmᵀ * A₀ * Nm = Matrix.fromBlocks 0 (-1) 1 0 := by
      have : (N'ᵀ * A' * N').map h.fixedField.subtype = Matrix.fromBlocks 0 (-1) 1 0 := by
        rw [hN']
        ext (i | i) (j | j) <;> simp [Matrix.one_apply] <;> split_ifs <;> simp
      rw [← this, ← hA']
      simp only [Matrix.map_mul, Matrix.transpose_map, Nm]
    rw [e1, hS₀t, Matrix.mul_smul, Matrix.smul_mul, e2, Matrix.fromBlocks_smul]
    congr 1 <;> simp
  obtain ⟨x, hx⟩ : ∃ x : F, x = -t⁻¹ := ⟨_, rfl⟩
  have hbx : h.bar x = t⁻¹ := by rw [hx, map_neg, map_inv₀, hbt, inv_neg, neg_neg]
  let Dsc : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    Matrix.fromBlocks 1 0 0 (x • (1 : Matrix (Fin 2) (Fin 2) F))
  let Qd : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    Matrix.fromBlocks 1 0 0 ((-1 : F) • (1 : Matrix (Fin 2) (Fin 2) F))
  let P' : Matrix (Fin 4) (Fin 2 ⊕ Fin 2) F := P'' * Dsc
  have hcTDsc : cT h Dsc = Matrix.fromBlocks 1 0 0 (t⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    simp only [Dsc]
    rw [cT_fromBlocks, cT_one, cT_zero, cT_smul, cT_one, hbx]
  have hG : cT h P' * P' = Matrix.fromBlocks 0 1 1 0 := by
    have e1 : cT h P' * P' = cT h Dsc * (cT h P'' * P'') * Dsc := by
      rw [show P' = P'' * Dsc from rfl, cT_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hG'', hcTDsc]
    simp only [Dsc]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    have hxt : x * t = -1 := by rw [hx]; field_simp
    have htt' : t * t⁻¹ = 1 := mul_inv_cancel₀ ht0
    congr 1
    · simp
    · simp [smul_smul, hxt]
    · simp [smul_smul, htt']
    · simp
  have hDsc : Dsc.map h.bar = Dsc * Qd := by
    simp only [Dsc, Qd]
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_multiply]
    have hmaps2 : ∀ (y : F) , ((y • (1 : Matrix (Fin 2) (Fin 2) F)).map h.bar) =
        h.bar y • (1 : Matrix (Fin 2) (Fin 2) F) := fun y => by ext i j; simp [Matrix.one_apply]; split_ifs <;> simp
    have h1m : (1 : Matrix (Fin 2) (Fin 2) F).map h.bar = 1 :=
      Matrix.map_one _ (map_zero h.bar) (map_one h.bar)
    have h0m : (0 : Matrix (Fin 2) (Fin 2) F).map h.bar = 0 :=
      Matrix.map_zero _ (map_zero h.bar)
    have hnx : x * -1 = t⁻¹ := by rw [hx]; ring
    rw [h1m, h0m, hmaps2, hbx]
    congr 1
    · simp
    · simp
    · simp
    · simp
      rw [hx]; simp
  have hg : g₁ * P'.map h.bar = P' * Qd := by
    rw [show P' = P'' * Dsc from rfl, Matrix.map_mul, show P'' = P₀ * Nm from rfl, Matrix.map_mul,
      hNmbar, hDsc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP₀]
  obtain ⟨P, hP1, hP2⟩ := adapted_finish h P' hG hg
  refine ⟨P, (b : F)⁻¹, inv_ne_zero hb0, hP1, ?_⟩
  have hgb : (g : Matrix (Fin 4) (Fin 4) F) = (b : F)⁻¹ • g₁ := by
    rw [hg₁, smul_smul, inv_mul_cancel₀ hb0, one_smul]
  rw [hgb, Matrix.smul_mul, hP2]

end CFSG.GH74.Generic.S1.Uni
