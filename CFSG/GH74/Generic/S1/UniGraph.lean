module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace
public import CFSG.GH74.Generic.S1.UniPaired

public section

namespace CFSG.GH74.Generic.S1.Uni

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F]

theorem commutant_scalar (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) {S : Matrix (Fin 4) (Fin 4) F}
    (hS : ∀ m : GL (Fin 4) F, m ∈ StatedSU 4 (p ^ f) F →
      S * (m : Matrix (Fin 4) (Fin 4) F) = (m : Matrix (Fin 4) (Fin 4) F) * S) :
    ∃ a : F, S = a • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨c, hcN, hck⟩ := exists_norm_one_not_fixed h hp2
  let X : (Fin 4 → F) →ₗ[h.fixedField] (Fin 4 → F) :=
    (Matrix.mulVecLin S).restrictScalars h.fixedField
  have hmem : ∀ M : GL (Fin 4) F, M ∈ gramSU h (1 : Matrix (Fin 4) (Fin 4) F) →
      ∀ u, X ((M : Matrix (Fin 4) (Fin 4) F) *ᵥ u) = (M : Matrix (Fin 4) (Fin 4) F) *ᵥ X u := by
    intro M hM u
    have hM' : M ∈ StatedSU 4 (p ^ f) F := by
      rw [show StatedSU 4 (p ^ f) F = unitarySU p f F 4 from rfl, unitarySU_eq_gramSU h]
      exact hM
    change S *ᵥ ((M : Matrix (Fin 4) (Fin 4) F) *ᵥ u) =
      (M : Matrix (Fin 4) (Fin 4) F) *ᵥ (S *ᵥ u)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS M hM']
  obtain ⟨a, ha⟩ := coordinate_commutant_scalar h h2 (by norm_num) hcN hck X
    (fun i l hil u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignDiag_mem h hil
      have := hmem M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitLambdaDiag_mem h hcN hij
      have := hmem M hMmem u
      rwa [hM] at this)
    (fun i j hij u => by
      obtain ⟨M, hM, hMmem⟩ := unitSignedSwapMatrix_mem h hij
      have := hmem M hMmem u
      rwa [hM] at this)
  refine ⟨a, Matrix.ext_iff_mulVec.2 fun v => ?_⟩
  have h1 : S *ᵥ v = a • v := ha v
  rw [h1]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.one_apply]

theorem map_bar_mem (h : UnitaryFieldData p f F) {m : GL (Fin 4) F}
    (hm : m ∈ StatedSU 4 (p ^ f) F) :
    Matrix.GeneralLinearGroup.map (h.bar : F →+* F) m ∈ StatedSU 4 (p ^ f) F := by
  rw [show StatedSU 4 (p ^ f) F = unitarySU p f F 4 from rfl, mem_unitarySU_iff h] at hm ⊢
  obtain ⟨hdet, hu⟩ := hm
  have hmv : ((Matrix.GeneralLinearGroup.map (h.bar : F →+* F) m : GL (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F) = (m : Matrix (Fin 4) (Fin 4) F).map h.bar := rfl
  refine ⟨?_, ?_⟩
  · rw [hmv]
    have := RingHom.map_det (h.bar : F →+* F) (m : Matrix (Fin 4) (Fin 4) F)
    rw [hdet, map_one] at this
    exact this.symm
  · rw [hmv, map_bar_bar]
    have := congrArg Matrix.transpose hu
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this

theorem inv_val_of_unitary (h : UnitaryFieldData p f F) {m : GL (Fin 4) F}
    (hu : cT h (m : Matrix (Fin 4) (Fin 4) F) * (m : Matrix (Fin 4) (Fin 4) F) = 1) :
    ((m⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = cT h (m : Matrix (Fin 4) (Fin 4) F) :=
  Units.inv_eq_of_mul_eq_one_left hu


theorem gram_comm (h : UnitaryFieldData p f F) (α : MulAut ↥(StatedSU 4 (p ^ f) F))
    {g : GL (Fin 4) F}
    (hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g⁻¹)
    (m : GL (Fin 4) F) (hm : m ∈ StatedSU 4 (p ^ f) F) :
    (cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) *
        (m : Matrix (Fin 4) (Fin 4) F) =
      (m : Matrix (Fin 4) (Fin 4) F) *
        (cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) := by
  set S : Matrix (Fin 4) (Fin 4) F := cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)
    with hS
  have hmu : cT h (m : Matrix (Fin 4) (Fin 4) F) * (m : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have := ((mem_unitarySU_iff h).1 hm).2
    exact this
  have hmi : ((m⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = cT h (m : Matrix (Fin 4) (Fin 4) F) :=
    inv_val_of_unitary h hmu
  have hmi_mem : m⁻¹ ∈ StatedSU 4 (p ^ f) F := inv_mem hm
  let kk : ↥(StatedSU 4 (p ^ f) F) :=
    ⟨Matrix.GeneralLinearGroup.map (h.bar : F →+* F) m⁻¹, map_bar_mem h hmi_mem⟩
  have h1 := hαg kk
  have hmm : Matrix.GeneralLinearGroup.map (h.bar : F →+* F)
      (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) m⁻¹) = m⁻¹ := by
    apply Units.ext
    exact map_bar_bar h _
  have h2 : ((α kk : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = g * m⁻¹ * g⁻¹ := by
    rw [h1]
    change g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F)
      (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) m⁻¹) * g⁻¹ = _
    rw [hmm]
  have h3 := ((mem_unitarySU_iff h).1 (α kk).2).2
  rw [h2] at h3
  rw [Units.val_mul, Units.val_mul, ← cT_def h, cT_mul, cT_mul, hmi, cT_cT] at h3
  have hgg : cT h (g : Matrix (Fin 4) (Fin 4) F) * cT h ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← cT_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, cT_one]
  have hgg' : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h4 : (m : Matrix (Fin 4) (Fin 4) F) * S * cT h (m : Matrix (Fin 4) (Fin 4) F) = S := by
    calc (m : Matrix (Fin 4) (Fin 4) F) * S * cT h (m : Matrix (Fin 4) (Fin 4) F)
        = (cT h (g : Matrix (Fin 4) (Fin 4) F) *
            cT h ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) *
          (m : Matrix (Fin 4) (Fin 4) F) * S * cT h (m : Matrix (Fin 4) (Fin 4) F) *
            (((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F)) := by
          rw [hgg, hgg']; simp
      _ = cT h (g : Matrix (Fin 4) (Fin 4) F) *
            (cT h ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
              ((m : Matrix (Fin 4) (Fin 4) F) * cT h (g : Matrix (Fin 4) (Fin 4) F)) *
                ((g : Matrix (Fin 4) (Fin 4) F) * cT h (m : Matrix (Fin 4) (Fin 4) F) *
                  ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) *
            (g : Matrix (Fin 4) (Fin 4) F) := by
          simp only [hS, Matrix.mul_assoc]
      _ = S := by rw [h3, Matrix.mul_one]
  calc S * (m : Matrix (Fin 4) (Fin 4) F)
      = ((m : Matrix (Fin 4) (Fin 4) F) * S * cT h (m : Matrix (Fin 4) (Fin 4) F)) *
          (m : Matrix (Fin 4) (Fin 4) F) := by rw [h4]
    _ = (m : Matrix (Fin 4) (Fin 4) F) * S * (cT h (m : Matrix (Fin 4) (Fin 4) F) *
          (m : Matrix (Fin 4) (Fin 4) F)) := by rw [Matrix.mul_assoc]
    _ = (m : Matrix (Fin 4) (Fin 4) F) * S := by rw [hmu, Matrix.mul_one]


theorem normalize_graph (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F)) {g : GL (Fin 4) F} {c : F}
    (hgc : (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F).map h.bar = c • 1)
    (hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g⁻¹) :
    ∃ (g' : GL (Fin 4) F) (ε : F), (ε = 1 ∨ ε = -1) ∧
      cT h (g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F) = 1 ∧
      (g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F).map h.bar = ε • 1 ∧
      (g' : Matrix (Fin 4) (Fin 4) F)ᵀ = ε • (g' : Matrix (Fin 4) (Fin 4) F) ∧
      ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
        g' * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g'⁻¹ := by
  classical
  have hfin : Finite F := h.finite
  obtain ⟨a, ha⟩ := commutant_scalar h hp2
    (S := cT h (g : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F))
    (fun m hm => gram_comm h α hαg m hm)
  have hdetg : (g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
  have hdetcT : ∀ M : Matrix (Fin 4) (Fin 4) F, (cT h M).det = h.bar M.det := fun M => by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : F →+* F) M).symm
  have ha0 : a ≠ 0 := by
    intro h0
    have := congrArg Matrix.det ha
    rw [Matrix.det_mul, hdetcT, h0] at this
    have h4 : (0 : F) • (1 : Matrix (Fin 4) (Fin 4) F) = 0 := zero_smul _ _
    rw [h4, Matrix.det_zero] at this
    exact mul_ne_zero ((map_ne_zero h.bar).2 hdetg) hdetg this
  have hbara : h.bar a = a := by
    have h1 : cT h (a • (1 : Matrix (Fin 4) (Fin 4) F)) = a • 1 := by
      rw [← ha, cT_mul, cT_cT]
    rw [cT_smul, cT_one] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simpa using h2
  have haF : a⁻¹ ∈ h.fixedField := h.mem_fixedField.mpr (by rw [map_inv₀, hbara])
  have hne : (⟨a⁻¹, haF⟩ : h.fixedField) ≠ 0 := fun h0 => inv_ne_zero ha0 (congrArg Subtype.val h0)
  obtain ⟨d, hd⟩ := (unitary_field_norm h).2.1 (Units.mk0 _ hne)
  have hdN : h.norm (d : F) = a⁻¹ :=
    congrArg (fun u : h.fixedFieldˣ => ((u : h.fixedField) : F)) hd
  have hdN' : h.bar (d : F) * (d : F) * a = 1 := by
    have : (d : F) * h.bar (d : F) * a = 1 := by
      rw [show (d : F) * h.bar (d : F) = h.norm (d : F) from rfl, hdN, inv_mul_cancel₀ ha0]
    rw [mul_comm (h.bar (d : F)), this]
  set g' : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) d * g with hg'
  have hg'v : (g' : Matrix (Fin 4) (Fin 4) F) = (d : F) • (g : Matrix (Fin 4) (Fin 4) F) := by
    rw [hg', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
  have hu : cT h (g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hg'v, cT_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha, smul_smul]
    rw [hdN', one_smul]
  have hαg' : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
        g' * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g'⁻¹ := by
    intro k
    rw [hαg k, hg']
    set x : GL (Fin 4) F := g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g⁻¹
      with hx
    have : Matrix.GeneralLinearGroup.scalar (Fin 4) d * g *
        Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) *
          (Matrix.GeneralLinearGroup.scalar (Fin 4) d * g)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin 4) d * x * (Matrix.GeneralLinearGroup.scalar (Fin 4) d)⁻¹ := by
      rw [hx]; group
    rw [this, Matrix.GeneralLinearGroup.scalar_commute d x, mul_inv_cancel_right]
  set lam : F := h.norm (d : F) * c with hlam
  have hmapsmul : ∀ (x : F) (M : Matrix (Fin 4) (Fin 4) F), (x • M).map h.bar = h.bar x • M.map h.bar :=
    fun x M => by ext i j; simp
  have hgg : (g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F).map h.bar =
      lam • 1 := by
    rw [hg'v, hmapsmul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hgc, smul_smul]
    rfl
  have hu' : (g' : Matrix (Fin 4) (Fin 4) F)ᵀ * (g' : Matrix (Fin 4) (Fin 4) F).map h.bar = 1 := by
    have := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M.map h.bar) hu
    simp only [cT, Matrix.map_mul, Matrix.transpose_map, map_bar_bar] at this
    rw [Matrix.map_one _ (map_zero h.bar) (map_one h.bar)] at this
    exact this
  have hdet1 : (g' : Matrix (Fin 4) (Fin 4) F).det * h.bar (g' : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    have := congrArg Matrix.det hu
    rw [Matrix.det_mul, hdetcT, Matrix.det_one, mul_comm] at this
    exact this
  have hlam4 : lam ^ 4 = 1 := by
    have := congrArg Matrix.det hgg
    rw [Matrix.det_mul, show ((g' : Matrix (Fin 4) (Fin 4) F).map h.bar).det =
      h.bar (g' : Matrix (Fin 4) (Fin 4) F).det from (RingHom.map_det (h.bar : F →+* F) _).symm,
      hdet1, Matrix.det_smul, Matrix.det_one] at this
    simpa using this.symm
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0] at hlam4
    norm_num at hlam4
  have hlamN : h.norm lam = 1 := by
    have hM : cT h ((g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F).map h.bar) *
        ((g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F).map h.bar) = 1 := by
      have e1 : cT h ((g' : Matrix (Fin 4) (Fin 4) F).map h.bar) =
          (g' : Matrix (Fin 4) (Fin 4) F)ᵀ := by
        rw [cT_def, map_bar_bar]
      rw [cT_mul, e1, Matrix.mul_assoc, ← Matrix.mul_assoc (cT h _) (g' : Matrix (Fin 4) (Fin 4) F),
        hu, Matrix.one_mul]
      exact hu'
    rw [hgg, cT_smul, cT_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one] at hM
    have h2 := congrFun (congrFun hM 0) 0
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
    rw [UnitaryFieldData.norm, mul_comm]
    exact h2
  have hlam : lam = 1 ∨ lam = -1 := by
    have hu1 : (Units.mk0 lam hlam0) = 1 ∨ (Units.mk0 lam hlam0) = -1 :=
      units_eq_one_or_neg_one_of_unitary hq4 (Units.mk0 lam hlam0)
        (Units.ext (by simpa using hlam4))
        (Units.ext (by
          have := h.norm_eq_pow lam
          rw [hlamN] at this
          simpa using this.symm))
    rcases hu1 with h1 | h1
    · exact Or.inl (by simpa using congrArg Units.val h1)
    · exact Or.inr (by simpa using congrArg Units.val h1)
  have hbarlam : h.bar lam = lam := by
    rcases hlam with h1 | h1 <;> rw [h1] <;> simp
  have hbar_g : (g' : Matrix (Fin 4) (Fin 4) F).map h.bar = lam • cT h (g' : Matrix (Fin 4) (Fin 4) F) := by
    calc (g' : Matrix (Fin 4) (Fin 4) F).map h.bar
        = (cT h (g' : Matrix (Fin 4) (Fin 4) F) * (g' : Matrix (Fin 4) (Fin 4) F)) *
            (g' : Matrix (Fin 4) (Fin 4) F).map h.bar := by rw [hu, Matrix.one_mul]
      _ = cT h (g' : Matrix (Fin 4) (Fin 4) F) * ((g' : Matrix (Fin 4) (Fin 4) F) *
            (g' : Matrix (Fin 4) (Fin 4) F).map h.bar) := by rw [Matrix.mul_assoc]
      _ = lam • cT h (g' : Matrix (Fin 4) (Fin 4) F) := by rw [hgg, Matrix.mul_smul, Matrix.mul_one]
  have hsymm : (g' : Matrix (Fin 4) (Fin 4) F)ᵀ = lam • (g' : Matrix (Fin 4) (Fin 4) F) := by
    have h1 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M.map h.bar) hbar_g
    simp only [map_bar_bar, hmapsmul, hbarlam, cT] at h1
    rw [Matrix.transpose_map, map_bar_bar] at h1
    have hll : lam * lam = 1 := by rcases hlam with h3 | h3 <;> rw [h3] <;> norm_num
    calc (g' : Matrix (Fin 4) (Fin 4) F)ᵀ = (lam * lam) • (g' : Matrix (Fin 4) (Fin 4) F)ᵀ := by
          rw [hll, one_smul]
      _ = lam • (lam • (g' : Matrix (Fin 4) (Fin 4) F)ᵀ) := (smul_smul _ _ _).symm
      _ = lam • (g' : Matrix (Fin 4) (Fin 4) F) := by rw [← h1]
  exact ⟨g', lam, hlam, hu, hgg, hsymm, hαg'⟩

end CFSG.GH74.Generic.S1.Uni
