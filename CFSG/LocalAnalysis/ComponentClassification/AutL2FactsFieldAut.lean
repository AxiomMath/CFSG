module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterDiag
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSylowModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Subgroup
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj projectiveSpecialLinearGroupEquivStatedProj)

theorem sq_eq_one_of_pow_four_char_two {F₁ : Type} [Field F₁] (h2 : (2 : F₁) = 0)
    (x : StatedProj (StatedSL 2 F₁)) (hx : x ^ 4 = 1) : x ^ 2 = 1 := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow] at hx ⊢
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  set m : Matrix (Fin 2) (Fin 2) F₁ := ((M : GL (Fin 2) F₁) : Matrix (Fin 2) (Fin 2) F₁) with hmdef
  have hdet : m.det = 1 := (mem_statedSL_iff _).mp M.2
  have hm4 : m ^ 4 = (c : F₁) • 1 := by
    have := congrArg (fun A : GL (Fin 2) F₁ => (A : Matrix (Fin 2) (Fin 2) F₁)) hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      at this
    rw [← this, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hc1 : (c : F₁) = 1 := by
    have := congrArg Matrix.det hm4
    rw [Matrix.det_pow, hdet, one_pow, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin] at this
    have h' : ((c : F₁) - 1) ^ 2 = 0 := by
      linear_combination (-1 : F₁) * this + (1 - (c : F₁)) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h')
  rw [hc1, one_smul] at hm4
  set t := m 0 0 + m 1 1
  have hdet' : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have htr : (m ^ 4).trace = (1 : Matrix (Fin 2) (Fin 2) F₁).trace := by rw [hm4]
  simp only [Matrix.trace_fin_two, pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.one_apply_eq] at htr
  have ht4 : t ^ 4 = 0 := by
    linear_combination htr + (2 * t ^ 2 * (m 0 0 * m 1 1 - m 0 1 * m 1 0) -
      (m 0 0 * m 1 1 - m 0 1 * m 1 0) ^ 2 + 1) * h2
  have ht : t = 0 := pow_eq_zero_iff (by norm_num) |>.mp ht4
  have hm2 : m ^ 2 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination (m 0 1) * ht
        | linear_combination (m 1 0) * ht
        | linear_combination (m 0 0) * ht - hdet' - h2
        | linear_combination (m 1 1) * ht - hdet' - h2
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨1, ?_⟩
  apply Units.ext
  rw [map_one]
  change (1 : Matrix (Fin 2) (Fin 2) F₁) = ((M ^ 2 : StatedSL 2 F₁) : GL (Fin 2) F₁).val
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  exact hm2.symm

@[expose] def ringAutConj {F₁ F : Type*} [Field F₁] [Field F] (θ : F₁ ≃+* F) :
    (F₁ ≃+* F₁) →* (F ≃+* F) where
  toFun σ := θ.symm.trans (σ.trans θ)
  map_one' := by
    ext x
    simp
  map_mul' σ τ := by
    ext x
    simp [RingAut.mul_apply]

theorem ringAutConj_apply {F₁ F : Type*} [Field F₁] [Field F] (θ : F₁ ≃+* F)
    (σ : F₁ ≃+* F₁) : ringAutConj θ σ = θ.symm.trans (σ.trans θ) := rfl

theorem orderOf_ringAutConj {F₁ F : Type*} [Field F₁] [Field F] (θ : F₁ ≃+* F)
    (σ : F₁ ≃+* F₁) : orderOf (ringAutConj θ σ) = orderOf σ := by
  apply orderOf_injective
  intro σ τ h
  ext x
  have := congrArg (fun ρ : F ≃+* F => ρ (θ x)) h
  simpa [ringAutConj] using this

theorem exists_psl2_pow_four {F : Type*} [Field F] [Finite F] (hn : 3 ≤ twoVal F) :
    ∃ y : PSL2 F, y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := by
  set a := stdGen F ^ 2 ^ (twoVal F - 3)
  have ha : orderOf a = 2 ^ 3 := by
    rw [orderOf_pow_of_dvd (by positivity) (by
      rw [orderOf_stdGen]; exact Nat.pow_dvd_pow 2 (by omega)), orderOf_stdGen,
      Nat.pow_div (by omega) (by norm_num)]
    congr 1
    omega
  obtain ⟨y, hy⟩ := tor_mem_range (F := F) (y := a ^ 2) ⟨(a : F), by push_cast; ring⟩
  refine ⟨y, ?_, ?_⟩
  · apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
    rw [map_pow, hy, map_one, ← map_pow, ← pow_mul,
      show 2 * 4 = 2 ^ 3 by norm_num, ← ha, pow_orderOf_eq_one, map_one]
  · intro h
    have h1 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
    rw [map_pow, hy, map_one, ← map_pow, ← pow_mul] at h1
    have h2 := pGammaL2FullSplitTorus_injective F (h1.trans (map_one _).symm)
    have := orderOf_dvd_of_pow_eq_one h2
    rw [ha] at this
    norm_num at this

theorem exists_conj_inr_of_field {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F)
    (hY : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1) (φ : MulAut Y) {F₁ : Type} [Field F₁] [Finite F₁]
    (e₁ : Y ≃* StatedProj (StatedSL 2 F₁)) (σ₁ : F₁ ≃+* F₁)
    (hφ : ∀ M N : StatedSL 2 F₁,
      (N : GL (Fin 2) F₁) = Matrix.GeneralLinearGroup.map σ₁.toRingHom (M : GL (Fin 2) F₁) →
        e₁ (φ (e₁.symm (QuotientGroup.mk M))) = QuotientGroup.mk N) :
    ∃ b : PGammaL2 F, ∃ σ : F ≃+* F, orderOf σ = orderOf σ₁ ∧
      autEquiv e φ = b * SemidirectProduct.inr σ * b⁻¹ := by
  have h2 : ringChar F₁ ≠ 2 := by
    intro hc
    have h2' : (2 : F₁) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := F₁)
      rw [hc] at this
      exact_mod_cast this
    obtain ⟨y, hy4, hy2⟩ := hY
    apply hy2
    have := sq_eq_one_of_pow_four_char_two h2' (e₁ y) (by rw [← map_pow, hy4, map_one])
    rw [← map_pow] at this
    exact e₁.injective (this.trans (map_one _).symm)
  have h₁ := isOddPrimePower_of_ringChar h2
  have hcard : Nat.card F₁ = Nat.card F := by
    apply card_eq_of_psl2_card_eq h₁ hodd
    rw [Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 F₁).toEquiv,
      ← Nat.card_congr e₁.toEquiv, Nat.card_congr e.toEquiv]
  have : Fintype F₁ := Fintype.ofFinite F₁
  have : Fintype F := Fintype.ofFinite F
  let θ : F₁ ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard])
  set e₂ : Y ≃* PSL2 F := e₁.trans (statedEquiv θ)
  have h₂ : autEquiv e₂ φ = SemidirectProduct.inr (ringAutConj θ σ₁) := by
    rw [autEquiv_eq_iff, semilinearAction_inr, congr_trans_apply, ringAutConj_apply]
    apply congr_statedEquiv_field θ σ₁
    intro M N hN
    rw [MulAut.congr_apply]
    exact hφ M N hN
  refine ⟨(semilinearEquivAut F).symm (e₂.symm.trans e), ringAutConj θ σ₁,
    orderOf_ringAutConj θ σ₁, ?_⟩
  rw [autEquiv_eq_conj e e₂, h₂]

theorem field_of_conj_inr {Y : Type} [Group Y] {F : Type} [Field F] [Finite F]
    (e : Y ≃* PSL2 F) (φ : MulAut Y) (b : PGammaL2 F) (σ : F ≃+* F)
    (h : autEquiv e φ = b * SemidirectProduct.inr σ * b⁻¹) :
    ∃ e₁ : Y ≃* StatedProj (StatedSL 2 F), ∀ M N : StatedSL 2 F,
      (N : GL (Fin 2) F) = Matrix.GeneralLinearGroup.map σ.toRingHom (M : GL (Fin 2) F) →
        e₁ (φ (e₁.symm (QuotientGroup.mk M))) = QuotientGroup.mk N := by
  set β : MulAut (PSL2 F) := semilinearEquivAut F b
  set e₂ : Y ≃* PSL2 F := e.trans (MulEquiv.symm β)
  set S := statedEquiv (RingEquiv.refl F)
  have hβ : e₂.symm.trans e = β := by
    ext x
    simp [e₂]
  have h₂ : autEquiv e₂ φ = SemidirectProduct.inr σ := by
    have := autEquiv_eq_conj e e₂ φ
    rw [hβ, MulEquiv.symm_apply_apply, h] at this
    exact (mul_left_cancel (mul_right_cancel this)).symm
  have hc : MulAut.congr e₂ φ = psl2FieldAut F σ := by
    rw [← semilinearAction_inr, ← h₂, semilinearAction_autEquiv]
  refine ⟨e₂.trans S.symm, fun M N hN => ?_⟩
  apply S.injective
  have h3 : S ((e₂.trans S.symm) (φ ((e₂.trans S.symm).symm (QuotientGroup.mk M)))) =
      MulAut.congr e₂ φ (S (QuotientGroup.mk M)) := by
    simp [MulAut.congr_apply]
  rw [h3, hc]
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [psl2FieldAut_toPGL, toPGL_statedEquiv_mk, toPGL_statedEquiv_mk, pgl2FieldAut_apply]
  change pgl2RingEquiv _ (QuotientGroup.mk' (Subgroup.center _) _) = _
  rw [pgl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  congr 1
  rw [hN]
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

section Model

variable {F : Type} [Field F]

@[expose] def IsFieldInvModel (x : PGammaL2 F) : Prop :=
  ∃ b : PGammaL2 F, ∃ σ : F ≃+* F, orderOf σ = 2 ∧ x = b * SemidirectProduct.inr σ * b⁻¹

@[expose] def IsFieldAutModel (x : PGammaL2 F) : Prop :=
  ∃ b : PGammaL2 F, ∃ σ : F ≃+* F, σ ≠ 1 ∧ x = b * SemidirectProduct.inr σ * b⁻¹

end Model

theorem isFieldAutPSL2_iff {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F)
    (hY : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1) (φ : MulAut Y) :
    HarrisLit.IsFieldAutPSL2 φ ↔ IsFieldInvModel (autEquiv e φ) := by
  constructor
  · rintro ⟨F₁, _, _, e₁, σ₁, hσ₁, hφ⟩
    obtain ⟨b, σ, hσ, h⟩ := exists_conj_inr_of_field hodd e hY φ e₁ σ₁ hφ
    exact ⟨b, σ, hσ.trans hσ₁, h⟩
  · rintro ⟨b, σ, hσ, h⟩
    obtain ⟨e₁, he₁⟩ := field_of_conj_inr e φ b σ h
    exact ⟨F, inferInstance, inferInstance, e₁, σ, hσ, he₁⟩

theorem isFieldAutPSL2Any_iff {Y : Type} [Group Y] [Finite Y] {F : Type} [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F)
    (hY : ∃ y : Y, y ^ 4 = 1 ∧ y ^ 2 ≠ 1) (φ : MulAut Y) :
    HarrisLit.IsFieldAutPSL2Any φ ↔ IsFieldAutModel (autEquiv e φ) := by
  constructor
  · rintro ⟨F₁, _, _, e₁, σ₁, hσ₁, hφ⟩
    obtain ⟨b, σ, hσ, h⟩ := exists_conj_inr_of_field hodd e hY φ e₁ σ₁ hφ
    refine ⟨b, σ, fun h1 => hσ₁ ?_, h⟩
    rw [← orderOf_eq_one_iff, ← hσ, h1, orderOf_one]
  · rintro ⟨b, σ, hσ, h⟩
    obtain ⟨e₁, he₁⟩ := field_of_conj_inr e φ b σ h
    exact ⟨F, inferInstance, inferInstance, e₁, σ, hσ, he₁⟩

end CFSG.ComponentClassification.AutL2Facts
