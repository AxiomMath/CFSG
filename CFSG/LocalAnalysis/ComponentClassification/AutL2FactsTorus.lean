module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2FullSplitTorus
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup Matrix

universe u

variable (F : Type u) [Field F]

abbrev tor : Fˣ →* PGL2 F := pGammaL2FullSplitTorus F

@[expose] def swGL : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [Matrix.det_fin_two])

@[expose] def sw : PGL2 F := Matrix.ProjGenLinGroup.mk (swGL F)

@[expose] def swp : Bool → PGL2 F
  | false => 1
  | true => sw F

@[expose] def twist : Bool → Fˣ → Fˣ
  | false, b => b
  | true, b => b⁻¹

abbrev fu (σ : F ≃+* F) : Fˣ →* Fˣ := Units.map σ.toRingHom

@[expose] def nm (a : Fˣ) (ε : Bool) (σ : F ≃+* F) : PGammaL2 F :=
  ⟨tor F a * swp F ε, σ⟩

variable {F}

@[simp] theorem swp_false : swp F false = 1 := rfl
@[simp] theorem swp_true : swp F true = sw F := rfl
@[simp] theorem twist_false (b : Fˣ) : twist F false b = b := rfl
@[simp] theorem twist_true (b : Fˣ) : twist F true b = b⁻¹ := rfl

theorem fu_fu_inv (σ : F ≃+* F) (a : Fˣ) : fu F σ (fu F σ⁻¹ a) = a := by
  ext
  simp

theorem fu_inv_fu (σ : F ≃+* F) (a : Fˣ) : fu F σ⁻¹ (fu F σ a) = a := by
  ext
  simp

theorem fu_one (a : Fˣ) : fu F 1 a = a := rfl

theorem fu_mul (σ τ : F ≃+* F) (a : Fˣ) : fu F (σ * τ) a = fu F σ (fu F τ a) := rfl

theorem swGL_mul_self : swGL F * swGL F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swGL, Matrix.mul_apply, Fin.sum_univ_two]

theorem sw_mul_sw : sw F * sw F = 1 := by
  rw [sw, ← map_mul, swGL_mul_self, map_one]

theorem sw_mul_tor (a : Fˣ) : sw F * tor F a = tor F a⁻¹ * sw F := by
  change Matrix.ProjGenLinGroup.mk (swGL F) * Matrix.ProjGenLinGroup.mk
      (pGammaL2FullSplitTorusGL F a) =
    Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F a⁻¹) *
      Matrix.ProjGenLinGroup.mk (swGL F)
  rw [← map_mul, ← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨a⁻¹, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have ha := a.ne_zero
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar]
  fin_cases i <;> fin_cases j <;>
    simp [swGL, pGammaL2FullSplitTorusGL, Matrix.mul_apply, Fin.sum_univ_two, ha,
      Matrix.vecMul_diagonal]

theorem fieldAut_sw (σ : F ≃+* F) : pgl2FieldAut F σ (sw F) = sw F := by
  change pgl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (swGL F)) = _
  rw [pgl2RingEquiv_mk]
  change Matrix.ProjGenLinGroup.mk _ = Matrix.ProjGenLinGroup.mk _
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swGL, Matrix.GeneralLinearGroup.map]

theorem fieldAut_tor (σ : F ≃+* F) (a : Fˣ) :
    pgl2FieldAut F σ (tor F a) = tor F (fu F σ a) :=
  pGammaL2FullSplitTorus_map_field F σ a

theorem fieldAut_swp (σ : F ≃+* F) (ε : Bool) : pgl2FieldAut F σ (swp F ε) = swp F ε := by
  cases ε
  · simp
  · simp [fieldAut_sw]

theorem swp_mul_tor (ε : Bool) (b : Fˣ) :
    swp F ε * tor F b = tor F (twist F ε b) * swp F ε := by
  cases ε
  · simp
  · simp [sw_mul_tor]

theorem swp_mul_swp (ε ε' : Bool) : swp F ε * swp F ε' = swp F (xor ε ε') := by
  cases ε <;> cases ε' <;> simp [sw_mul_sw]

theorem twist_mul (ε : Bool) (a b : Fˣ) : twist F ε (a * b) = twist F ε a * twist F ε b := by
  cases ε
  · rfl
  · simp [mul_comm]

theorem twist_twist (ε ε' : Bool) (a : Fˣ) :
    twist F ε (twist F ε' a) = twist F (xor ε ε') a := by
  cases ε <;> cases ε' <;> simp

theorem fu_twist (σ : F ≃+* F) (ε : Bool) (a : Fˣ) :
    fu F σ (twist F ε a) = twist F ε (fu F σ a) := by
  cases ε <;> simp

@[simp] theorem nm_left (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    (nm F a ε σ).left = tor F a * swp F ε := rfl

@[simp] theorem nm_right (a : Fˣ) (ε : Bool) (σ : F ≃+* F) : (nm F a ε σ).right = σ := rfl

theorem nm_mul (a b : Fˣ) (ε ε' : Bool) (σ τ : F ≃+* F) :
    nm F a ε σ * nm F b ε' τ = nm F (a * twist F ε (fu F σ b)) (xor ε ε') (σ * τ) := by
  apply SemidirectProduct.ext
  · simp only [SemidirectProduct.mul_left, nm_left, nm_right, map_mul, fieldAut_tor, fieldAut_swp]
    rw [mul_assoc, ← mul_assoc (swp F ε), swp_mul_tor, mul_assoc, swp_mul_swp, ← mul_assoc,
      ← map_mul]
  · rfl

theorem nm_one : nm F 1 false 1 = 1 := by
  apply SemidirectProduct.ext
  · simp
  · rfl

theorem nm_inv (a : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    (nm F a ε σ)⁻¹ = nm F (twist F ε (fu F σ⁻¹ a⁻¹)) ε σ⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, nm_mul, Bool.xor_self]
  have : a * twist F ε (fu F σ (twist F ε (fu F σ⁻¹ a⁻¹))) = 1 := by
    rw [fu_twist, twist_twist, Bool.xor_self, twist_false, fu_fu_inv, mul_inv_cancel]
  rw [this, mul_inv_cancel, nm_one]

theorem tor_ne_tor_mul_sw (a b : Fˣ) : tor F a ≠ tor F b * sw F := by
  intro h
  change Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F a) =
    Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F b) * Matrix.ProjGenLinGroup.mk
      (swGL F) at h
  rw [← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h00 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hu
  simp [swGL, pGammaL2FullSplitTorusGL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.scalar] at h00

theorem tor_mul_swp_injective {a b : Fˣ} {ε ε' : Bool}
    (h : tor F a * swp F ε = tor F b * swp F ε') : a = b ∧ ε = ε' := by
  cases ε <;> cases ε'
  · simp only [swp_false, mul_one] at h
    exact ⟨pGammaL2FullSplitTorus_injective F h, rfl⟩
  · simp only [swp_false, swp_true, mul_one] at h
    exact absurd h (tor_ne_tor_mul_sw a b)
  · simp only [swp_false, swp_true, mul_one] at h
    exact absurd h.symm (tor_ne_tor_mul_sw b a)
  · simp only [swp_true] at h
    exact ⟨pGammaL2FullSplitTorus_injective F (mul_right_cancel h), rfl⟩

theorem nm_injective {a b : Fˣ} {ε ε' : Bool} {σ τ : F ≃+* F}
    (h : nm F a ε σ = nm F b ε' τ) : a = b ∧ ε = ε' ∧ σ = τ := by
  obtain ⟨h1, h2⟩ := tor_mul_swp_injective (congrArg SemidirectProduct.left h)
  exact ⟨h1, h2, congrArg SemidirectProduct.right h⟩

theorem nm_eq_nm_iff {a b : Fˣ} {ε ε' : Bool} {σ τ : F ≃+* F} :
    nm F a ε σ = nm F b ε' τ ↔ a = b ∧ ε = ε' ∧ σ = τ := by
  constructor
  · exact nm_injective
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem diag_or_antidiag_of_conj {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det ≠ 0) {μ ν c : F}
    (hμ : μ ≠ 1)
    (h : A * Matrix.diagonal ![μ, 1] * Matrix.diagonal (fun _ => c) =
      Matrix.diagonal ![ν, 1] * A) :
    (A 0 1 = 0 ∧ A 1 0 = 0) ∨ (A 0 0 = 0 ∧ A 1 1 = 0) := by
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  have e00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Matrix.diagonal_apply] at e00 e01 e10 e11
  rw [Matrix.det_fin_two] at hA
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · exact Or.inl ⟨hb, hc⟩
    · exfalso
      have hμc : μ * c = 1 := by
        have h' : (μ * c - 1) * A 1 0 = 0 := by linear_combination e10
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hc)
      have hd : A 1 1 ≠ 0 := by
        intro hd; apply hA; rw [hb, hd]; ring
      have hc1 : c = 1 := by
        have h' : (c - 1) * A 1 1 = 0 := by linear_combination e11
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hd)
      exact hμ (by rw [hc1, mul_one] at hμc; exact hμc)
  · have hcν : c = ν := by
      have h' : (c - ν) * A 0 1 = 0 := by linear_combination e01
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hb)
    have hc : A 1 0 ≠ 0 := by
      intro hc
      by_cases hd : A 1 1 = 0
      · apply hA; rw [hc, hd]; ring
      · exact hA (by
          have ha : A 0 0 ≠ 0 ∨ A 0 0 = 0 := (em _).symm
          rw [hc]
          simp only [mul_zero, sub_zero]
          by_contra hne
          have ha' : A 0 0 ≠ 0 := left_ne_zero_of_mul hne
          have hc1 : c = 1 := by
            have h' : (c - 1) * A 1 1 = 0 := by linear_combination e11
            exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hd)
          have : μ * c = ν := by
            have h' : (μ * c - ν) * A 0 0 = 0 := by linear_combination e00
            exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right ha')
          rw [hc1, mul_one, ← hcν, hc1] at this
          exact hμ this)
    have hμc : μ * c = 1 := by
      have h' : (μ * c - 1) * A 1 0 = 0 := by linear_combination e10
      exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hc)
    have ha : A 0 0 = 0 := by
      by_contra ha
      have : μ * c = ν := by
        have h' : (μ * c - ν) * A 0 0 = 0 := by linear_combination e00
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right ha)
      rw [← hcν, hμc] at this
      rw [← this, mul_one] at hμc
      exact hμ hμc
    have hd : A 1 1 = 0 := by
      by_contra hd
      have hc1 : c = 1 := by
        have h' : (c - 1) * A 1 1 = 0 := by linear_combination e11
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hd)
      rw [hc1, mul_one] at hμc
      exact hμ hμc
    exact Or.inr ⟨ha, hd⟩

theorem exists_tor_swp_of_diag_or_antidiag (A : GL (Fin 2) F)
    (h : ((A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) ∨
      ((A : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0)) :
    ∃ a ε, Matrix.ProjGenLinGroup.mk A = tor F a * swp F ε := by
  have hdet := A.det_ne_zero
  rw [Matrix.det_fin_two] at hdet
  rcases h with ⟨hb, hc⟩ | ⟨ha, hd⟩
  · have ha : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
      intro h0; apply hdet; rw [h0, hb]; ring
    have hd : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
      intro h0; apply hdet; rw [h0, hb]; ring
    refine ⟨Units.mk0 _ ha / Units.mk0 _ hd, false, ?_⟩
    simp only [swp_false, mul_one]
    change Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F _)
    rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨(Units.mk0 _ hd)⁻¹, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pGammaL2FullSplitTorusGL, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.scalar, hb, hc, hd, div_eq_mul_inv]
  · have hb : (A : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0 := by
      intro h0; apply hdet; rw [h0, ha]; ring
    have hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
      intro h0; apply hdet; rw [h0, ha]; ring
    refine ⟨Units.mk0 _ hb / Units.mk0 _ hc, true, ?_⟩
    simp only [swp_true]
    change Matrix.ProjGenLinGroup.mk A =
      Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F _) *
        Matrix.ProjGenLinGroup.mk (swGL F)
    rw [← map_mul, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨(Units.mk0 _ hc)⁻¹, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pGammaL2FullSplitTorusGL, swGL, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.GeneralLinearGroup.scalar, hc, ha, hd, div_eq_mul_inv]

theorem exists_tor_swp_of_conj (g : PGL2 F) {μ ν : Fˣ} (hμ : μ ≠ 1)
    (h : g * tor F μ * g⁻¹ = tor F ν) : ∃ a ε, g = tor F a * swp F ε := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  apply exists_tor_swp_of_diag_or_antidiag
  have h' : Matrix.ProjGenLinGroup.mk (A * pGammaL2FullSplitTorusGL F μ) =
      Matrix.ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL F ν * A) := by
    rw [map_mul, map_mul]
    change Matrix.ProjGenLinGroup.mk A * tor F μ = tor F ν * Matrix.ProjGenLinGroup.mk A
    rw [← h]
    group
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h'
  have hm := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F)) hu
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, pGammaL2FullSplitTorusGL,
    MonoidHom.coe_mk, OneHom.coe_mk, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.scalar_apply] at hm
  exact diag_or_antidiag_of_conj A.det_ne_zero (fun h1 => hμ (Units.ext h1)) hm

theorem exists_nm_of_conj_tor (x : PGammaL2 F) {μ ν : Fˣ} (hμ : μ ≠ 1)
    (h : x * SemidirectProduct.inl (tor F μ) * x⁻¹ = SemidirectProduct.inl (tor F ν)) :
    ∃ a ε, x = nm F a ε x.right := by
  have hleft : x.left * tor F (fu F x.right μ) * x.left⁻¹ = tor F ν := by
    have h1 := congrArg SemidirectProduct.left h
    rw [← fieldAut_tor]
    have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
      (SemidirectProduct.inl_left_mul_inr_right x).symm
    rw [hx] at h1
    simpa [SemidirectProduct.mul_left, SemidirectProduct.inv_left, mul_assoc] using h1
  have hμ' : fu F x.right μ ≠ 1 := by
    intro h1
    apply hμ
    have := congrArg (fu F x.right⁻¹) h1
    rwa [map_one, fu_inv_fu] at this
  obtain ⟨a, ε, hg⟩ := exists_tor_swp_of_conj x.left hμ' hleft
  exact ⟨a, ε, SemidirectProduct.ext hg rfl⟩

theorem nm_commute_tor_iff (a μ : Fˣ) (ε : Bool) (σ : F ≃+* F) :
    nm F a ε σ * nm F μ false 1 = nm F μ false 1 * nm F a ε σ ↔ twist F ε (fu F σ μ) = μ := by
  rw [nm_mul, nm_mul, nm_eq_nm_iff]
  simp only [Bool.xor_false, Bool.false_xor, mul_one, one_mul, and_true, twist_false, fu_one]
  constructor
  · intro h
    rw [mul_comm μ a] at h
    exact mul_left_cancel h
  · intro h
    rw [h, mul_comm]

end CFSG.ComponentClassification.AutL2Facts
