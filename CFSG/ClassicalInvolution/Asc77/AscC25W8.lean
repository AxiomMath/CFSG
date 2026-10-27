module

public import CFSG.ClassicalInvolution.Asc77.AscC25W7

public section

open scoped Matrix MatrixGroups
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.LieType.Steinberg.Sp (blockMat)

namespace CFSG.ClassicalInvolution.Asc77.C25W.Sp

variable {F : Type} [Field F] {m : ℕ} (τ : F ≃+* F)
  (N : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F)

theorem blockMat_mulVec_left (p q : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (hpq : p ≠ q)
    (A : Matrix (Fin 2) (Fin 2) F) :
    blockMat p q A *ᵥ Pi.single p 1 =
      A 0 0 • (Pi.single p 1 : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) +
        A 1 0 • (Pi.single q 1 : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) := by
  ext r
  rw [mulVec_single_one_apply]
  by_cases hrp : r = p
  · subst hrp; simp [blockMat, hpq]
  · by_cases hrq : r = q
    · subst hrq; simp [blockMat, hrp]
    · simp [blockMat, hrp, hrq, Matrix.one_apply]

theorem blockMat_mulVec_right (p q : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (hpq : p ≠ q)
    (A : Matrix (Fin 2) (Fin 2) F) :
    blockMat p q A *ᵥ Pi.single q 1 =
      A 0 1 • (Pi.single p 1 : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) +
        A 1 1 • (Pi.single q 1 : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) := by
  ext r
  rw [mulVec_single_one_apply]
  by_cases hrp : r = p
  · subst hrp; simp [blockMat, Ne.symm hpq]
  · by_cases hrq : r = q
    · subst hrq; simp [blockMat, hrp]
    · simp [blockMat, hrp, hrq, Matrix.one_apply]

theorem neg_one_mul_neg_one_sl2 : (-1 : SL(2, F)) * (-1) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_rotation (u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) (huw : form u w = 1)
    (g₁ : SL(2, F)) :
    ∃ s : StatedSp (m + 1 + 1) F,
      mat (m + 1 + 1) F s *ᵥ u = (g₁ : Matrix (Fin 2) (Fin 2) F) 0 0 • u +
        (g₁ : Matrix (Fin 2) (Fin 2) F) 1 0 • w ∧
      mat (m + 1 + 1) F s *ᵥ w = (g₁ : Matrix (Fin 2) (Fin 2) F) 0 1 • u +
        (g₁ : Matrix (Fin 2) (Fin 2) F) 1 1 • w ∧
      (∀ q, form q u = 0 → form q w = 0 → mat (m + 1 + 1) F s *ᵥ q = q) ∧
      (g₁ * g₁ = -1 → (2 : F) ≠ 0 →
        s * s * (s * s) = 1 ∧ ¬ ∃ c : F, mat (m + 1 + 1) F (s * s) = c • 1) := by
  obtain ⟨g, hgu, hgw⟩ := exists_sp_apply_eq (m := m + 1) u w huw
  have hpq : (Sum.inl 0 : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) ≠ Sum.inr 0 := Sum.inl_ne_inr
  have e1 : mat (m + 1 + 1) F g⁻¹ *ᵥ u = Pi.single (Sum.inl 0) 1 := by
    rw [← hgu, mulVec_inv_mulVec]
  have e2 : mat (m + 1 + 1) F g⁻¹ *ᵥ w = Pi.single (Sum.inr 0) 1 := by
    rw [← hgw, mulVec_inv_mulVec]
  refine ⟨g * longBlock F (m + 1 + 1) 0 g₁ * g⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, mat_longBlock,
      blockMat_mulVec_left _ _ hpq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hgu, hgw]
  · rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, mat_longBlock,
      blockMat_mulVec_right _ _ hpq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hgu, hgw]
  · intro q hq1 hq2
    have h1 : form (mat (m + 1 + 1) F g⁻¹ *ᵥ q) (Pi.single (Sum.inl 0) 1) = 0 := by
      rw [← e1, form_mulVec]; exact hq1
    have h2 : form (mat (m + 1 + 1) F g⁻¹ *ᵥ q) (Pi.single (Sum.inr 0) 1) = 0 := by
      rw [← e2, form_mulVec]; exact hq2
    rw [form_single_right] at h1 h2
    simp only [par_inl, par_inr, sgn_inl, sgn_inr] at h1 h2
    have hz : ∀ t ∈ coords (0 : Fin (m + 1 + 1)),
        (mat (m + 1 + 1) F g⁻¹ *ᵥ q) t = 0 := by
      intro t ht
      rcases mem_coords.1 ht with rfl | rfl
      · simpa using h2
      · simpa using h1
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      mulVec_eq_self_of_isSupp (isSupp_longBlock 0 g₁) hz, mulVec_mulVec_inv]
  · intro hg h2
    have hss : g * longBlock F (m + 1 + 1) 0 g₁ * g⁻¹ * (g * longBlock F (m + 1 + 1) 0 g₁ * g⁻¹) =
        g * longInv F (m + 1 + 1) 0 * g⁻¹ := by
      calc _ = g * (longBlock F (m + 1 + 1) 0 (g₁ * g₁)) * g⁻¹ := by rw [map_mul]; group
        _ = _ := by rw [hg]; rfl
    refine ⟨?_, ?_⟩
    · rw [hss]
      calc g * longInv F (m + 1 + 1) 0 * g⁻¹ * (g * longInv F (m + 1 + 1) 0 * g⁻¹) =
          g * (longInv F (m + 1 + 1) 0 * longInv F (m + 1 + 1) 0) * g⁻¹ := by group
        _ = 1 := by
          have : longInv F (m + 1 + 1) 0 * longInv F (m + 1 + 1) 0 = 1 := by
            rw [longInv, ← map_mul, neg_one_mul_neg_one_sl2, map_one]
          rw [this]; group
    · rintro ⟨c, hc⟩
      rw [hss] at hc
      have hi : mat (m + 1 + 1) F (longInv F (m + 1 + 1) 0) = c • 1 := by
        have : longInv F (m + 1 + 1) 0 = g⁻¹ * (g * longInv F (m + 1 + 1) 0 * g⁻¹) * g := by
          group
        rw [this, map_mul, map_mul, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
          ← map_mul, inv_mul_cancel, map_one]
      rw [mat_longInv] at hi
      have a0 := congrFun (congrFun hi (Sum.inl 0)) (Sum.inl 0)
      have a1 := congrFun (congrFun hi (Sum.inl 1)) (Sum.inl 1)
      have h10 : (Sum.inl 1 : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) ∉
          coords (0 : Fin (m + 1 + 1)) := by
        intro h
        rcases mem_coords.1 h with h | h
        · exact absurd (Sum.inl.inj h) (by simp)
        · exact Sum.inl_ne_inr h
      simp [inl_mem_coords, h10] at a0 a1
      apply h2
      linear_combination a1 - a0


theorem phi_eq_of_id (hid : ∀ a, τ a = a) (v : Fin (m + 1) ⊕ Fin (m + 1) → F) :
    phi N τ v = N *ᵥ v := by
  have : tv τ v = v := by ext i; simp [tv, hid]
  simp [phi, this]

theorem map_eq_of_id (hid : ∀ a, τ a = a) :
    N.map τ = N := by
  ext i j; simp [hid]

theorem matrix_comm_of_phi_comm (hτ : ∀ x, τ (τ x) = x)
    (S : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F)
    (hcomm : ∀ v, phi N τ (S *ᵥ v) = S *ᵥ phi N τ v) : N * S.map τ = S * N := by
  have key : ∀ v, (N * S.map τ) *ᵥ v = (S * N) *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : S.map τ *ᵥ v = tv τ (S *ᵥ tv τ v) := by
      rw [tv_mulVec, tv_tv τ hτ]
    have h2 := hcomm (tv τ v)
    unfold phi at h2
    rw [tv_tv τ hτ] at h2
    rw [h1]
    exact h2
  ext i j
  rw [← mulVec_single_one_apply (N * S.map τ) j i, ← mulVec_single_one_apply (S * N) j i,
    key]

theorem mem_planeGroup_of_perp {u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F}
    (s : StatedSp (m + 1 + 1) F)
    (hperp : ∀ q, form q u = 0 → form q w = 0 → mat (m + 1 + 1) F s *ᵥ q = q) :
    s ∈ planeGroup (Submodule.span F {u, w}) := by
  rw [planeGroup, mem_fixing]
  intro v hv
  obtain ⟨h1, h2⟩ := mem_orthSet_span_pair.1 hv
  exact hperp v h1 h2

@[expose] def gStd : SL(2, F) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem gStd_sq : gStd * gStd = (-1 : SL(2, F)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gStd, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def gRot (h : F) (hh : h ≠ 0) : SL(2, F) :=
  ⟨!![0, -h⁻¹; h, 0], by simp [Matrix.det_fin_two, hh]⟩

theorem gRot_sq (h : F) (hh : h ≠ 0) : gRot h hh * gRot h hh = (-1 : SL(2, F)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gRot, Matrix.mul_apply, Fin.sum_univ_two, hh]


theorem phi_neg (a : Fin (m + 1) ⊕ Fin (m + 1) → F) : phi N τ (-a) = -phi N τ a := by
  have h := phi_smul τ N (-1 : F) a
  rw [neg_one_smul, map_neg, map_one, neg_one_smul] at h
  exact h

theorem rotation_of_pair
    (N : Matrix (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) F)
    (hτ : ∀ x, τ (τ x) = x) (h2 : (2 : F) ≠ 0)
    {u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F} (huw : form u w = 1) (g₁ : SL(2, F))
    (hg : g₁ * g₁ = -1)
    (hφperp : ∀ q, form q u = 0 → form q w = 0 →
      form (phi N τ q) u = 0 ∧ form (phi N τ q) w = 0)
    (hcomm : ∀ S : Matrix (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) F,
      S *ᵥ u = (g₁ : Matrix (Fin 2) (Fin 2) F) 0 0 • u +
        (g₁ : Matrix (Fin 2) (Fin 2) F) 1 0 • w →
      S *ᵥ w = (g₁ : Matrix (Fin 2) (Fin 2) F) 0 1 • u +
        (g₁ : Matrix (Fin 2) (Fin 2) F) 1 1 • w →
      phi N τ (S *ᵥ u) = S *ᵥ phi N τ u ∧ phi N τ (S *ᵥ w) = S *ᵥ phi N τ w) :
    ∃ (u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) (s : StatedSp (m + 1 + 1) F),
      form u w = 1 ∧ s ∈ planeGroup (Submodule.span F {u, w}) ∧ s * s * (s * s) = 1 ∧
      (¬ ∃ c : F, mat (m + 1 + 1) F (s * s) = c • 1) ∧
      N * (mat (m + 1 + 1) F s).map τ = mat (m + 1 + 1) F s * N := by
  obtain ⟨s, hsu, hsw, hperp, hpow⟩ := exists_rotation u w huw g₁
  obtain ⟨hs4, hsc⟩ := hpow hg h2
  obtain ⟨hu, hw⟩ := hcomm (mat (m + 1 + 1) F s) hsu hsw
  have hall := comm_of_pair τ (phi N τ) (phi_add τ N) (phi_smul τ N) huw
    (mat (m + 1 + 1) F s) hperp hφperp hu hw
  exact ⟨u, w, s, huw, mem_planeGroup_of_perp s hperp, hs4, hsc,
    matrix_comm_of_phi_comm τ N hτ _ hall⟩

theorem case_fixed
    (N : Matrix (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) F)
    (hτ : ∀ x, τ (τ x) = x) (h2 : (2 : F) ≠ 0)
    (hN : Nᵀ * gram F (m + 1 + 1) * N = gram F (m + 1 + 1))
    {u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F} (hu : phi N τ u = u) (hw : phi N τ w = w)
    (huw : form u w = 1) :
    ∃ (u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) (s : StatedSp (m + 1 + 1) F),
      form u w = 1 ∧ s ∈ planeGroup (Submodule.span F {u, w}) ∧ s * s * (s * s) = 1 ∧
      (¬ ∃ c : F, mat (m + 1 + 1) F (s * s) = c • 1) ∧
      N * (mat (m + 1 + 1) F s).map τ = mat (m + 1 + 1) F s * N := by
  refine rotation_of_pair τ N hτ h2 huw gStd gStd_sq ?_ ?_
  · intro q hq1 hq2
    constructor
    · have := form_phi τ N hN q u
      rwa [hu, hq1, map_zero] at this
    · have := form_phi τ N hN q w
      rwa [hw, hq2, map_zero] at this
  · intro S hSu hSw
    simp [gStd] at hSu hSw
    constructor
    · rw [hSu, hu, hSu, phi_neg, hw]
    · rw [hSw, hw, hSw, hu]

theorem case_neg
    (N : Matrix (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) F)
    (hτ : ∀ x, τ (τ x) = x) (h2 : (2 : F) ≠ 0)
    (hN : Nᵀ * gram F (m + 1 + 1) * N = gram F (m + 1 + 1))
    (hc : N * N.map τ = (-1 : F) • 1) (x : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F)
    (hx : form x (phi N τ x) ≠ 0) :
    ∃ (u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) (s : StatedSp (m + 1 + 1) F),
      form u w = 1 ∧ s ∈ planeGroup (Submodule.span F {u, w}) ∧ s * s * (s * s) = 1 ∧
      (¬ ∃ c : F, mat (m + 1 + 1) F (s * s) = c • 1) ∧
      N * (mat (m + 1 + 1) F s).map τ = mat (m + 1 + 1) F s * N := by
  have hφφ : ∀ v, phi N τ (phi N τ v) = -v := by
    intro v; rw [phi_phi τ N hτ (-1) hc, neg_one_smul]
  obtain ⟨h, hh⟩ : ∃ h, h = form x (phi N τ x) := ⟨_, rfl⟩
  rw [← hh] at hx
  have hτh : τ h ≠ 0 := (map_ne_zero τ).2 hx
  obtain ⟨w, hw⟩ : ∃ w, w = h⁻¹ • phi N τ x := ⟨_, rfl⟩
  have huw : form x w = 1 := by rw [hw, form_smul_right, ← hh, inv_mul_cancel₀ hx]
  have hφu : phi N τ x = h • w := by rw [hw, smul_smul, mul_inv_cancel₀ hx, one_smul]
  have hφw : phi N τ w = (-(τ h)⁻¹) • x := by
    rw [hw, phi_smul, hφφ, map_inv₀, smul_neg, neg_smul]
  have hx' : x = (-τ h) • phi N τ w := by
    rw [hφw, smul_smul]
    have : (-τ h) * (-(τ h)⁻¹) = 1 := by field_simp
    rw [this, one_smul]
  refine rotation_of_pair τ N hτ h2 huw (gRot h hx) (gRot_sq h hx) ?_ ?_
  · intro q hq1 hq2
    constructor
    · have h1 := form_phi τ N hN q w
      rw [hq2, map_zero] at h1
      rw [hx', form_smul_right, h1, mul_zero]
    · have h1 := form_phi τ N hN q x
      rw [hq1, map_zero] at h1
      rw [hw, form_smul_right, h1, mul_zero]
  · intro S hSu hSw
    have e00 : ((gRot h hx : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by simp [gRot]
    have e10 : ((gRot h hx : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = h := by simp [gRot]
    have e01 : ((gRot h hx : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1 = -h⁻¹ := by simp [gRot]
    have e11 : ((gRot h hx : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by simp [gRot]
    rw [e00, e10, zero_smul, zero_add] at hSu
    rw [e01, e11, zero_smul, add_zero] at hSw
    constructor
    · rw [hSu, phi_smul, hφw, hφu, Matrix.mulVec_smul, hSw, smul_smul, smul_smul]
      have e1 : τ h * -(τ h)⁻¹ = -1 := by field_simp
      have e2 : h * -h⁻¹ = -1 := by field_simp
      rw [e1, e2]
    · rw [hSw, phi_smul, hφu, hφw, Matrix.mulVec_smul, hSu, map_neg, map_inv₀, smul_smul]


theorem case_scalar
    (N : Matrix (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) F)
    (hτ : ∀ x, τ (τ x) = x) (h2 : (2 : F) ≠ 0) (hid : ∀ a, τ a = a)
    (hy : ∀ y, N *ᵥ y + y = 0) :
    ∃ (u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) (s : StatedSp (m + 1 + 1) F),
      form u w = 1 ∧ s ∈ planeGroup (Submodule.span F {u, w}) ∧ s * s * (s * s) = 1 ∧
      (¬ ∃ c : F, mat (m + 1 + 1) F (s * s) = c • 1) ∧
      N * (mat (m + 1 + 1) F s).map τ = mat (m + 1 + 1) F s * N := by
  have hNy : ∀ y, N *ᵥ y = -y := fun y => eq_neg_of_add_eq_zero_left (hy y)
  have hφ : ∀ y, phi N τ y = -y := fun y => by rw [phi_eq_of_id τ N hid, hNy]
  refine rotation_of_pair τ N hτ h2
    (form_single_inl_inr (K := F) (n := m + 1 + 1) 0) gStd gStd_sq ?_ ?_
  · intro q hq1 hq2
    rw [hφ, form_neg_left, form_neg_left, hq1, hq2]; simp
  · intro S _ _
    exact ⟨by rw [hφ, hφ, Matrix.mulVec_neg], by rw [hφ, hφ, Matrix.mulVec_neg]⟩

theorem exists_stable_rotation
    (N : Matrix (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) (Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1)) F)
    (hτ : ∀ x, τ (τ x) = x) (h2 : (2 : F) ≠ 0)
    (hN : Nᵀ * gram F (m + 1 + 1) * N = gram F (m + 1 + 1)) (c' : F) (hc'1 : c' * c' = 1)
    (hc : N * N.map τ = c' • 1) :
    ∃ (u w : Fin (m + 1 + 1) ⊕ Fin (m + 1 + 1) → F) (s : StatedSp (m + 1 + 1) F),
      form u w = 1 ∧ s ∈ planeGroup (Submodule.span F {u, w}) ∧ s * s * (s * s) = 1 ∧
      (¬ ∃ c : F, mat (m + 1 + 1) F (s * s) = c • 1) ∧
      N * (mat (m + 1 + 1) F s).map τ = mat (m + 1 + 1) F s * N := by
  have hc'0 : c' ≠ 0 := by rintro rfl; simp at hc'1
  have hinj := phi_inj τ N hτ c' hc'0 hc
  rcases mul_self_eq_one_iff.1 hc'1 with rfl | rfl
  · by_cases hne : ∃ a, τ a ≠ a
    · obtain ⟨u, w, hu, hw, huw⟩ := exists_fixed_pair_semi τ N h2 hτ hne hN hc
      exact case_fixed τ N hτ h2 hN hu hw huw
    · push Not at hne
      have hNN : N * N = 1 := by
        rw [map_eq_of_id τ N hne] at hc
        simpa using hc
      by_cases hy : ∃ y, N *ᵥ y + y ≠ 0
      · obtain ⟨y, hy⟩ := hy
        obtain ⟨u, w, hu, hw, huw⟩ := exists_fixed_pair_lin N h2 hN hNN y hy
        exact case_fixed τ N hτ h2 hN (by rw [phi_eq_of_id τ N hne]; exact hu)
          (by rw [phi_eq_of_id τ N hne]; exact hw) huw
      · push Not at hy
        exact case_scalar τ N hτ h2 hne hy
  · obtain ⟨x, hx⟩ : ∃ x, form x (phi N τ x) ≠ 0 := by
      by_cases hne : ∃ a, τ a ≠ a
      · exact exists_form_phi_ne_of_ne τ N hne hinj
      · push Not at hne
        have hNN : N * N = -1 := by
          rw [map_eq_of_id τ N hne] at hc
          simpa using hc
        obtain ⟨x, hx⟩ := exists_form_ne_of_sq_neg N h2 hN hNN
        exact ⟨x, by rwa [phi_eq_of_id τ N hne]⟩
    exact case_neg τ N hτ h2 hN hc x hx

end CFSG.ClassicalInvolution.Asc77.C25W.Sp
