module

public import CFSG.ClassicalInvolution.Asc77.AscE189Std

public section

namespace CFSG.ClassicalInvolution.Asc77

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Aux

variable {F : Type} [Field F] {n : ℕ}

theorem mulVec_eq_neg_of_mem_center (hn : 1 ≤ n) {ζ : StatedSp n F}
    (hζ : ζ ∈ Subgroup.center (StatedSp n F)) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1)
    (v : Fin n ⊕ Fin n → F) : mat n F ζ *ᵥ v = -v := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hζ
  have hmat : mat n F ζ = Matrix.diagonal (fun _ => (c : F)) := by
    change ((ζ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hsq : (c : F) * c = 1 := by
    have h := congrArg (mat n F) hζ2
    rw [map_mul, hmat, Matrix.diagonal_mul_diagonal, map_one] at h
    have := congrFun (congrFun h (Sum.inl ⟨0, hn⟩)) (Sum.inl ⟨0, hn⟩)
    simpa using this
  have hc1 : (c : F) ≠ 1 := by
    intro h
    apply hζ1
    apply mat_injective
    rw [hmat, h, map_one]
    ext r s
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hcm : (c : F) = -1 := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h hc1
    · exact h
  rw [hmat, mulVec_diagonal_eq, hcm]
  funext t
  simp

end Aux


section LongBlockVec

variable {F : Type} [Field F] {n : ℕ}

theorem longBlock_mulVec_inl (k : Fin n) (A : SL(2, F)) :
    mat n F (longBlock F n k A) *ᵥ Pi.single (Sum.inl k) 1 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 0 • (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) +
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 • (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F) := by
  funext r
  rw [mulVec_single_one_apply, mat_longBlock]
  by_cases h1 : r = Sum.inl k
  · subst h1
    simp [CFSG.LieType.Steinberg.Sp.blockMat]
  · by_cases h2 : r = Sum.inr k
    · subst h2
      simp [CFSG.LieType.Steinberg.Sp.blockMat]
    · simp [CFSG.LieType.Steinberg.Sp.blockMat, h1, h2, Matrix.one_apply]

theorem longBlock_mulVec_inr (k : Fin n) (A : SL(2, F)) :
    mat n F (longBlock F n k A) *ᵥ Pi.single (Sum.inr k) 1 =
      (A : Matrix (Fin 2) (Fin 2) F) 0 1 • (Pi.single (Sum.inl k) 1 : Fin n ⊕ Fin n → F) +
        (A : Matrix (Fin 2) (Fin 2) F) 1 1 • (Pi.single (Sum.inr k) 1 : Fin n ⊕ Fin n → F) := by
  funext r
  rw [mulVec_single_one_apply, mat_longBlock]
  by_cases h1 : r = Sum.inl k
  · subst h1
    simp [CFSG.LieType.Steinberg.Sp.blockMat]
  · by_cases h2 : r = Sum.inr k
    · subst h2
      simp [CFSG.LieType.Steinberg.Sp.blockMat]
    · simp [CFSG.LieType.Steinberg.Sp.blockMat, h1, h2, Matrix.one_apply]

end LongBlockVec

section SpA

variable {F : Type} [Field F]

@[expose] def spA (c : F) (hc : c ≠ 0) : SL(2, F) :=
  mkSL !![0, c⁻¹; -c, 0] (by rw [Matrix.det_fin_two_of]; field_simp; ring)

theorem spA_apply_00 (c : F) (hc : c ≠ 0) : (spA c hc : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := rfl

theorem spA_apply_01 (c : F) (hc : c ≠ 0) : (spA c hc : Matrix (Fin 2) (Fin 2) F) 0 1 = c⁻¹ := rfl

theorem spA_apply_10 (c : F) (hc : c ≠ 0) : (spA c hc : Matrix (Fin 2) (Fin 2) F) 1 0 = -c := rfl

theorem spA_apply_11 (c : F) (hc : c ≠ 0) : (spA c hc : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := rfl

theorem spA_pow_four (c : F) (hc : c ≠ 0) : spA c hc ^ 4 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  have h1 : (spA c hc : Matrix (Fin 2) (Fin 2) F) * (spA c hc : Matrix (Fin 2) (Fin 2) F) =
      -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, spA_apply_00, spA_apply_01, spA_apply_10,
        spA_apply_11, hc]
  calc (spA c hc : Matrix (Fin 2) (Fin 2) F) ^ 4
      = ((spA c hc : Matrix (Fin 2) (Fin 2) F) * (spA c hc : Matrix (Fin 2) (Fin 2) F)) *
        ((spA c hc : Matrix (Fin 2) (Fin 2) F) * (spA c hc : Matrix (Fin 2) (Fin 2) F)) := by
        rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
    _ = 1 := by rw [h1]; simp

end SpA


section Core

variable {F : Type} [Field F]

theorem e189Sp4_std (h2 : (2 : F) ≠ 0) {ζ a : StatedSp 2 F}
    (hζ : ζ ∈ Subgroup.center (StatedSp 2 F)) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1)
    (ha2 : a * a = ζ) (haz : a * longInv F 2 0 * a⁻¹ = ζ * longInv F 2 0) :
    ∃ y α β : StatedSp 2 F, α ∈ longRootSp2 F 2 0 ∧ β ∈ conjSub a (longRootSp2 F 2 0) ∧
      α ^ 4 = 1 ∧ β ^ 4 = 1 ∧ y * a * y⁻¹ = α * β := by
  have hneg := mulVec_eq_neg_of_mem_center (n := 2) (by norm_num) hζ hζ1 hζ2
  have haa : ∀ v, mat 2 F a *ᵥ (mat 2 F a *ᵥ v) = -v := fun v => by
    rw [Matrix.mulVec_mulVec, ← map_mul, ha2, hneg]
  have hda : ∀ v, mat 2 F (longInv F 2 0) *ᵥ (mat 2 F a *ᵥ v) =
      -(mat 2 F a *ᵥ (mat 2 F (longInv F 2 0) *ᵥ v)) := by
    intro v
    have h' : a * longInv F 2 0 = ζ * longInv F 2 0 * a := by
      calc a * longInv F 2 0 = a * longInv F 2 0 * a⁻¹ * a := by group
        _ = ζ * longInv F 2 0 * a := by rw [haz]
    have := congrArg (fun x => mat 2 F x *ᵥ v) h'
    simp only [map_mul, ← Matrix.mulVec_mulVec, hneg] at this
    rw [this, neg_neg]
  have hE0v : ∀ t ∉ coords (0 : Fin 2), (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) t = 0 := by
    intro t ht
    have : t ≠ Sum.inl 0 := fun h => ht (h ▸ inl_mem_coords 0)
    simp [this]
  have hF0v : ∀ t ∉ coords (0 : Fin 2), (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) t = 0 := by
    intro t ht
    have : t ≠ Sum.inr 0 := fun h => ht (h ▸ inr_mem_coords 0)
    simp [this]
  have hE0m : (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) ∈ minusSpace (longInv F 2 0) :=
    (mem_minusSpace_longInv h2 0).mpr hE0v
  have hF0m : (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) ∈ minusSpace (longInv F 2 0) :=
    (mem_minusSpace_longInv h2 0).mpr hF0v
  have hfix : ∀ v ∈ minusSpace (longInv F 2 0), mat 2 F a *ᵥ v ∈ fixSpace (longInv F 2 0) := by
    intro v hv
    rw [mem_fixSpace, hda, mem_minusSpace.mp hv, Matrix.mulVec_neg, neg_neg]
  have hu2v := (mem_fixSpace_longInv h2 0).mp (hfix _ hE0m)
  have hw2v := (mem_fixSpace_longInv h2 0).mp (hfix _ hF0m)
  have hcross : ∀ x y : Fin 2 ⊕ Fin 2 → F, (∀ t ∈ coords (0 : Fin 2), x t = 0) →
      (∀ t ∉ coords (0 : Fin 2), y t = 0) → form x y = 0 ∧ form y x = 0 := fun x y hx hy => by
    have h := form_eq_zero_of_supp (parClosed_coords 0) hx hy
    exact ⟨h, by rw [form_antisymm, h, neg_zero]⟩
  set E0 : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1 with hE0
  set F0 : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inr 0) 1 with hF0
  set E1 : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 1) 1 with hE1
  set F1 : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inr 1) 1 with hF1
  set u₂ : Fin 2 ⊕ Fin 2 → F := mat 2 F a *ᵥ E0 with hu₂
  set w₂ : Fin 2 ⊕ Fin 2 → F := mat 2 F a *ᵥ F0 with hw₂
  have hEF : form E0 F0 = 1 := by
    rw [hF0, form_single_right]
    simp [hE0]
  have hFE : form F0 E0 = -1 := by rw [form_antisymm, hEF]
  have hUW : form u₂ w₂ = 1 := by rw [hu₂, hw₂, form_mulVec]; exact hEF
  have hWU : form w₂ u₂ = -1 := by rw [form_antisymm, hUW]
  have hE0E0 : form E0 E0 = 0 := form_self E0
  have hF0F0 : form F0 F0 = 0 := form_self F0
  have hu2u2 : form u₂ u₂ = 0 := form_self u₂
  have hw2w2 : form w₂ w₂ = 0 := form_self w₂
  obtain ⟨c1, c1'⟩ := hcross u₂ E0 hu2v hE0v
  obtain ⟨c2, c2'⟩ := hcross u₂ F0 hu2v hF0v
  obtain ⟨c3, c3'⟩ := hcross w₂ E0 hw2v hE0v
  obtain ⟨c4, c4'⟩ := hcross w₂ F0 hw2v hF0v
  have hinv : (2 : F)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  have h₁ : form (E0 + w₂) ((2 : F)⁻¹ • F0 + (-(2 : F)⁻¹) • u₂) = 1 := by
    simp only [form_add_left, form_add_right, form_smul_right, hEF,
      hWU, c1', c4]
    linear_combination hinv
  have h₂ : form (u₂ + F0) ((2 : F)⁻¹ • w₂ + (-(2 : F)⁻¹) • E0) = 1 := by
    simp only [form_add_left, form_add_right, form_smul_right, hFE, hUW,
      c1, c4']
    linear_combination hinv
  have o₁ : form (E0 + w₂) (u₂ + F0) = 0 := by
    simp only [form_add_left, form_add_right, hEF,
      hWU, c1', c4]
    ring
  have o₂ : form (E0 + w₂) ((2 : F)⁻¹ • w₂ + (-(2 : F)⁻¹) • E0) = 0 := by
    simp only [form_add_left, form_add_right, form_smul_right,
      hE0E0, hw2w2, c3, c3']
    ring
  have o₃ : form ((2 : F)⁻¹ • F0 + (-(2 : F)⁻¹) • u₂) (u₂ + F0) = 0 := by
    simp only [form_add_left, form_add_right, form_smul_left,
      hF0F0, hu2u2, c2, c2']
    ring
  have o₄ : form ((2 : F)⁻¹ • F0 + (-(2 : F)⁻¹) • u₂)
      ((2 : F)⁻¹ • w₂ + (-(2 : F)⁻¹) • E0) = 0 := by
    simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hFE, hUW,
      c1, c4']
    ring
  obtain ⟨g, hg1, hg2, hg3, hg4⟩ : ∃ g : StatedSp 2 F,
      mat 2 F g *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) = E0 + w₂ ∧
      mat 2 F g *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) =
        (2 : F)⁻¹ • F0 + (-(2 : F)⁻¹) • u₂ ∧
      mat 2 F g *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) = u₂ + F0 ∧
      mat 2 F g *ᵥ (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) =
        (2 : F)⁻¹ • w₂ + (-(2 : F)⁻¹) • E0 :=
    exists_sp_apply_eq_two (m := 0) _ _ _ _ h₁ h₂ o₁ o₂ o₃ o₄
  have hau₂ : mat 2 F a *ᵥ u₂ = -E0 := haa E0
  have haw₂ : mat 2 F a *ᵥ w₂ = -F0 := haa F0
  have ap₁ : mat 2 F a *ᵥ (E0 + w₂) =
      (-2 : F) • ((2 : F)⁻¹ • F0 + (-(2 : F)⁻¹) • u₂) := by
    rw [Matrix.mulVec_add, haw₂]
    have : mat 2 F a *ᵥ E0 = u₂ := rfl
    rw [this]
    match_scalars <;> field_simp
  have aq₁ : mat 2 F a *ᵥ ((2 : F)⁻¹ • F0 + (-(2 : F)⁻¹) • u₂) = (2 : F)⁻¹ • (E0 + w₂) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hau₂]
    have : mat 2 F a *ᵥ F0 = w₂ := rfl
    rw [this]
    module
  have ap₂ : mat 2 F a *ᵥ (u₂ + F0) =
      (2 : F) • ((2 : F)⁻¹ • w₂ + (-(2 : F)⁻¹) • E0) := by
    rw [Matrix.mulVec_add, hau₂]
    have : mat 2 F a *ᵥ F0 = w₂ := rfl
    rw [this]
    match_scalars <;> field_simp
  have aq₂ : mat 2 F a *ᵥ ((2 : F)⁻¹ • w₂ + (-(2 : F)⁻¹) • E0) = (-(2 : F)⁻¹) • (u₂ + F0) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, haw₂]
    have : mat 2 F a *ᵥ E0 = u₂ := rfl
    rw [this]
    module
  have hu0 : mat 2 F (g⁻¹ * a * g) *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) =
      (-2 : F) • (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) := by
    rw [(mulVec_eq_iff g _ _).1 hg1, mulVec_conj_apply, ap₁, Matrix.mulVec_smul,
      ← (mulVec_eq_iff g _ _).1 hg2]
  have hu1 : mat 2 F (g⁻¹ * a * g) *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) =
      (2 : F)⁻¹ • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) := by
    rw [(mulVec_eq_iff g _ _).1 hg2, mulVec_conj_apply, aq₁, Matrix.mulVec_smul,
      ← (mulVec_eq_iff g _ _).1 hg1]
  have hu2 : mat 2 F (g⁻¹ * a * g) *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) =
      (2 : F) • (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) := by
    rw [(mulVec_eq_iff g _ _).1 hg3, mulVec_conj_apply, ap₂, Matrix.mulVec_smul,
      ← (mulVec_eq_iff g _ _).1 hg4]
  have hu3 : mat 2 F (g⁻¹ * a * g) *ᵥ (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) =
      (-(2 : F)⁻¹) • (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) := by
    rw [(mulVec_eq_iff g _ _).1 hg4, mulVec_conj_apply, aq₂, Matrix.mulVec_smul,
      ← (mulVec_eq_iff g _ _).1 hg3]
  have hF2 : (-(2 : F)) ≠ 0 := neg_ne_zero.mpr h2
  set A₁ : SL(2, F) := spA 2 h2 with hA₁
  set A₂ : SL(2, F) := spA (-2) hF2 with hA₂
  have hβfix : ∀ v : Fin 2 ⊕ Fin 2 → F, (∀ t ∈ coords (1 : Fin 2), v t = 0) →
      mat 2 F (longBlock F 2 1 A₂) *ᵥ v = v := fun v hv =>
    mulVec_eq_self_of_isSupp (isSupp_longBlock 1 A₂) hv
  have hαfix : ∀ v : Fin 2 ⊕ Fin 2 → F, (∀ t ∈ coords (0 : Fin 2), v t = 0) →
      mat 2 F (longBlock F 2 0 A₁) *ᵥ v = v := fun v hv =>
    mulVec_eq_self_of_isSupp (isSupp_longBlock 0 A₁) hv
  have hv0 : ∀ t ∈ coords (1 : Fin 2), (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) t = 0 := by
    intro t ht
    rcases mem_coords.1 ht with rfl | rfl <;> simp
  have hv1 : ∀ t ∈ coords (1 : Fin 2), (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) t = 0 := by
    intro t ht
    rcases mem_coords.1 ht with rfl | rfl <;> simp
  have hv2 : ∀ t ∈ coords (0 : Fin 2), (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) t = 0 := by
    intro t ht
    rcases mem_coords.1 ht with rfl | rfl <;> simp
  have hv3 : ∀ t ∈ coords (0 : Fin 2), (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) t = 0 := by
    intro t ht
    rcases mem_coords.1 ht with rfl | rfl <;> simp
  have hαβ0 : mat 2 F (longBlock F 2 0 A₁ * longBlock F 2 1 A₂) *ᵥ
      (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → F) = (-2 : F) • (Pi.single (Sum.inr 0) 1 :
        Fin 2 ⊕ Fin 2 → F) := by
    rw [map_mul, ← Matrix.mulVec_mulVec, hβfix _ hv0, longBlock_mulVec_inl, hA₁, spA_apply_00,
      spA_apply_10]
    simp
  have hαβ1 : mat 2 F (longBlock F 2 0 A₁ * longBlock F 2 1 A₂) *ᵥ
      (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → F) = (2 : F)⁻¹ • (Pi.single (Sum.inl 0) 1 :
        Fin 2 ⊕ Fin 2 → F) := by
    rw [map_mul, ← Matrix.mulVec_mulVec, hβfix _ hv1, longBlock_mulVec_inr, hA₁, spA_apply_01,
      spA_apply_11]
    simp
  have hαβ2 : mat 2 F (longBlock F 2 0 A₁ * longBlock F 2 1 A₂) *ᵥ
      (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → F) = (2 : F) • (Pi.single (Sum.inr 1) 1 :
        Fin 2 ⊕ Fin 2 → F) := by
    rw [map_mul, ← Matrix.mulVec_mulVec, longBlock_mulVec_inl, hA₂, spA_apply_00, spA_apply_10,
      zero_smul, zero_add, Matrix.mulVec_smul, hαfix _ hv3, neg_neg]
  have hαβ3 : mat 2 F (longBlock F 2 0 A₁ * longBlock F 2 1 A₂) *ᵥ
      (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → F) = (-(2 : F)⁻¹) • (Pi.single (Sum.inl 1) 1 :
        Fin 2 ⊕ Fin 2 → F) := by
    rw [map_mul, ← Matrix.mulVec_mulVec, longBlock_mulVec_inr, hA₂, spA_apply_01, spA_apply_11,
      zero_smul, add_zero, Matrix.mulVec_smul, hαfix _ hv2, inv_neg]
  have hu : g⁻¹ * a * g = longBlock F 2 0 A₁ * longBlock F 2 1 A₂ := by
    apply mat_injective
    apply Matrix.ext_of_mulVec_single
    intro b
    rcases b with (i | i)
    · revert i
      rw [Fin.forall_fin_two]
      exact ⟨by rw [hu0, hαβ0], by rw [hu2, hαβ2]⟩
    · revert i
      rw [Fin.forall_fin_two]
      exact ⟨by rw [hu1, hαβ1], by rw [hu3, hαβ3]⟩
  refine ⟨g⁻¹, longBlock F 2 0 A₁, longBlock F 2 1 A₂, ⟨A₁, rfl⟩, ?_, ?_, ?_, ?_⟩
  · have hconj : conjSub a (longRootSp2 F 2 0) = longRootGroup (ζ * longInv F 2 0) := by
      rw [longRootSp2, range_longBlock_eq_longRootGroup h2, ← haz]
      exact (longRootGroup_conj _ a).symm
    rw [hconj, mem_longRootGroup]
    intro v hv
    have hv' : mat 2 F (longInv F 2 0) *ᵥ v = -v := by
      have := mem_fixSpace.mp hv
      rw [map_mul, ← Matrix.mulVec_mulVec, hneg] at this
      have h := congrArg Neg.neg this
      simpa using h
    apply hβfix
    intro t ht
    exact (mem_minusSpace_longInv h2 0).mp (mem_minusSpace.mpr hv') t
      (coords_subset_compl (by decide) ht)
  · rw [← map_pow, hA₁, spA_pow_four, map_one]
  · rw [← map_pow, hA₂, spA_pow_four, map_one]
  · rw [inv_inv]
    exact hu

end Core


section Model

variable {p e : ℕ} [Fact p.Prime]

theorem e189ModelAt_psp_two (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSp 2 p e) : E189ModelAt p e .PSp 2 := by
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hfund : fundamentalSubgroups .PSp (modelUniv .PSp 2 p e Fact.out).D =
      {F | ∃ g : StatedSp 2 (GaloisField p e),
        F = conjSub g (longRootSp2 (GaloisField p e) 2 0)} := by
    rw [fundamentalSubgroups_psp_eq hadm]
    ext R
    exact (exists_conj_longBlock_iff 0 R).symm
  have hcl := isClassicalSL2_longRootSp2 h2 (0 : Fin 2)
  have key : E189AtFam (StatedSp 2 (GaloisField p e))
      {F | ∃ g : StatedSp 2 (GaloisField p e),
        F = conjSub g (longRootSp2 (GaloisField p e) 2 0)} :=
    e189AtFam_of_conjClass (isUniqueInvolution_of_isClassicalSL2 hcl hodd)
      (fun c hc => conjSub_eq_of_isClassicalSL2 hcl hc)
      (fun ζ hζ hζ1 hζ2 a ha2 haz => e189Sp4_std h2 hζ hζ1 hζ2 ha2 haz)
  unfold E189ModelAt modelFund ModelGrp
  rw [hfund]
  exact key

end Model

end CFSG.ClassicalInvolution.Asc77
