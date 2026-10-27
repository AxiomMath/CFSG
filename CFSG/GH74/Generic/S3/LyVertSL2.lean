module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAut
public import CFSG.ClassicalInvolution.SL2Facts
public import CFSG.LocalAnalysis.ComponentInitial.SwappedQuasisimple

public section

namespace CFSG.GH74.Generic.S3

open Matrix CFSG.ABGLocalTools CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

variable {F : Type} [Field F]

@[expose] noncomputable def glConj (G : GL (Fin 2) F) : SL(2, F) ≃* SL(2, F) where
  toFun a := ⟨(G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
      ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]⟩
  invFun a := ⟨((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
      (G : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]⟩
  left_inv a := by
    apply Subtype.ext
    have h1 : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (G : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
        (G : Matrix (Fin 2) (Fin 2) F) = a
    calc _ = (((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) *
          (a : Matrix (Fin 2) (Fin 2) F) *
          (((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) := by
          simp only [Matrix.mul_assoc]
      _ = a := by rw [h1]; simp
  right_inv a := by
    apply Subtype.ext
    have h1 : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (G : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (G : Matrix (Fin 2) (Fin 2) F) *
        (((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
          (G : Matrix (Fin 2) (Fin 2) F)) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = a
    calc _ = ((G : Matrix (Fin 2) (Fin 2) F) * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
          (a : Matrix (Fin 2) (Fin 2) F) *
          ((G : Matrix (Fin 2) (Fin 2) F) * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
          simp only [Matrix.mul_assoc]
      _ = a := by rw [h2]; simp
  map_mul' a b := by
    apply Subtype.ext
    have h1 : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    show (G : Matrix (Fin 2) (Fin 2) F) * ((a * b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
      ((G : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    rw [Matrix.SpecialLinearGroup.coe_mul]
    calc (G : Matrix (Fin 2) (Fin 2) F) *
          ((a : Matrix (Fin 2) (Fin 2) F) * (b : Matrix (Fin 2) (Fin 2) F)) *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = (G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
          (((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)) *
          (b : Matrix (Fin 2) (Fin 2) F) * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_glConj (G : GL (Fin 2) F) (a : SL(2, F)) :
    ((glConj G a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) *
        ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl

theorem glConj_mul (G H : GL (Fin 2) F) (a : SL(2, F)) :
    glConj (G * H) a = glConj G (glConj H a) := by
  apply Subtype.ext
  simp only [coe_glConj, Units.val_mul, _root_.mul_inv_rev, Matrix.mul_assoc]

theorem glConj_one (a : SL(2, F)) : glConj (1 : GL (Fin 2) F) a = a := by
  apply Subtype.ext
  simp [coe_glConj]

@[expose] noncomputable def glConjHom : GL (Fin 2) F →* MulAut SL(2, F) where
  toFun := glConj
  map_one' := by ext a : 1; exact glConj_one a
  map_mul' G H := by ext a : 1; exact glConj_mul G H a

theorem glConjHom_apply (G : GL (Fin 2) F) (a : SL(2, F)) : glConjHom G a = glConj G a := rfl

@[expose] noncomputable def sl2Map (σ : F ≃+* F) : SL(2, F) ≃* SL(2, F) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map σ.toRingHom)
    (Matrix.SpecialLinearGroup.map σ.symm.toRingHom)
    (by
      ext a : 1
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])
    (by
      ext a : 1
      apply Subtype.ext
      ext i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe])

theorem coe_sl2Map (σ : F ≃+* F) (a : SL(2, F)) :
    ((sl2Map σ a : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = (a : Matrix (Fin 2) (Fin 2) F).map σ := by
  simp [sl2Map, Matrix.SpecialLinearGroup.map_apply_coe]

theorem glConj_scalar (z : Fˣ) (a : SL(2, F)) :
    glConj (GeneralLinearGroup.scalar (Fin 2) z) a = a := by
  apply Subtype.ext
  rw [coe_glConj, ← map_inv, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar]
  ext i j
  simp only [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  simp
  field_simp

theorem sl2Map_glConj (σ : F ≃+* F) (Q : GL (Fin 2) F) (a : SL(2, F)) :
    sl2Map σ (glConj Q a) = glConj (GeneralLinearGroup.map σ.toRingHom Q) (sl2Map σ a) := by
  apply Subtype.ext
  rw [coe_sl2Map, coe_glConj, coe_glConj, coe_sl2Map]
  have h1 : ((GeneralLinearGroup.map σ.toRingHom Q : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (Q : Matrix (Fin 2) (Fin 2) F).map σ := rfl
  have h2 : (((GeneralLinearGroup.map σ.toRingHom Q)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((Q⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ := by
    rw [← map_inv]
    rfl
  rw [h1, h2, Matrix.map_mul, Matrix.map_mul]

theorem cross_zero {g1 g2 g3 u1 u2 u3 v1 v2 v3 : F} (hg : g1 ≠ 0 ∨ g2 ≠ 0 ∨ g3 ≠ 0)
    (hu12 : u1 * g2 = u2 * g1) (hu13 : u1 * g3 = u3 * g1) (hu23 : u2 * g3 = u3 * g2)
    (hv12 : v1 * g2 = v2 * g1) (hv13 : v1 * g3 = v3 * g1) (hv23 : v2 * g3 = v3 * g2) :
    u1 * v2 = u2 * v1 ∧ u1 * v3 = u3 * v1 ∧ u2 * v3 = u3 * v2 := by
  rcases hg with h | h | h
  · have hu2 : u2 = u1 * g2 / g1 := by rw [eq_div_iff h]; exact hu12.symm
    have hu3 : u3 = u1 * g3 / g1 := by rw [eq_div_iff h]; exact hu13.symm
    have hv2 : v2 = v1 * g2 / g1 := by rw [eq_div_iff h]; exact hv12.symm
    have hv3 : v3 = v1 * g3 / g1 := by rw [eq_div_iff h]; exact hv13.symm
    subst hu2 hu3 hv2 hv3
    refine ⟨by ring, by ring, by ring⟩
  · have hu1 : u1 = u2 * g1 / g2 := by rw [eq_div_iff h]; exact hu12
    have hu3 : u3 = u2 * g3 / g2 := by rw [eq_div_iff h]; exact hu23.symm
    have hv1 : v1 = v2 * g1 / g2 := by rw [eq_div_iff h]; exact hv12
    have hv3 : v3 = v2 * g3 / g2 := by rw [eq_div_iff h]; exact hv23.symm
    subst hu1 hu3 hv1 hv3
    refine ⟨by ring, by ring, by ring⟩
  · have hu1 : u1 = u3 * g1 / g3 := by rw [eq_div_iff h]; exact hu13
    have hu2 : u2 = u3 * g2 / g3 := by rw [eq_div_iff h]; exact hu23
    have hv1 : v1 = v3 * g1 / g3 := by rw [eq_div_iff h]; exact hv13
    have hv2 : v2 = v3 * g2 / g3 := by rw [eq_div_iff h]; exact hv23
    subst hu1 hu2 hv1 hv2
    refine ⟨by ring, by ring, by ring⟩

theorem commute_of_commute_nonscalar {G A B : Matrix (Fin 2) (Fin 2) F}
    (hG : ¬ ∃ r : F, G = Matrix.scalar (Fin 2) r) (hA : A * G = G * A) (hB : B * G = G * B) :
    A * B = B * A := by
  have hg : G 0 1 ≠ 0 ∨ G 1 0 ≠ 0 ∨ G 0 0 - G 1 1 ≠ 0 := by
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply hG
    refine ⟨G 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.scalar_apply, h1, h2]
    linear_combination -h3
  have eA := fun i j => congrFun (congrFun hA i) j
  have eB := fun i j => congrFun (congrFun hB i) j
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at eA eB
  have a00 := eA 0 0
  have a01 := eA 0 1
  have a10 := eA 1 0
  have b00 := eB 0 0
  have b01 := eB 0 1
  have b10 := eB 1 0
  obtain ⟨c1, c2, c3⟩ := cross_zero (g1 := G 0 1) (g2 := G 1 0) (g3 := G 0 0 - G 1 1)
    (u1 := A 0 1) (u2 := A 1 0) (u3 := A 0 0 - A 1 1) (v1 := B 0 1) (v2 := B 1 0)
    (v3 := B 0 0 - B 1 1) hg (by linear_combination a00) (by linear_combination -a01)
    (by linear_combination a10) (by linear_combination b00) (by linear_combination -b01)
    (by linear_combination b10)
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination c1
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -c2
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination c3
  · simp only [Fin.mk_one, Fin.isValue, Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination -c1

theorem eq_of_inv_mul_mem_center {P Q : Type*} [Group P] [Group Q] (hP : Group.IsPerfect P)
    (f g : P →* Q) (h : ∀ b, (f b)⁻¹ * g b ∈ Subgroup.center Q) : f = g := by
  have hcomm : commutator P ≤ f.eqLocus g := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hga : g a = f a * ((f a)⁻¹ * g a) := by group
    have hgb : g b = f b * ((f b)⁻¹ * g b) := by group
    have hc1 := h a
    have hc2 := h b
    change f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hga, hgb]
    have hz1 : Commute ((f a)⁻¹ * g a) (f b) := (Subgroup.mem_center_iff.mp hc1 (f b)).symm
    have hz2 : Commute ((f a)⁻¹ * g a) ((f b)⁻¹ * g b) := (Subgroup.mem_center_iff.mp hc1 _).symm
    have hz3 : Commute ((f b)⁻¹ * g b) (f a) := (Subgroup.mem_center_iff.mp hc2 (f a)).symm
    exact (CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_of_commute hz1 hz2 hz3).symm
  have htop : f.eqLocus g = ⊤ := by
    rw [eq_top_iff, ← hP.commutator_eq_top]
    exact hcomm
  ext b
  have : b ∈ f.eqLocus g := by rw [htop]; exact Subgroup.mem_top b
  exact this

theorem fix_glConj_abelian {G : GL (Fin 2) F}
    (hG : ¬ ∃ r : F, (G : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r)
    {a b : SL(2, F)} (ha : glConj G a = a) (hb : glConj G b = b) : a * b = b * a := by
  have h1 : ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : ∀ c : SL(2, F), glConj G c = c →
      (c : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F) =
        (G : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    intro c hcc
    have := congrArg Subtype.val hcc
    rw [coe_glConj] at this
    calc (c : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F)
        = ((G : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) *
            ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F) := by
          rw [this]
      _ = (G : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact commute_of_commute_nonscalar hG (hc a ha) (hc b hb)

theorem exists_fixed_matrix (σ : F ≃+* F) (hσ : σ ≠ 1) (hσσ : ∀ x, σ (σ x) = x)
    (h2 : (2 : F) ≠ 0) (G : Matrix (Fin 2) (Fin 2) F) (hG : G * G.map σ = 1)
    (hdet : G.det ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) F, P.det ≠ 0 ∧ G * P.map σ = P := by
  have h00 : G 0 0 * σ (G 0 0) + G 0 1 * σ (G 1 0) = 1 := by
    have := congrFun (congrFun hG 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : G 0 0 * σ (G 0 1) + G 0 1 * σ (G 1 1) = 0 := by
    have := congrFun (congrFun hG 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : G 1 0 * σ (G 0 0) + G 1 1 * σ (G 1 0) = 0 := by
    have := congrFun (congrFun hG 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : G 1 0 * σ (G 0 1) + G 1 1 * σ (G 1 1) = 1 := by
    have := congrFun (congrFun hG 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  obtain ⟨t, ht⟩ : ∃ t : F, σ t ≠ t := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  set ε : F := t - σ t with hε
  have hσε : σ ε = -ε := by rw [hε, map_sub, hσσ]; ring
  have hε0 : ε ≠ 0 := by
    intro h
    apply ht
    rw [hε] at h
    exact (sub_eq_zero.mp h).symm
  let ψ0 : F → F → F := fun a b => G 0 0 * σ a + G 0 1 * σ b
  let ψ1 : F → F → F := fun a b => G 1 0 * σ a + G 1 1 * σ b
  have hv : ∃ a b : F, a * ψ1 a b - b * ψ0 a b ≠ 0 := by
    by_contra hall
    push Not at hall
    have d1 := hall 1 0
    have d2 := hall 0 1
    have d3 := hall 1 1
    have d4 := hall ε 1
    simp only [ψ0, ψ1, map_one, map_zero, mul_one, mul_zero, add_zero, zero_add, one_mul,
      zero_mul, sub_zero, hσε] at d1 d2 d3 d4
    have g10 : G 1 0 = 0 := by linear_combination d1
    have g01 : G 0 1 = 0 := by linear_combination -d2
    have g11 : G 1 1 = G 0 0 := by
      rw [g10, g01] at d3
      linear_combination d3
    have ha : G 0 0 = 0 := by
      rw [g10, g01, g11] at d4
      have : (2 * ε) * G 0 0 = 0 := by linear_combination d4
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero h2 hε0)
      · exact h
    apply hdet
    rw [Matrix.det_fin_two, g10, g01, g11, ha]
    ring
  obtain ⟨a, b, hab⟩ := hv
  refine ⟨!![a + ψ0 a b, ε * (a - ψ0 a b); b + ψ1 a b, ε * (b - ψ1 a b)], ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have : (a + ψ0 a b) * (ε * (b - ψ1 a b)) - ε * (a - ψ0 a b) * (b + ψ1 a b) =
        (-2 * ε) * (a * ψ1 a b - b * ψ0 a b) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hε0) hab
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ψ0, ψ1, Matrix.mul_apply, Fin.sum_univ_two, hσσ, map_add, map_mul, hσε]
    · linear_combination a * h00 + b * h01
    · linear_combination (ε * a) * h00 + (ε * b) * h01
    · linear_combination a * h10 + b * h11
    · linear_combination (ε * a) * h10 + (ε * b) * h11

theorem sl2Map_one (a : SL(2, F)) : sl2Map (1 : F ≃+* F) a = a := by
  apply Subtype.ext
  rw [coe_sl2Map]
  ext i j
  simp

theorem sl2_involution_normal_form [Finite F] (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (β : MulAut SL(2, F)) (hβ : β * β = 1) (hout : β ∉ (glConjHom (F := F)).range) :
    ∃ (σ : F ≃+* F) (P : GL (Fin 2) F), σ ≠ 1 ∧ (∀ x, σ (σ x) = x) ∧
      ∀ a : SL(2, F), β a = glConj P (sl2Map σ (glConj P⁻¹ a)) := by
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  have h2F : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have hK : IsOddPrimePower (Nat.card F) := isOddPrimePower_card_of_odd hodd
  obtain ⟨f, -, hKcard⟩ := card_eq_ringChar_pow (F := F)
  have : Fact (ringChar F).Prime := ⟨ringChar_prime⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F hKcard hK h3 (psl2MulAutOf β)
  have hγ2 : γ ^ 2 = 1 := by
    apply pGammaL2ToMulAutPSL2_injective F hK h3
    rw [map_pow, hγ, psl2MulAutOf_pow_eq_one (p := 2) (by rw [pow_two]; exact hβ), map_one]
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective γ.left
  set σ : F ≃+* F := γ.right with hσdef
  have hσ2 : σ ^ 2 = 1 := by
    rw [hσdef, ← pGammaL2_pow_right, hγ2, SemidirectProduct.one_right]
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have := DFunLike.congr_fun hσ2 x
    simpa [pow_two, RingAut.mul_apply] using this
  have hN := pGammaL2_pow_left γ G hG 2
  rw [hγ2, SemidirectProduct.one_left] at hN
  have hNc : glNorm σ G 2 ∈ Subgroup.center (GL (Fin 2) F) :=
    ProjGenLinGroup.mk_eq_one.mp hN.symm
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hNc
  have hGnorm : (glNorm σ G 2 : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F).map σ := by
    have e1 : ((GeneralLinearGroup.map ((σ ^ 0 : F ≃+* F) : F →+* F) G : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = (G : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      simp [GeneralLinearGroup.map]
    have e2 : ((GeneralLinearGroup.map ((σ ^ 1 : F ≃+* F) : F →+* F) G : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = (G : Matrix (Fin 2) (Fin 2) F).map σ := by
      ext i j
      simp [GeneralLinearGroup.map]
    rw [glNorm_succ, glNorm_succ, glNorm_zero, Units.val_mul, Units.val_mul, Units.val_one,
      one_mul, e1, e2]
  have hGs : (G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F).map σ =
      Matrix.scalar (Fin 2) c := by
    rw [← hGnorm, ← hc]
  have hu := coe_mulAut_eq_smul_conj hK h3 β γ hγ G hG
  have h4 : 4 ≤ Nat.card F := by omega
  have hρ : ∀ b : SL(2, F), β b = glConj G (sl2Map σ b) := by
    have hcen : ∀ b, (β.toMonoidHom b)⁻¹ * (((sl2Map σ).trans (glConj G)).toMonoidHom b) ∈
        Subgroup.center SL(2, F) := by
      intro b
      obtain ⟨u, hu0, hub⟩ := hu b
      change (β b)⁻¹ * glConj G (sl2Map σ b) ∈ Subgroup.center SL(2, F)
      set X : SL(2, F) := β b with hX
      set Y : SL(2, F) := glConj G (sl2Map σ b) with hY
      have hYmat : (Y : Matrix (Fin 2) (Fin 2) F) = (G : Matrix (Fin 2) (Fin 2) F) *
          (b : Matrix (Fin 2) (Fin 2) F).map σ * ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
        rw [hY, coe_glConj, coe_sl2Map]
      have hXY : (X : Matrix (Fin 2) (Fin 2) F) = u • (Y : Matrix (Fin 2) (Fin 2) F) := by
        rw [hYmat]; exact hub
      have hu2 : u ^ 2 = 1 := by
        have h1 := congrArg Matrix.det hXY
        rw [Matrix.SpecialLinearGroup.det_coe, Matrix.det_smul, Matrix.SpecialLinearGroup.det_coe,
          Fintype.card_fin, mul_one] at h1
        exact h1.symm
      have hYX : (Y : Matrix (Fin 2) (Fin 2) F) = u⁻¹ • (X : Matrix (Fin 2) (Fin 2) F) := by
        rw [hXY, smul_smul, inv_mul_cancel₀ hu0, one_smul]
      have hXiX : ((X⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (X : Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
      rw [Matrix.SpecialLinearGroup.mem_center_iff]
      refine ⟨u⁻¹, ?_, ?_⟩
      · rw [Fintype.card_fin, inv_pow, hu2, inv_one]
      · rw [Matrix.SpecialLinearGroup.coe_mul, hYX, Matrix.mul_smul, hXiX, Matrix.scalar_apply,
          Matrix.smul_one_eq_diagonal]
    have := eq_of_inv_mul_mem_center (CFSG.ClassicalInvolution.sl2_isPerfect h4) β.toMonoidHom
      ((sl2Map σ).trans (glConj G)).toMonoidHom hcen
    intro b
    exact DFunLike.congr_fun this b
  by_cases hσ1 : σ = 1
  · exfalso
    apply hout
    refine ⟨G, ?_⟩
    refine MulEquiv.ext fun a => ?_
    rw [glConjHom_apply, hρ a, hσ1, sl2Map_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf σ = 2 := orderOf_eq_prime hσ2 hσ1
  have hdetG : (G : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    have := (Matrix.GeneralLinearGroup.det G).ne_zero
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hc0 : c ≠ 0 := by
    intro hc0
    have h1 := congrArg Matrix.det hGs
    have h2 : ((G : Matrix (Fin 2) (Fin 2) F).map σ).det = σ (G : Matrix (Fin 2) (Fin 2) F).det := by
      have := RingHom.map_det σ.toRingHom (G : Matrix (Fin 2) (Fin 2) F)
      simpa using this.symm
    rw [Matrix.det_mul, h2] at h1
    have h3 : Matrix.det (Matrix.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) F) = c ^ 2 := by
      simp [Matrix.scalar_apply, Matrix.det_diagonal]
    rw [h3, hc0] at h1
    have h4 : (G : Matrix (Fin 2) (Fin 2) F).det * σ (G : Matrix (Fin 2) (Fin 2) F).det = 0 := by
      rw [h1]; ring
    rcases mul_eq_zero.mp h4 with h | h
    · exact hdetG h
    · exact hdetG (by simpa using h)
  have hσc : σ c = c := by
    have h1 : (c⁻¹ • (G : Matrix (Fin 2) (Fin 2) F)) * (G : Matrix (Fin 2) (Fin 2) F).map σ = 1 := by
      rw [Matrix.smul_mul, hGs, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have h2 := mul_eq_one_comm.mp h1
    have hcom : (G : Matrix (Fin 2) (Fin 2) F).map σ * (G : Matrix (Fin 2) (Fin 2) F) =
        Matrix.scalar (Fin 2) c := by
      have h3 : (G : Matrix (Fin 2) (Fin 2) F).map σ * (c⁻¹ • (G : Matrix (Fin 2) (Fin 2) F)) = 1 := h2
      rw [Matrix.mul_smul] at h3
      have h4 : c • ((c⁻¹ : F) • ((G : Matrix (Fin 2) (Fin 2) F).map σ * (G : Matrix (Fin 2) (Fin 2) F))) =
          c • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [h3]
      rw [smul_smul, mul_inv_cancel₀ hc0, one_smul] at h4
      rw [h4, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have hmapmul : ((G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F).map σ).map σ =
        (G : Matrix (Fin 2) (Fin 2) F).map σ * (G : Matrix (Fin 2) (Fin 2) F) := by
      rw [Matrix.map_mul]
      congr 1
      ext i j
      simp [hσσ]
    have hmapc : ((G : Matrix (Fin 2) (Fin 2) F) * (G : Matrix (Fin 2) (Fin 2) F).map σ).map σ =
        Matrix.scalar (Fin 2) (σ c) := by
      rw [hGs]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    have h5 := hmapmul.symm.trans hmapc
    have h6 := congrFun (congrFun (hcom.symm.trans h5) 0) 0
    simpa [Matrix.scalar_apply] using h6.symm
  obtain ⟨d, hd⟩ := exists_prod_pow_eq σ hσc
  rw [hord] at hd
  simp only [Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, pow_zero,
    pow_one] at hd
  have hd' : d * σ d = c := by simpa using hd
  have hd0 : d ≠ 0 := fun h => hc0 (by rw [← hd', h]; simp)
  have hσd0 : σ d ≠ 0 := fun h => hd0 (by simpa using h)
  set G' : Matrix (Fin 2) (Fin 2) F := d⁻¹ • (G : Matrix (Fin 2) (Fin 2) F) with hG'def
  have hG'σ : G'.map σ = (σ d)⁻¹ • (G : Matrix (Fin 2) (Fin 2) F).map σ := by
    ext i j
    simp [hG'def]
  have hG'1 : G' * G'.map σ = 1 := by
    rw [hG'σ, hG'def, Matrix.smul_mul, Matrix.mul_smul, hGs, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, smul_smul, smul_smul]
    have : d⁻¹ * (σ d)⁻¹ * c = 1 := by
      rw [← hd']
      field_simp
    rw [this, one_smul]
  have hdetG' : G'.det ≠ 0 := by
    rw [hG'def, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hd0)) hdetG
  obtain ⟨P, hPdet, hP⟩ := exists_fixed_matrix σ hσ1 hσσ h2F G' hG'1 hdetG'
  let Pu : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet
  have hPu : (Pu : Matrix (Fin 2) (Fin 2) F) = P := rfl
  refine ⟨σ, Pu, hσ1, hσσ, fun a => ?_⟩
  let zd : Fˣ := Units.mk0 d hd0
  let Gs' : GL (Fin 2) F := GeneralLinearGroup.scalar (Fin 2) zd⁻¹ * G
  have hGs'mat : (Gs' : Matrix (Fin 2) (Fin 2) F) = G' := by
    simp only [Gs', Units.val_mul, GeneralLinearGroup.coe_scalar, hG'def]
    ext i j
    simp [Matrix.scalar_apply, zd, Matrix.diagonal_mul]
  have hGG : G = GeneralLinearGroup.scalar (Fin 2) zd * Gs' := by
    simp only [Gs', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hfix : Gs' * GeneralLinearGroup.map σ.toRingHom Pu = Pu := by
    apply Units.ext
    rw [Units.val_mul, hGs'mat, hPu]
    exact hP
  have hGs'eq : Gs' = Pu * (GeneralLinearGroup.map σ.toRingHom Pu)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hfix
  calc β a = glConj G (sl2Map σ a) := hρ a
    _ = glConj (GeneralLinearGroup.scalar (Fin 2) zd * Gs') (sl2Map σ a) := by rw [← hGG]
    _ = glConj (GeneralLinearGroup.scalar (Fin 2) zd) (glConj Gs' (sl2Map σ a)) := glConj_mul _ _ _
    _ = glConj Gs' (sl2Map σ a) := glConj_scalar _ _
    _ = glConj (Pu * (GeneralLinearGroup.map σ.toRingHom Pu)⁻¹) (sl2Map σ a) := by rw [hGs'eq]
    _ = glConj Pu (glConj (GeneralLinearGroup.map σ.toRingHom Pu)⁻¹ (sl2Map σ a)) := glConj_mul _ _ _
    _ = glConj Pu (sl2Map σ (glConj Pu⁻¹ a)) := by rw [sl2Map_glConj, map_inv]

theorem glConj_toGL (a b : SL(2, F)) :
    glConj (Matrix.SpecialLinearGroup.toGL a) b = a * b * a⁻¹ := by
  apply Subtype.ext
  rw [coe_glConj, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have : (((Matrix.SpecialLinearGroup.toGL a)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((a⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← map_inv]
    rfl
  rw [this]
  rfl

theorem eq_one_of_mem_range_of_fix_nonabelian {β : MulAut SL(2, F)}
    (hβ : β ∈ (glConjHom (F := F)).range)
    (hna : ∃ a b : SL(2, F), β a = a ∧ β b = b ∧ a * b ≠ b * a) : β = 1 := by
  obtain ⟨G, rfl⟩ := hβ
  by_cases hs : ∃ r : F, (G : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) r
  · obtain ⟨r, hr⟩ := hs
    have hr0 : r ≠ 0 := by
      intro h0
      have h1 : (G : Matrix (Fin 2) (Fin 2) F) = 0 := by
        rw [hr, h0]; simp
      have h2 := (Matrix.GeneralLinearGroup.det G).ne_zero
      apply h2
      simp [Matrix.GeneralLinearGroup.val_det_apply, h1]
    have hG : G = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 r hr0) := by
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar, hr]
      rfl
    refine MulEquiv.ext fun a => ?_
    rw [glConjHom_apply, hG, glConj_scalar]
    rfl
  · exfalso
    obtain ⟨a, b, ha, hb, hab⟩ := hna
    exact hab (fix_glConj_abelian hs ha hb)

@[expose] noncomputable def diagSL (ε : Fˣ) : SL(2, F) :=
  ⟨Matrix.diagonal ![(ε : F), (ε⁻¹ : Fˣ)], by
    rw [Matrix.det_diagonal]; simp⟩

theorem coe_diagSL (ε : Fˣ) :
    ((diagSL ε : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![(ε : F), (ε⁻¹ : Fˣ)] := rfl

theorem exists_neg_of_normal_form {σ : F ≃+* F} {P : GL (Fin 2) F} (hσ : σ ≠ 1)
    (hσσ : ∀ x, σ (σ x) = x) {β : MulAut SL(2, F)}
    (hβ : ∀ a, β a = glConj P (sl2Map σ (glConj P⁻¹ a))) :
    ∃ ℓ : SL(2, F), β ℓ = (-1 : SL(2, F)) * ℓ := by
  obtain ⟨t, ht⟩ : ∃ t : F, σ t ≠ t := by
    by_contra hall
    push Not at hall
    exact hσ (RingEquiv.ext hall)
  set ε : F := t - σ t with hε
  have hσε : σ ε = -ε := by rw [hε, map_sub, hσσ]; ring
  have hε0 : ε ≠ 0 := by
    intro h
    apply ht
    rw [hε] at h
    exact (sub_eq_zero.mp h).symm
  let εu : Fˣ := Units.mk0 ε hε0
  refine ⟨glConj P (diagSL εu), ?_⟩
  have h1 : β (glConj P (diagSL εu)) = glConj P (sl2Map σ (diagSL εu)) := by
    rw [hβ, ← glConj_mul, inv_mul_cancel, glConj_one]
  have h2 : sl2Map σ (diagSL εu) = (-1 : SL(2, F)) * diagSL εu := by
    apply Subtype.ext
    rw [coe_sl2Map, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, coe_diagSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hσε, εu]
  have h3 : glConj P ((-1 : SL(2, F)) * diagSL εu) = (-1 : SL(2, F)) * glConj P (diagSL εu) := by
    rw [map_mul]
    congr 1
    apply Subtype.ext
    rw [coe_glConj, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    have : (P : Matrix (Fin 2) (Fin 2) F) * (-1 : Matrix (Fin 2) (Fin 2) F) *
        ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
      rw [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [this]
  rw [h1, h2, h3]

@[expose] def fixSub (β : MulAut SL(2, F)) : Subgroup SL(2, F) :=
  β.toMonoidHom.eqLocus (MonoidHom.id _)

theorem mem_fixSub {β : MulAut SL(2, F)} {a : SL(2, F)} : a ∈ fixSub β ↔ β a = a := Iff.rfl

theorem exists_sl2_equiv_fixSub [Finite F] {σ : F ≃+* F} {P : GL (Fin 2) F} {β : MulAut SL(2, F)}
    (hβ : ∀ a, β a = glConj P (sl2Map σ (glConj P⁻¹ a))) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀) (ι : F₀ →+* F), Function.Injective ι ∧
      Nonempty (SL(2, F₀) ≃* ↥(fixSub β)) := by
  let F₀ : Subfield F := RingHom.eqLocusField σ.toRingHom (RingHom.id F)
  have hF₀ : ∀ x : F, x ∈ F₀ ↔ σ x = x := fun x => Iff.rfl
  let ι : F₀ →+* F := F₀.subtype
  have hι : Function.Injective ι := Subtype.val_injective
  let φ : SL(2, F₀) →* SL(2, F) :=
    (glConj P).toMonoidHom.comp (Matrix.SpecialLinearGroup.map ι)
  have hφmat : ∀ A : SL(2, F₀), ((φ A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (P : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F₀).map ι *
        ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro A
    rfl
  have hinj : Function.Injective φ := by
    intro A B hAB
    have h1 : Matrix.SpecialLinearGroup.map ι A = Matrix.SpecialLinearGroup.map ι B :=
      (glConj P).injective hAB
    have h2 := congrArg (fun C : SL(2, F) => (C : Matrix (Fin 2) (Fin 2) F)) h1
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h2
    exact Subtype.ext (Matrix.ext fun i j => hι (congrFun (congrFun h2 i) j))
  have hrange : φ.range = fixSub β := by
    ext a
    constructor
    · rintro ⟨A, rfl⟩
      rw [mem_fixSub, hβ]
      have : sl2Map σ (glConj P⁻¹ (φ A)) = Matrix.SpecialLinearGroup.map ι A := by
        apply Subtype.ext
        rw [coe_sl2Map]
        have : glConj P⁻¹ (φ A) = Matrix.SpecialLinearGroup.map ι A := by
          show glConj P⁻¹ (glConj P _) = _
          rw [← glConj_mul, inv_mul_cancel, glConj_one]
        rw [this, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
        ext i j
        exact (A i j).2
      rw [this]
      rfl
    · intro ha
      rw [mem_fixSub, hβ] at ha
      set B : SL(2, F) := glConj P⁻¹ a with hB
      have hσB : sl2Map σ B = B := by
        have h1 : glConj P (sl2Map σ B) = glConj P B := by
          rw [ha, hB, ← glConj_mul, mul_inv_cancel, glConj_one]
        exact (glConj P).injective h1
      have hentry : ∀ i j, σ ((B : Matrix (Fin 2) (Fin 2) F) i j) = (B : Matrix (Fin 2) (Fin 2) F) i j := by
        intro i j
        have := congrArg (fun C : SL(2, F) => (C : Matrix (Fin 2) (Fin 2) F) i j) hσB
        simpa [coe_sl2Map] using this
      let Amat : Matrix (Fin 2) (Fin 2) F₀ := Matrix.of fun i j =>
        ⟨(B : Matrix (Fin 2) (Fin 2) F) i j, (hF₀ _).2 (hentry i j)⟩
      have hAmap : Amat.map ι = (B : Matrix (Fin 2) (Fin 2) F) := by
        ext i j
        rfl
      have hAdet : Amat.det = 1 := by
        apply hι
        rw [map_one]
        have h1 := RingHom.map_det ι Amat
        rw [RingHom.mapMatrix_apply, hAmap, Matrix.SpecialLinearGroup.det_coe] at h1
        exact h1
      let Asl : SL(2, F₀) := ⟨Amat, hAdet⟩
      refine ⟨Asl, ?_⟩
      have h2 : Matrix.SpecialLinearGroup.map ι Asl = B := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
        exact hAmap
      show glConj P (Matrix.SpecialLinearGroup.map ι Asl) = a
      rw [h2, hB, ← glConj_mul, mul_inv_cancel, glConj_one]
  refine ⟨F₀, inferInstance, inferInstance, ι, hι, ⟨?_⟩⟩
  exact (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)

end CFSG.GH74.Generic.S3
