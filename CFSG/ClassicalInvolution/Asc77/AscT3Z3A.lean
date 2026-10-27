module

public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open scoped MatrixGroups

section Pure

variable {F : Type*} [Field F]

theorem z3_comm_of_comm_nonscalar {W X Y : Matrix (Fin 2) (Fin 2) F}
    (hW : ∀ r : F, W ≠ Matrix.scalar (Fin 2) r) (hX : X * W = W * X) (hY : Y * W = W * Y) :
    X * Y = Y * X := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d, W = !![a, b; c, d] :=
    ⟨W 0 0, W 0 1, W 1 0, W 1 1, Matrix.eta_fin_two W⟩
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s, X = !![p, q; r, s] :=
    ⟨X 0 0, X 0 1, X 1 0, X 1 1, Matrix.eta_fin_two X⟩
  obtain ⟨p', q', r', s', rfl⟩ : ∃ p q r s, Y = !![p, q; r, s] :=
    ⟨Y 0 0, Y 0 1, Y 1 0, Y 1 1, Matrix.eta_fin_two Y⟩
  have hX00 := congrFun (congrFun hX 0) 0
  have hX01 := congrFun (congrFun hX 0) 1
  have hX10 := congrFun (congrFun hX 1) 0
  have hY00 := congrFun (congrFun hY 0) 0
  have hY01 := congrFun (congrFun hY 0) 1
  have hY10 := congrFun (congrFun hY 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at hX00 hX01 hX10 hY00 hY01 hY10
  have key : q * r' = q' * r ∧ q' * (p - s) = q * (p' - s') ∧
      r * (p' - s') = r' * (p - s) := by
    by_cases hb : b = 0
    · by_cases hc : c = 0
      · have had : a ≠ d := by
          intro h
          refine hW a ?_
          rw [hb, hc, ← h]
          ext i j
          fin_cases i <;> fin_cases j <;> simp
        have hne : a - d ≠ 0 := sub_ne_zero.mpr had
        have hq : q = 0 := by
          have : q * (a - d) = 0 := by rw [hb] at hX01; linear_combination -hX01
          exact (mul_eq_zero.mp this).resolve_right hne
        have hq' : q' = 0 := by
          have : q' * (a - d) = 0 := by rw [hb] at hY01; linear_combination -hY01
          exact (mul_eq_zero.mp this).resolve_right hne
        have hr : r = 0 := by
          have : r * (a - d) = 0 := by rw [hc] at hX10; linear_combination hX10
          exact (mul_eq_zero.mp this).resolve_right hne
        have hr' : r' = 0 := by
          have : r' * (a - d) = 0 := by rw [hc] at hY10; linear_combination hY10
          exact (mul_eq_zero.mp this).resolve_right hne
        subst hq hq' hr hr'
        simp
      · have hq : q = 0 := by
          have : q * c = 0 := by rw [hb] at hX00; linear_combination hX00
          exact (mul_eq_zero.mp this).resolve_right hc
        have hq' : q' = 0 := by
          have : q' * c = 0 := by rw [hb] at hY00; linear_combination hY00
          exact (mul_eq_zero.mp this).resolve_right hc
        subst hq hq'
        refine ⟨by ring, by ring, ?_⟩
        have e1 : c * (p - s) = r * (a - d) := by linear_combination -hX10
        have e2 : c * (p' - s') = r' * (a - d) := by linear_combination -hY10
        apply mul_left_cancel₀ hc
        linear_combination r * e2 - r' * e1
    · have hr : r = q * c / b := by field_simp; linear_combination -hX00
      have hr' : r' = q' * c / b := by field_simp; linear_combination -hY00
      have hps : p - s = q * (a - d) / b := by field_simp; linear_combination hX01
      have hps' : p' - s' = q' * (a - d) / b := by field_simp; linear_combination hY01
      refine ⟨?_, ?_, ?_⟩
      · rw [hr, hr']; field_simp
      · rw [hps, hps']; field_simp
      · rw [hr, hr', hps, hps']; field_simp
  obtain ⟨k1, k2, k3⟩ := key
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination k1
  · linear_combination k2
  · linear_combination k3
  · linear_combination -k1

theorem z3_commute_of_commute_noncentral {w x y : SL(2, F)}
    (hw : w ∉ Subgroup.center SL(2, F)) (hx : x * w = w * x) (hy : y * w = w * y) :
    x * y = y * x := by
  have hW : ∀ r : F, (w : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) r := by
    intro r hr
    apply hw
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨r, ?_, hr.symm⟩
    have h1 : Matrix.det (w : Matrix (Fin 2) (Fin 2) F) = 1 := Matrix.SpecialLinearGroup.det_coe w
    rw [hr] at h1
    simpa [Matrix.det_fin_two, Matrix.scalar_apply, pow_two] using h1
  have := z3_comm_of_comm_nonscalar hW (X := (x : Matrix (Fin 2) (Fin 2) F))
    (Y := (y : Matrix (Fin 2) (Fin 2) F))
    (by exact_mod_cast congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hx)
    (by exact_mod_cast congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F)) hy)
  exact Subtype.ext (by simpa using this)

theorem z3_center_trivial_of_perfect_inner {P : Type*} [Group P] (hP : Group.IsPerfect P)
    (φ : P →* MulAut SL(2, F)) (hin : ∀ g : P, ∃ x : SL(2, F), φ g = MulAut.conj x) {c : P}
    (hc : c ∈ Subgroup.center P) : φ c = 1 := by
  obtain ⟨w, hw⟩ := hin c
  by_cases hwc : w ∈ Subgroup.center SL(2, F)
  · rw [hw]
    refine MulEquiv.ext fun y => ?_
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [(Subgroup.mem_center_iff.mp hwc y).symm]
    group
  have hfix : ∀ (g : P) (x : SL(2, F)), x ∈ Subgroup.center SL(2, F) → φ g x = x := by
    intro g x hx
    rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff x).mp hx with rfl | rfl
    · exact map_one _
    · have hc1 : φ g (-1) ∈ Subgroup.center SL(2, F) := by
        rw [Subgroup.mem_center_iff]
        intro y
        obtain ⟨y', rfl⟩ := (φ g).surjective y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y']
      rcases (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp hc1 with h | h
      · have h1 : (-1 : SL(2, F)) = 1 := (φ g).injective (h.trans (map_one _).symm)
        exact h.trans h1.symm
      · exact h
  have hcent : ∀ g : P, w⁻¹ * φ g w ∈ Subgroup.center SL(2, F) := by
    intro g
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 : φ g * φ c = φ c * φ g := by
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc g]
    have h2 : ∀ y' : SL(2, F), φ g w * y' * (φ g w)⁻¹ = w * y' * w⁻¹ := by
      intro y'
      have h3 := congrArg (fun α : MulAut SL(2, F) => α ((φ g)⁻¹ y')) h1
      simp only [MulAut.mul_apply, hw, MulAut.conj_apply, map_mul, map_inv] at h3
      have h4 : (φ g) ((φ g)⁻¹ y') = y' := (φ g).apply_symm_apply y'
      rw [h4] at h3
      exact h3
    have h5 := h2 y
    calc y * (w⁻¹ * φ g w) = w⁻¹ * (w * y * w⁻¹ * φ g w) := by group
      _ = w⁻¹ * (φ g w * y * (φ g w)⁻¹ * φ g w) := by rw [h5]
      _ = (w⁻¹ * φ g w) * y := by group
  let θ : P →* Subgroup.center SL(2, F) :=
    { toFun := fun g => ⟨w⁻¹ * φ g w, hcent g⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun g h => by
        apply Subtype.ext
        have e1 : φ g (φ h w) = φ g w * (w⁻¹ * φ h w) := by
          have : φ h w = w * (w⁻¹ * φ h w) := by group
          rw [this, map_mul, hfix g _ (hcent h)]
          simp
        simp only [map_mul, MulAut.mul_apply, Subgroup.coe_mul]
        rw [e1]
        group }
  have hθ : ∀ g : P, w⁻¹ * φ g w = 1 := by
    intro g
    have h1 := Abelianization.commutator_subset_ker θ
    rw [hP.commutator_eq_top] at h1
    have h2 : θ g = 1 := h1 (Subgroup.mem_top g)
    exact congrArg Subtype.val h2
  have hφw : ∀ g : P, φ g w = w := fun g => by
    have := hθ g
    rwa [inv_mul_eq_one, eq_comm] at this
  choose x hx using hin
  have hxw : ∀ g : P, x g * w = w * x g := fun g => by
    have h1 := hφw g
    rw [hx g, MulAut.conj_apply] at h1
    calc x g * w = x g * w * (x g)⁻¹ * x g := by group
      _ = w * x g := by rw [h1]
  have hcomm : ∀ g h : P, φ g * φ h = φ h * φ g := fun g h => by
    rw [hx g, hx h, ← map_mul, ← map_mul,
      z3_commute_of_commute_noncentral hwc (hxw g) (hxw h)]
  have hker : commutator P ≤ (φ).ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm g h)
  rw [hP.commutator_eq_top] at hker
  exact hker (Subgroup.mem_top c)

end Pure

end CFSG.ClassicalInvolution.Asc77.T3CII
