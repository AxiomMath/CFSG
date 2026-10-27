module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveCoGF

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section FieldFour

variable {F : Type} [Field F]

theorem pow_four_eq_self_of_card_four (hF : Nat.card F = 4) (x : F) : x ^ 4 = x := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 4 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have h := FiniteField.pow_card x
  rwa [hq] at h

theorem pow_three_eq_one_of_card_four (hF : Nat.card F = 4) {x : F} (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  have h := pow_four_eq_self_of_card_four hF x
  have h2 : x * (x ^ 3 - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hx
  · linear_combination h3

theorem sq_add_self_add_one_of_card_four (hF : Nat.card F = 4) {x : F} (h0 : x ≠ 0)
    (h1 : x ≠ 1) : x ^ 2 + x + 1 = 0 := by
  have h3 := pow_three_eq_one_of_card_four hF h0
  have h : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h1
  · exact h

theorem eq_or_eq_sq_of_sq_add_self_add_one {x y : F} (hx : x ^ 2 + x + 1 = 0)
    (hy : y ^ 2 + y + 1 = 0) : y = x ∨ y = x ^ 2 := by
  have h : (y - x) * (y - x ^ 2) = 0 := by linear_combination hy - (y + 1 - x) * hx
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (sub_eq_zero.1 h)

theorem ringEquiv_eq_id_or_sq_of_card_four (hF : Nat.card F = 4) (σ : F ≃+* F) :
    (∀ x, σ x = x) ∨ (∀ x, σ x = x ^ 2) := by
  have hpt : ∀ x, σ x = x ∨ σ x = x ^ 2 := by
    intro x
    by_cases h0 : x = 0
    · left
      rw [h0, map_zero]
    by_cases h1 : x = 1
    · left
      rw [h1, map_one]
    have hx := sq_add_self_add_one_of_card_four hF h0 h1
    have hσ : σ x ^ 2 + σ x + 1 = 0 := by
      have h := congrArg σ hx
      rwa [map_add, map_add, map_pow, map_one, map_zero] at h
    exact eq_or_eq_sq_of_sq_add_self_add_one hx hσ
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hcon
  have hσa : σ a = a ^ 2 := (hpt a).resolve_left ha
  have hσb : σ b = b := (hpt b).resolve_right hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha (map_zero σ)
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact ha (map_one σ)
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply hb
    rw [map_zero]
    ring
  have hb1 : b ≠ 1 := by
    rintro rfl
    apply hb
    rw [map_one]
    ring
  rcases eq_or_eq_sq_of_sq_add_self_add_one (sq_add_self_add_one_of_card_four hF ha0 ha1)
      (sq_add_self_add_one_of_card_four hF hb0 hb1) with rfl | rfl
  · exact ha hσb
  · have h1 : σ (a ^ 2) = a := by
      rw [map_pow, hσa]
      calc (a ^ 2) ^ 2 = a ^ 4 := by ring
        _ = a := pow_four_eq_self_of_card_four hF a
    rw [hσb] at h1
    have h2 : a * (a - 1) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact ha0 h
    · exact ha1 (sub_eq_zero.1 h)

end FieldFour

section Scalar

variable {F : Type} [Field F]

theorem mem_range_scalar_of_forall_commute_sl (M : Matrix (Fin 3) (Fin 3) F)
    (h : ∀ g : SpecialLinearGroup (Fin 3) F,
      M * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * M) :
    M ∈ Set.range (Matrix.scalar (Fin 3)) := by
  apply mem_range_scalar_of_commute_single
  intro i j hij
  have h1 := h ⟨transvection i j 1, det_transvection_of_ne i j hij 1⟩
  change M * transvection i j 1 = transvection i j 1 * M at h1
  rw [transvection, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul] at h1
  exact (add_left_cancel h1).symm

end Scalar

section GraphFieldGL

variable (F : Type) [Field F] [CharP F 2]

@[expose] noncomputable def graphFieldGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun M := ⟨(((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).map (frobenius F 2),
    ((M : Matrix (Fin 3) (Fin 3) F)ᵀ).map (frobenius F 2), by
      rw [← Matrix.map_mul, ← transpose_mul, Units.mul_inv, transpose_one]
      exact Matrix.map_one _ (map_zero _) (map_one _), by
      rw [← Matrix.map_mul, ← transpose_mul, Units.inv_mul, transpose_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' M N := by
    apply Units.ext
    simp [_root_.mul_inv_rev, transpose_mul, Matrix.map_mul]

variable {F}

theorem coe_graphFieldGL (M : GL (Fin 3) F) :
    ((graphFieldGL F M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ).map (frobenius F 2) :=
  rfl

theorem coe_graphFieldGL_inv (M : GL (Fin 3) F) :
    (((graphFieldGL F M)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((M : Matrix (Fin 3) (Fin 3) F)ᵀ).map (frobenius F 2) :=
  rfl

theorem toGL_graphFieldSL (g : SpecialLinearGroup (Fin 3) F) :
    SpecialLinearGroup.toGL (graphFieldSL F g) = graphFieldGL F (SpecialLinearGroup.toGL g) := by
  apply Units.ext
  rw [SpecialLinearGroup.coe_GL_coe_matrix, coe_graphFieldGL]
  ext i j
  rw [graphFieldSL_apply, Matrix.map_apply, transpose_apply, frobenius_def, ← map_inv,
    SpecialLinearGroup.coe_GL_coe_matrix]

theorem graphFieldGL_graphFieldGL (hF : ∀ x : F, (x ^ 2) ^ 2 = x) (M : GL (Fin 3) F) :
    graphFieldGL F (graphFieldGL F M) = M := by
  apply Units.ext
  rw [coe_graphFieldGL, coe_graphFieldGL_inv]
  ext i j
  simp only [Matrix.map_apply, transpose_apply, frobenius_def, hF]

theorem det_graphFieldGL (M : GL (Fin 3) F) :
    ((graphFieldGL F M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det =
      (((M⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ 2 := by
  rw [coe_graphFieldGL, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_transpose,
    frobenius_def]

theorem det_eq_one_of_conj_graphField_sq (hF : Nat.card F = 4) (C S : GL (Fin 3) F)
    (hS : (S : Matrix (Fin 3) (Fin 3) F).det = 1)
    (h : ∀ g : SpecialLinearGroup (Fin 3) F,
      C * graphFieldGL F (C * graphFieldGL F (SpecialLinearGroup.toGL g) * C⁻¹) * C⁻¹ =
        S * SpecialLinearGroup.toGL g * S⁻¹) :
    (C : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have hFF : ∀ x : F, (x ^ 2) ^ 2 = x := fun x => by
    rw [← pow_mul]
    exact pow_four_eq_self_of_card_four hF x
  set D : GL (Fin 3) F := S⁻¹ * (C * graphFieldGL F C) with hD
  have hcomm : ∀ g : SpecialLinearGroup (Fin 3) F,
      (D : Matrix (Fin 3) (Fin 3) F) * (g : Matrix (Fin 3) (Fin 3) F) =
        (g : Matrix (Fin 3) (Fin 3) F) * D := by
    intro g
    have h2 : D * SpecialLinearGroup.toGL g = SpecialLinearGroup.toGL g * D := by
      rw [hD]
      calc S⁻¹ * (C * graphFieldGL F C) * SpecialLinearGroup.toGL g
          = S⁻¹ * (C * graphFieldGL F (C * graphFieldGL F (SpecialLinearGroup.toGL g) * C⁻¹) *
              C⁻¹) * (C * graphFieldGL F C) := by
            rw [map_mul, map_mul, map_inv, graphFieldGL_graphFieldGL hFF]
            group
        _ = S⁻¹ * (S * SpecialLinearGroup.toGL g * S⁻¹) * (C * graphFieldGL F C) := by rw [h g]
        _ = SpecialLinearGroup.toGL g * (S⁻¹ * (C * graphFieldGL F C)) := by group
    have h3 := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h2
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using h3
  obtain ⟨c, hc⟩ := mem_range_scalar_of_forall_commute_sl (D : Matrix (Fin 3) (Fin 3) F) hcomm
  have hdetD : (D : Matrix (Fin 3) (Fin 3) F).det = c ^ 3 := by
    rw [← hc, Matrix.scalar_apply, det_diagonal, Fin.prod_univ_three]
    ring
  have hD0 : (D : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    intro h0
    have h1 := congrArg det (Units.mul_inv D)
    rw [det_mul, h0, zero_mul, det_one] at h1
    exact zero_ne_one h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hD0
    rw [hdetD]
    ring
  have hc3 := pow_three_eq_one_of_card_four hF hc0
  have hSinv : ((S⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    have h1 := congrArg det (Units.mul_inv S)
    rwa [det_mul, det_one, hS, one_mul] at h1
  have hCinv : (C : Matrix (Fin 3) (Fin 3) F).det *
      ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [← det_mul, Units.mul_inv, det_one]
  have hDdet : (D : Matrix (Fin 3) (Fin 3) F).det = (C : Matrix (Fin 3) (Fin 3) F).det *
      ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ^ 2 := by
    rw [hD, Units.val_mul, Units.val_mul, det_mul, det_mul, hSinv, det_graphFieldGL, one_mul]
  set a := (C : Matrix (Fin 3) (Fin 3) F).det
  set b := ((C⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det
  have hab : a * b ^ 2 = 1 := by rw [← hDdet, hdetD, hc3]
  have hb : b = 1 := by
    calc b = (a * b) * b := by rw [hCinv, one_mul]
      _ = a * b ^ 2 := by ring
      _ = 1 := hab
  calc a = a * b := by rw [hb, mul_one]
    _ = 1 := hCinv

end GraphFieldGL

section Transvection

variable {F : Type} [Field F]

theorem transvection_map_ringEquiv (σ : F ≃+* F) (i j : Fin 3) :
    (transvection i j (1 : F)).map σ = transvection i j 1 := by
  ext a b
  simp only [transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply, map_add]
  split_ifs <;> simp

theorem transpose_transvection_mulVec {i : Fin 3} (u : Fin 3 → F) (hu : u 0 = 0) :
    (transvection 0 i (1 : F))ᵀ *ᵥ u = u := by
  ext k
  simp [transvection, transpose_add, transpose_single, add_mulVec, single_mulVec, hu]

theorem eq_zero_of_transvection_mulVec {i : Fin 3} (y : Fin 3 → F)
    (h : transvection 0 i (1 : F) *ᵥ y = y) : y i = 0 := by
  have h0 := congrFun h 0
  simpa [transvection, add_mulVec, single_mulVec] using h0

end Transvection

section Induced

variable {G : Type*} [Group G]

theorem exists_mulAut_of_conj {X : Subgroup G} {H : Type*} [Group H] (φ : X →* H)
    (hφ : Function.Surjective φ) {d : G} (hdX : ∀ x ∈ X, d * x * d⁻¹ ∈ X)
    (hdX' : ∀ x ∈ X, d⁻¹ * x * d ∈ X)
    (hk : ∀ x : X, φ x = 1 → φ ⟨d * x * d⁻¹, hdX x x.2⟩ = 1)
    (hk' : ∀ x : X, φ x = 1 → φ ⟨d⁻¹ * x * d, hdX' x x.2⟩ = 1) :
    ∃ β : MulAut H, ∀ x : X, β (φ x) = φ ⟨d * x * d⁻¹, hdX x x.2⟩ := by
  let c : X →* X :=
    { toFun := fun x => ⟨d * x * d⁻¹, hdX x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let c' : X →* X :=
    { toFun := fun x => ⟨d⁻¹ * x * d, hdX' x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hc : ∀ x, c x = ⟨d * x * d⁻¹, hdX x x.2⟩ := fun _ => rfl
  have hc' : ∀ x, c' x = ⟨d⁻¹ * x * d, hdX' x x.2⟩ := fun _ => rfl
  let f₁ : H →* H := φ.liftOfRightInverse (Function.surjInv hφ)
    (Function.rightInverse_surjInv hφ)
    ⟨φ.comp c, fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact hk x hx⟩
  let f₂ : H →* H := φ.liftOfRightInverse (Function.surjInv hφ)
    (Function.rightInverse_surjInv hφ)
    ⟨φ.comp c', fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      exact hk' x hx⟩
  have h₁ : ∀ x, f₁ (φ x) = φ (c x) := fun x => φ.liftOfRightInverse_comp_apply _ _ _ x
  have h₂ : ∀ x, f₂ (φ x) = φ (c' x) := fun x => φ.liftOfRightInverse_comp_apply _ _ _ x
  have hcc' : ∀ x, c (c' x) = x := fun x => Subtype.ext (by
    rw [hc, hc']
    group)
  have hc'c : ∀ x, c' (c x) = x := fun x => Subtype.ext (by
    rw [hc, hc']
    group)
  have hl : Function.LeftInverse f₂ f₁ := by
    intro h
    obtain ⟨x, rfl⟩ := hφ h
    rw [h₁, h₂, hc'c]
  have hr : Function.RightInverse f₂ f₁ := by
    intro h
    obtain ⟨x, rfl⟩ := hφ h
    rw [h₂, h₁, hcc']
  let β : MulAut H :=
    { toFun := f₁
      invFun := f₂
      left_inv := hl
      right_inv := hr
      map_mul' := f₁.map_mul }
  exact ⟨β, fun x => h₁ x⟩

end Induced

section Swap

variable {G : Type*} [Group G] {F : Type} [Field F]

theorem vec_three_ext {α : Type*} {y z : Fin 3 → α} (h0 : y 0 = z 0) (h1 : y 1 = z 1)
    (h2 : y 2 = z 2) : y = z := by
  funext k
  fin_cases k
  · exact h0
  · exact h1
  · exact h2

theorem false_of_semilinear_of_swap (hF : Nat.card F = 4) {W₁ W₂ X : Subgroup G}
    (φ : X →* SpecialLinearGroup (Fin 3) F) (hφ : Function.Surjective φ)
    (hXW₁ : ∀ x ∈ X, ∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁) (hXW₂ : ∀ x ∈ X, ∀ w ∈ W₂, x * w * x⁻¹ ∈ W₂)
    {μ₁ μ₂ : G → Fin 3 → F}
    (hμ₁add : ∀ w ∈ W₁, ∀ w' ∈ W₁, μ₁ (w * w') = μ₁ w + μ₁ w')
    (hμ₁surj : ∀ v, ∃ w ∈ W₁, μ₁ w = v) (hμ₁ker : ∀ w ∈ W₁, μ₁ w = 0 ↔ w ∈ W₂)
    (hμ₁act : ∀ x : X, ∀ w ∈ W₁, μ₁ ((x : G) * w * (x : G)⁻¹) =
      (((φ x)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ μ₁ w)
    (hμ₂add : ∀ w ∈ W₂, ∀ w' ∈ W₂, μ₂ (w * w') = μ₂ w + μ₂ w')
    (hμ₂ker : ∀ w ∈ W₂, μ₂ w = 0 ↔ w ∈ W₁)
    (hμ₂act : ∀ x : X, ∀ w ∈ W₂, μ₂ ((x : G) * w * (x : G)⁻¹) =
      ((φ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ w)
    {d : G} (hd₁₂ : ∀ w ∈ W₁, d * w * d⁻¹ ∈ W₂) (hd₂₁ : ∀ w ∈ W₂, d * w * d⁻¹ ∈ W₁)
    (hd₁₂' : ∀ w ∈ W₁, d⁻¹ * w * d ∈ W₂) (hdX : ∀ x ∈ X, d * x * d⁻¹ ∈ X)
    (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hβ : ∀ x : X, ((φ ⟨d * x * d⁻¹, hdX x x.2⟩ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) *
        (φ x : Matrix (Fin 3) (Fin 3) F).map σ *
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    False := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hμ₁div : ∀ w ∈ W₁, ∀ w' ∈ W₁, μ₁ (w * w'⁻¹) = μ₁ w - μ₁ w' := by
    intro w hw w' hw'
    have h := hμ₁add (w * w'⁻¹) (mul_mem hw (inv_mem hw')) w' hw'
    rw [inv_mul_cancel_right] at h
    exact eq_sub_of_add_eq h.symm
  have hμ₂div : ∀ w ∈ W₂, ∀ w' ∈ W₂, μ₂ (w * w'⁻¹) = μ₂ w - μ₂ w' := by
    intro w hw w' hw'
    have h := hμ₂add (w * w'⁻¹) (mul_mem hw (inv_mem hw')) w' hw'
    rw [inv_mul_cancel_right] at h
    exact eq_sub_of_add_eq h.symm
  have key : ∀ i : Fin 3, i ≠ 0 → ∀ w ∈ W₁, μ₁ w 0 = 0 →
      (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹)) i = 0 := by
    intro i hi w hw hw0
    let τ : SpecialLinearGroup (Fin 3) F :=
      ⟨transvection 0 i 1, det_transvection_of_ne 0 i (Ne.symm hi) 1⟩
    obtain ⟨x, hx⟩ := hφ τ⁻¹
    have hxw : (x : G) * w * (x : G)⁻¹ ∈ W₁ := hXW₁ x x.2 w hw
    have h1 : μ₁ ((x : G) * w * (x : G)⁻¹) = μ₁ w := by
      rw [hμ₁act x w hw, hx, inv_inv]
      exact transpose_transvection_mulVec _ hw0
    have hz₁ : (x : G) * w * (x : G)⁻¹ * w⁻¹ ∈ W₁ := mul_mem hxw (inv_mem hw)
    have hz₂ : (x : G) * w * (x : G)⁻¹ * w⁻¹ ∈ W₂ :=
      (hμ₁ker _ hz₁).1 (by rw [hμ₁div _ hxw _ hw, h1, sub_self])
    have hμz : μ₂ (d * ((x : G) * w * (x : G)⁻¹ * w⁻¹) * d⁻¹) = 0 :=
      (hμ₂ker _ (hd₁₂ _ hz₁)).2 (hd₂₁ _ hz₂)
    have hw' : d * w * d⁻¹ ∈ W₂ := hd₁₂ w hw
    have ha : (d * x * d⁻¹) * (d * w * d⁻¹) * (d * x * d⁻¹)⁻¹ ∈ W₂ :=
      hXW₂ _ (hdX x x.2) _ hw'
    have hrw : d * ((x : G) * w * (x : G)⁻¹ * w⁻¹) * d⁻¹ =
        ((d * x * d⁻¹) * (d * w * d⁻¹) * (d * x * d⁻¹)⁻¹) * (d * w * d⁻¹)⁻¹ := by group
    rw [hrw, hμ₂div _ ha _ hw', sub_eq_zero] at hμz
    have hact : μ₂ ((d * x * d⁻¹) * (d * w * d⁻¹) * (d * x * d⁻¹)⁻¹) =
        ((φ ⟨d * x * d⁻¹, hdX x x.2⟩ : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹) :=
      hμ₂act ⟨d * x * d⁻¹, hdX x x.2⟩ (d * w * d⁻¹) hw'
    rw [hμz, hβ x, hx] at hact
    have hy : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹) =
        ((τ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ *ᵥ
          (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹)) := by
      conv_lhs => rw [hact]
      rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul,
        Matrix.one_mul]
    have hττ : (τ : Matrix (Fin 3) (Fin 3) F).map σ *
        ((τ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map σ = 1 := by
      rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one]
      exact Matrix.map_one _ (map_zero σ) (map_one σ)
    have h3 : (τ : Matrix (Fin 3) (Fin 3) F).map σ *ᵥ
        (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹)) =
          ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹) := by
      conv_lhs => rw [hy]
      rw [mulVec_mulVec, hττ, one_mulVec]
    have hτ : (τ : Matrix (Fin 3) (Fin 3) F) = transvection 0 i 1 := rfl
    rw [hτ, transvection_map_ringEquiv] at h3
    exact eq_zero_of_transvection_mulVec _ h3
  have hinj : Function.Injective (fun v : Fin 2 → F =>
      (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        μ₂ (d * Classical.choose (hμ₁surj ![0, v 0, v 1]) * d⁻¹)) 0) := by
    intro v v' hvv'
    simp only at hvv'
    obtain ⟨hw, hwv⟩ := Classical.choose_spec (hμ₁surj ![0, v 0, v 1])
    obtain ⟨hw', hwv'⟩ := Classical.choose_spec (hμ₁surj ![0, v' 0, v' 1])
    generalize Classical.choose (hμ₁surj ![0, v 0, v 1]) = w at hw hwv hvv'
    generalize Classical.choose (hμ₁surj ![0, v' 0, v' 1]) = w' at hw' hwv' hvv'
    have hw0 : μ₁ w 0 = 0 := by rw [hwv]; rfl
    have hw0' : μ₁ w' 0 = 0 := by rw [hwv']; rfl
    have hy : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w * d⁻¹) =
        ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ (d * w' * d⁻¹) :=
      vec_three_ext hvv'
        (by rw [key 1 (by decide) w hw hw0, key 1 (by decide) w' hw' hw0'])
        (by rw [key 2 (by decide) w hw hw0, key 2 (by decide) w' hw' hw0'])
    have hμ : μ₂ (d * w * d⁻¹) = μ₂ (d * w' * d⁻¹) := by
      have h := congrArg (fun u => (A : Matrix (Fin 3) (Fin 3) F) *ᵥ u) hy
      simpa only [mulVec_mulVec, Units.mul_inv, one_mulVec] using h
    have h1 : d * (w * w'⁻¹) * d⁻¹ ∈ W₁ := by
      have hm := (hμ₂ker _ (mul_mem (hd₁₂ w hw) (inv_mem (hd₁₂ w' hw')))).1
        (by rw [hμ₂div _ (hd₁₂ w hw) _ (hd₁₂ w' hw'), hμ, sub_self])
      rwa [show d * w * d⁻¹ * (d * w' * d⁻¹)⁻¹ = d * (w * w'⁻¹) * d⁻¹ by group] at hm
    have h2 : w * w'⁻¹ ∈ W₂ := by
      have h := hd₁₂' _ h1
      rwa [show d⁻¹ * (d * (w * w'⁻¹) * d⁻¹) * d = w * w'⁻¹ by group] at h
    have h3 : μ₁ w = μ₁ w' := by
      have h := (hμ₁ker _ (mul_mem hw (inv_mem hw'))).2 h2
      rw [hμ₁div _ hw _ hw'] at h
      exact sub_eq_zero.1 h
    rw [hwv, hwv'] at h3
    funext k
    fin_cases k
    · simpa using congrFun h3 1
    · simpa using congrFun h3 2
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_fun, hF, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  norm_num at hcard

end Swap

section Core

variable {G : Type*} [Group G] {F : Type} [Field F] [CharP F 2]

theorem exists_graphField_conj_of_levi (hF : Nat.card F = 4) {W₁ W₂ X : Subgroup G}
    (φ : X →* SpecialLinearGroup (Fin 3) F) (hφ : Function.Surjective φ)
    (hker : ∀ x : X, φ x = 1 ↔ (x : G) ∈ W₁ ⊔ W₂)
    (hXW₁ : ∀ x ∈ X, ∀ w ∈ W₁, x * w * x⁻¹ ∈ W₁) (hXW₂ : ∀ x ∈ X, ∀ w ∈ W₂, x * w * x⁻¹ ∈ W₂)
    {μ₁ μ₂ : G → Fin 3 → F}
    (hμ₁add : ∀ w ∈ W₁, ∀ w' ∈ W₁, μ₁ (w * w') = μ₁ w + μ₁ w')
    (hμ₁surj : ∀ v, ∃ w ∈ W₁, μ₁ w = v) (hμ₁ker : ∀ w ∈ W₁, μ₁ w = 0 ↔ w ∈ W₂)
    (hμ₁act : ∀ x : X, ∀ w ∈ W₁, μ₁ ((x : G) * w * (x : G)⁻¹) =
      (((φ x)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ *ᵥ μ₁ w)
    (hμ₂add : ∀ w ∈ W₂, ∀ w' ∈ W₂, μ₂ (w * w') = μ₂ w + μ₂ w')
    (hμ₂ker : ∀ w ∈ W₂, μ₂ w = 0 ↔ w ∈ W₁)
    (hμ₂act : ∀ x : X, ∀ w ∈ W₂, μ₂ ((x : G) * w * (x : G)⁻¹) =
      ((φ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ μ₂ w)
    {d t : G} (hdX : ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hdX' : ∀ x ∈ X, d⁻¹ * x * d ∈ X)
    (htX : ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hd₁₂ : ∀ w ∈ W₁, d * w * d⁻¹ ∈ W₂) (hd₂₁ : ∀ w ∈ W₂, d * w * d⁻¹ ∈ W₁)
    (hd₁₂' : ∀ w ∈ W₁, d⁻¹ * w * d ∈ W₂) (hd₂₁' : ∀ w ∈ W₂, d⁻¹ * w * d ∈ W₁)
    (hdt : d * t = t * d) (ht2 : t * t = 1) (hdd : d * d ∈ X) (B : GL (Fin 3) F)
    (hB : ∀ x : X, ((φ ⟨t * x * t⁻¹, htX x x.2⟩ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = (B : Matrix (Fin 3) (Fin 3) F) *
        (φ x : Matrix (Fin 3) (Fin 3) F).map (frobenius F 2) *
          ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧
      ∃ (A : SpecialLinearGroup (Fin 3) F) (hd₁X : ∀ x ∈ X, d₁ * x * d₁⁻¹ ∈ X),
        ∀ x : X, φ ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩ = A * graphFieldSL F (φ x) * A⁻¹ := by
  classical
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have hsup : ∀ y ∈ W₁ ⊔ W₂, d * y * d⁻¹ ∈ W₁ ⊔ W₂ := by
    intro y hy
    have hle : (W₁ ⊔ W₂).map (MulAut.conj d).toMonoidHom ≤ W₁ ⊔ W₂ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact Subgroup.mem_sup_right (hd₁₂ w hw)
      · rintro _ ⟨w, hw, rfl⟩
        exact Subgroup.mem_sup_left (hd₂₁ w hw)
    exact hle ⟨y, hy, rfl⟩
  have hsup' : ∀ y ∈ W₁ ⊔ W₂, d⁻¹ * y * d ∈ W₁ ⊔ W₂ := by
    intro y hy
    have hle : (W₁ ⊔ W₂).map (MulAut.conj d⁻¹).toMonoidHom ≤ W₁ ⊔ W₂ := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        show d⁻¹ * w * d⁻¹⁻¹ ∈ W₁ ⊔ W₂
        rw [inv_inv]
        exact Subgroup.mem_sup_right (hd₁₂' w hw)
      · rintro _ ⟨w, hw, rfl⟩
        show d⁻¹ * w * d⁻¹⁻¹ ∈ W₁ ⊔ W₂
        rw [inv_inv]
        exact Subgroup.mem_sup_left (hd₂₁' w hw)
    have h := hle ⟨y, hy, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
  obtain ⟨β, hβ⟩ := exists_mulAut_of_conj φ hφ hdX hdX'
    (fun x hx => (hker _).2 (hsup _ ((hker x).1 hx)))
    (fun x hx => (hker _).2 (hsup' _ ((hker x).1 hx)))
  obtain ⟨A, σ, hform | hform⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_matrix_form_of_mulAut_sl (le_refl 3) β
  · exact (false_of_semilinear_of_swap hF φ hφ hXW₁ hXW₂ hμ₁add hμ₁surj hμ₁ker hμ₁act hμ₂add
      hμ₂ker hμ₂act hd₁₂ hd₂₁ hd₁₂' hdX A σ (fun x => by rw [← hβ x]; exact hform (φ x))).elim
  obtain ⟨d₁, hd₁, C, hd₁X, hC⟩ : ∃ d₁ : G, (d₁ = d ∨ d₁ = d * t) ∧
      ∃ (C : GL (Fin 3) F) (hd₁X : ∀ x ∈ X, d₁ * x * d₁⁻¹ ∈ X), ∀ x : X,
        Matrix.SpecialLinearGroup.toGL (φ ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩) =
          C * graphFieldGL F (Matrix.SpecialLinearGroup.toGL (φ x)) * C⁻¹ := by
    rcases ringEquiv_eq_id_or_sq_of_card_four hF σ with hσ | hσ
    ·
      have hdtX : ∀ x ∈ X, d * t * x * (d * t)⁻¹ ∈ X := by
        intro x hx
        have h := hdX _ (htX x hx)
        rwa [show d * (t * x * t⁻¹) * d⁻¹ = d * t * x * (d * t)⁻¹ by group] at h
      let Bt : GL (Fin 3) F :=
        ⟨((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)ᵀ, (B : Matrix (Fin 3) (Fin 3) F)ᵀ, by
          rw [← transpose_mul, Units.mul_inv, transpose_one], by
          rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
      refine ⟨d * t, Or.inr rfl, A * Bt, hdtX, fun x => ?_⟩
      have hL : ((φ ⟨d * t * x * (d * t)⁻¹, hdtX x x.2⟩ : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) *
            ((((φ ⟨t * x * t⁻¹, htX x x.2⟩)⁻¹ : SpecialLinearGroup (Fin 3) F) :
              Matrix (Fin 3) (Fin 3) F)ᵀ) * ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        have e1 : (⟨d * t * x * (d * t)⁻¹, hdtX x x.2⟩ : X) =
            ⟨d * ((⟨t * x * t⁻¹, htX x x.2⟩ : X) : G) * d⁻¹, hdX _ (htX x x.2)⟩ :=
          Subtype.ext (by simp only; group)
        rw [e1, ← hβ, hform]
        congr 2
        ext i j
        simp only [Matrix.map_apply, hσ]
      have hinv : (((φ ⟨t * x * t⁻¹, htX x x.2⟩)⁻¹ : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) = (B : Matrix (Fin 3) (Fin 3) F) *
            (((φ x)⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map
              (frobenius F 2) * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
        have e2 : (⟨t * x * t⁻¹, htX x x.2⟩ : X)⁻¹ =
            ⟨t * ((x⁻¹ : X) : G) * t⁻¹, htX _ (x⁻¹).2⟩ :=
          Subtype.ext (by simp only [Subgroup.coe_inv]; group)
        rw [← map_inv φ, e2, hB, map_inv]
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hL, hinv, _root_.mul_inv_rev]
      simp only [Units.val_mul]
      rw [coe_graphFieldGL, transpose_mul, transpose_mul, ← transpose_map]
      simp only [Matrix.mul_assoc]
      rfl
    ·
      refine ⟨d, Or.inl rfl, A, hdX, fun x => ?_⟩
      apply Units.ext
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, ← hβ x, hform, Units.val_mul,
        Units.val_mul, coe_graphFieldGL]
      congr 2
      ext i j
      simp only [Matrix.map_apply, transpose_apply, hσ, frobenius_def]
      rfl
  have hd₁sq : d₁ * d₁ = d * d := by
    rcases hd₁ with rfl | rfl
    · rfl
    · calc d * t * (d * t) = d * (t * d) * t := by group
        _ = d * (d * t) * t := by rw [hdt]
        _ = d * d * (t * t) := by group
        _ = d * d := by rw [ht2, mul_one]
  have hdet : (C : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    refine det_eq_one_of_conj_graphField_sq hF C
      (Matrix.SpecialLinearGroup.toGL (φ ⟨d * d, hdd⟩)) (φ ⟨d * d, hdd⟩).2 ?_
    intro g
    obtain ⟨x, rfl⟩ := hφ g
    rw [← hC x, ← hC ⟨d₁ * x * d₁⁻¹, hd₁X x x.2⟩, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc d₁ * (d₁ * x * d₁⁻¹) * d₁⁻¹ = (d₁ * d₁) * x * (d₁ * d₁)⁻¹ := by group
      _ = d * d * x * (d * d)⁻¹ := by rw [hd₁sq]
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL A₀ = C :=
    ⟨⟨(C : Matrix (Fin 3) (Fin 3) F), hdet⟩, Units.ext rfl⟩
  refine ⟨d₁, hd₁, A₀, hd₁X, fun x => ?_⟩
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [map_mul, map_mul, map_inv, hC x, toGL_graphFieldSL, hA₀]

end Core

end CFSG.SeitzReduction.LinearPilot
