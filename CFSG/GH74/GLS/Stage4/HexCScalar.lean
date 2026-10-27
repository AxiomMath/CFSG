module

public import CFSG.GH74.GLS.Stage4.HexCNat

public noncomputable section

open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

section Diag

variable {F : Type*} [Field F]

theorem sl2D_one : sl2D (1 : Fˣ) = (1 : SL2 F) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2D_mul_sl2U_eq (t : Fˣ) (c : F) :
    sl2D t * sl2U c = sl2U ((t : F) ^ 2 * c) * sl2D t := by
  apply sl2_ext
  have ht : (t : F) ≠ 0 := t.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp

theorem sl2D_mul (t t' : Fˣ) : sl2D (t * t') = (sl2D t * sl2D t' : SL2 F) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

end Diag

theorem ringHom_bijective_of_card_eq {F F' : Type*} [Field F] [Field F'] [Finite F']
    (θ : F →+* F') (h : Nat.card F = Nat.card F') : Function.Bijective θ :=
  (Function.Injective.bijective_of_nat_card_le θ.injective h.ge)

section Scalar

variable {F : Type*} [Field F] {G : Type*} [Group G] {φ : SL2 F →* G} {A B : Subgroup G}
  (h : NatPair φ A B)

include h in
theorem NatPair.comm_inj {F' : Type*} [Field F'] (xB : F' → G)
    (hadd : ∀ y y', xB (y + y') = xB y * xB y') (hinj : Function.Injective xB)
    (hmem : ∀ y, xB y ∈ B) :
    ∀ y₁ y₂, ⁅φ (sl2U 1), xB y₁⁆ = ⁅φ (sl2U 1), xB y₂⁆ → y₁ = y₂ := by
  have hx0 : xB 0 = 1 := by
    have := hadd 0 0
    simpa using this
  have hmulR : ∀ b b', b ∈ B → b' ∈ B →
      ⁅φ (sl2U 1), b * b'⁆ = ⁅φ (sl2U 1), b⁆ * ⁅φ (sl2U 1), b'⁆ := fun b b' hb hb' =>
    h.comm_mul_right 1 hb hb'
  intro y₁ y₂ he
  have hneg : ⁅φ (sl2U 1), xB (-y₂)⁆ = (⁅φ (sl2U 1), xB y₂⁆)⁻¹ := by
    have := hmulR (xB y₂) (xB (-y₂)) (hmem _) (hmem _)
    rw [← hadd, add_neg_cancel, hx0] at this
    simp only [commutatorElement_def, mul_one, inv_one, mul_inv_cancel] at this
    exact eq_inv_of_mul_eq_one_right (by
      simpa [commutatorElement_def] using this.symm)
  have h1 : ⁅φ (sl2U 1), xB (y₁ + -y₂)⁆ = 1 := by
    rw [hadd, hmulR _ _ (hmem _) (hmem _), hneg, he, mul_inv_cancel]
  have h2 : φ (sl2U 1) * xB (y₁ + -y₂) * (φ (sl2U 1))⁻¹ = xB (y₁ + -y₂) := by
    have := h1
    rw [commutatorElement_def, mul_inv_eq_one] at this
    exact this
  have h3 := h.ndU _ (hmem _) h2
  have : y₁ + -y₂ = 0 := hinj (h3.trans hx0.symm)
  exact sub_eq_zero.1 (by simpa [sub_eq_add_neg] using this)

include h in
theorem NatPair.exists_ringHom {F' : Type*} [Field F'] (xB : F' → G)
    (hadd : ∀ y y', xB (y + y') = xB y * xB y') (hinj : Function.Injective xB)
    (hmem : ∀ y, xB y ∈ B) (a : Fˣ → F')
    (ha : ∀ (t : Fˣ) (y : F'), φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB (a t * y)) :
    ∃ θ : F →+* F', (∀ (c : F) (y : F'), ⁅φ (sl2U c), xB y⁆ = ⁅φ (sl2U 1), xB (θ c * y)⁆) ∧
      ∀ (t : Fˣ) (y : F'), φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB ((θ (t : F))⁻¹ * y) := by
  classical
  have hx0 : xB 0 = 1 := by
    have := hadd 0 0
    simpa using this
  have hxneg : ∀ y, xB (-y) = (xB y)⁻¹ := fun y => by
    have := hadd y (-y)
    rw [add_neg_cancel, hx0] at this
    exact (eq_inv_of_mul_eq_one_right this.symm)
  have ha_ne : ∀ t, a t ≠ 0 := by
    intro t hat
    have h1 := ha t 1
    rw [hat, zero_mul, hx0] at h1
    have h2 : xB 1 = 1 := by
      have := congrArg (fun x => (φ (sl2D t))⁻¹ * x * φ (sl2D t)) h1
      simpa [mul_assoc] using this
    exact one_ne_zero (hinj (h2.trans hx0.symm))
  have ha_mul : ∀ t t', a (t * t') = a t * a t' := by
    intro t t'
    apply hinj
    have h1 := ha (t * t') 1
    rw [sl2D_mul, map_mul, mul_one] at h1
    calc xB (a (t * t')) = _ := h1.symm
      _ = φ (sl2D t) * (φ (sl2D t') * xB 1 * (φ (sl2D t'))⁻¹) * (φ (sl2D t))⁻¹ := by group
      _ = φ (sl2D t) * xB (a t' * 1) * (φ (sl2D t))⁻¹ := by rw [ha t' 1]
      _ = xB (a t * (a t' * 1)) := ha t _
      _ = xB (a t * a t') := by rw [mul_one]
  have ha_one : a 1 = 1 := by
    apply hinj
    have h1 := ha 1 1
    rw [sl2D_one, map_one] at h1
    simpa using h1.symm
  have hmulR : ∀ b b', b ∈ B → b' ∈ B →
      ⁅φ (sl2U 1), b * b'⁆ = ⁅φ (sl2U 1), b⁆ * ⁅φ (sl2U 1), b'⁆ := fun b b' hb hb' =>
    h.comm_mul_right 1 hb hb'
  have hinjc := h.comm_inj xB hadd hinj hmem
  let θ : F → F' := fun c => if hc : c = 0 then 0 else (a (Units.mk0 c hc))⁻¹
  have hθ0 : θ 0 = 0 := by simp [θ]
  have hθu : ∀ t : Fˣ, θ (t : F) = (a t)⁻¹ := by
    intro t
    simp [θ, t.ne_zero]
  have hform : ∀ (c : F) (y : F'), ⁅φ (sl2U c), xB y⁆ = ⁅φ (sl2U 1), xB (θ c * y)⁆ := by
    intro c y
    by_cases hc : c = 0
    · subst hc
      simp [hθ0, sl2U_zero, hx0]
    · set t := Units.mk0 c hc with ht
      have h1 := (h.key t (hmem ((a t)⁻¹ * y))).2
      rw [ha t ((a t)⁻¹ * y), mul_inv_cancel_left₀ (ha_ne t)] at h1
      have e : c = (t : F) := rfl
      rw [e, hθu t]
      exact h1
  have hθadd : ∀ c c', θ (c + c') = θ c + θ c' := by
    intro c c'
    apply hinjc
    have e1 := hform (c + c') 1
    have e2 := hform c 1
    have e3 := hform c' 1
    rw [h.comm_mul_left c c' (hmem 1), e2, e3] at e1
    simp only [mul_one] at e1
    rw [hadd, hmulR _ _ (hmem _) (hmem _)]
    exact e1.symm
  have hθmul : ∀ c c', θ (c * c') = θ c * θ c' := by
    intro c c'
    by_cases hc : c = 0
    · simp [hc, hθ0]
    by_cases hc' : c' = 0
    · simp [hc', hθ0]
    obtain ⟨t, rfl⟩ := isUnit_iff_ne_zero.2 hc
    obtain ⟨t', rfl⟩ := isUnit_iff_ne_zero.2 hc'
    rw [← Units.val_mul, hθu, hθu, hθu, ha_mul, mul_inv]
  have hθ1 : θ 1 = 1 := by
    have := hθu 1
    simpa [ha_one] using this
  let θr : F →+* F' :=
    { toFun := θ
      map_one' := hθ1
      map_mul' := hθmul
      map_zero' := hθ0
      map_add' := hθadd }
  refine ⟨θr, hform, fun t y => ?_⟩
  show φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB ((θ (t : F))⁻¹ * y)
  rw [ha t y, hθu, inv_inv]


include h in
theorem NatPair.exists_coords {F' : Type*} [Field F'] [Finite F] (xB : F' → G)
    (hadd : ∀ y y', xB (y + y') = xB y * xB y') (hinj : Function.Injective xB)
    (hmem : ∀ y, xB y ∈ B) (hsurj : ∀ b ∈ B, ∃ y, xB y = b) (a : Fˣ → F')
    (ha : ∀ (t : Fˣ) (y : F'), φ (sl2D t) * xB y * (φ (sl2D t))⁻¹ = xB (a t * y))
    (hcard : Nat.card F = Nat.card F') (hcardA : Nat.card A = Nat.card F) :
    ∃ x₂ x₄ : F → G, (∀ c d, x₂ (c + d) = x₂ c * x₂ d) ∧ Function.Injective x₂ ∧
      (∀ d, x₂ d ∈ B) ∧ (∀ b ∈ B, ∃ d, x₂ d = b) ∧
      (∀ c d, x₄ (c + d) = x₄ c * x₄ d) ∧ Function.Injective x₄ ∧ (∀ d, x₄ d ∈ A) ∧
      (∀ b ∈ A, ∃ d, x₄ d = b) ∧ (∀ c d, ⁅φ (sl2U c), x₂ d⁆ = x₄ (c * d)) ∧
      (∀ (t : Fˣ) d, φ (sl2D t) * x₂ d * (φ (sl2D t))⁻¹ = x₂ ((t : F)⁻¹ * d)) ∧
      (∀ (t : Fˣ) d, φ (sl2D t) * x₄ d * (φ (sl2D t))⁻¹ = x₄ ((t : F) * d)) := by
  classical
  obtain ⟨θ, hform, hwt⟩ := h.exists_ringHom xB hadd hinj hmem a ha
  have hF' : Finite F' := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact Nat.card_pos.ne')
  have hθbij : Function.Bijective θ := ringHom_bijective_of_card_eq θ hcard
  have hinjc := h.comm_inj xB hadd hinj hmem
  have hx4mem : ∀ u : F, ⁅φ (sl2U 1), xB (θ u)⁆ ∈ A := fun u => by
    simpa [commutatorElement_def] using h.uB 1 _ (hmem (θ u))
  have hx4add : ∀ u u' : F, ⁅φ (sl2U 1), xB (θ (u + u'))⁆ =
      ⁅φ (sl2U 1), xB (θ u)⁆ * ⁅φ (sl2U 1), xB (θ u')⁆ := by
    intro u u'
    rw [map_add, hadd]
    exact h.comm_mul_right 1 (hmem _) (hmem _)
  have hx4inj : Function.Injective fun u : F => ⁅φ (sl2U 1), xB (θ u)⁆ := fun u u' hu =>
    θ.injective (hinjc _ _ hu)
  have hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcardA]; exact Nat.card_pos.ne')
  refine ⟨fun d => xB (θ d), fun u => ⁅φ (sl2U 1), xB (θ u)⁆, ?_, ?_, ?_, ?_, hx4add, hx4inj,
    hx4mem, ?_, ?_, ?_, ?_⟩
  · intro c d
    simp only [map_add]
    exact hadd _ _
  · exact hinj.comp θ.injective
  · intro d
    exact hmem _
  · intro b hb
    obtain ⟨y, rfl⟩ := hsurj b hb
    obtain ⟨d, rfl⟩ := hθbij.2 y
    exact ⟨d, rfl⟩
  · intro b hb
    let g : F → A := fun u => ⟨⁅φ (sl2U 1), xB (θ u)⁆, hx4mem u⟩
    have hg : Function.Injective g := fun u u' hu => hx4inj (congrArg Subtype.val hu)
    have hgb : Function.Bijective g := hg.bijective_of_nat_card_le hcardA.le
    obtain ⟨u, hu⟩ := hgb.2 ⟨b, hb⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · intro c d
    rw [hform c (θ d), ← map_mul]
  · intro t d
    rw [hwt t (θ d), ← map_inv₀, ← map_mul]
  · intro t d
    have e1 : φ (sl2D t) * φ (sl2U 1) * (φ (sl2D t))⁻¹ = φ (sl2U ((t : F) ^ 2 * 1)) := by
      rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, sl2D_mul_sl2U_eq]
    have e2 := hwt t (θ d)
    have e3 : ⁅φ (sl2U ((t : F) ^ 2)), xB (θ ((t : F)⁻¹ * d))⁆ =
        ⁅φ (sl2U 1), xB (θ (t * d))⁆ := by
      have e4 : (t : F) ^ 2 * ((t : F)⁻¹ * d) = (t : F) * d := by
        have ht : (t : F) ≠ 0 := t.ne_zero
        field_simp
      rw [hform, ← map_mul, e4]
    calc φ (sl2D t) * ⁅φ (sl2U 1), xB (θ d)⁆ * (φ (sl2D t))⁻¹
        = ⁅φ (sl2D t) * φ (sl2U 1) * (φ (sl2D t))⁻¹,
            φ (sl2D t) * xB (θ d) * (φ (sl2D t))⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅φ (sl2U ((t : F) ^ 2)), xB (θ ((t : F)⁻¹ * d))⁆ := by
          rw [e1, e2, mul_one, map_mul, map_inv₀]
      _ = _ := e3

end Scalar

end CFSG.GH74.GLS.Stage4.Hex
