module

public import CFSG.ClassicalInvolution.Asc77.AscC25X9
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  QuadraticMap CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups commutatorElement

namespace C25X

section Six

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {p : Fin 6 → V}

structure Ortho6 (Q : QuadraticForm F V) (p : Fin 6 → V) : Prop where
  q : ∀ i, Q (p i) = 1
  orth : ∀ i j, i ≠ j → polar Q (p i) (p j) = 0

theorem Ortho6.polar_eq (h : Ortho6 Q p) (i j : Fin 6) :
    polar Q (p i) (p j) = if i = j then 2 else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [ite_true, polar_self_eq_two_mul, h.q]
    ring
  · simp only [hij, ite_false]
    exact h.orth i j hij

theorem Ortho6.quad1 (h : Ortho6 Q p) : Ortho4 Q (p 0) (p 1) (p 2) (p 3) :=
  ⟨h.q 0, h.q 1, h.q 2, h.q 3, h.orth 0 1 (by decide), h.orth 0 2 (by decide),
    h.orth 0 3 (by decide), h.orth 1 2 (by decide), h.orth 1 3 (by decide),
    h.orth 2 3 (by decide)⟩

theorem Ortho6.quad2 (h : Ortho6 Q p) : Ortho4 Q (p 0) (p 1) (p 4) (p 5) :=
  ⟨h.q 0, h.q 1, h.q 4, h.q 5, h.orth 0 1 (by decide), h.orth 0 4 (by decide),
    h.orth 0 5 (by decide), h.orth 1 4 (by decide), h.orth 1 5 (by decide),
    h.orth 4 5 (by decide)⟩


variable {x y : F} {h2 : (2 : F) ≠ 0} {hxy : x * x + y * y = -1}

theorem Ortho6.decomp (h : Ortho6 Q p) (h2 : (2 : F) ≠ 0) (u : V) (j : Fin 6) :
    polar Q (u - ((polar Q u (p 0) / 2) • p 0 + (polar Q u (p 1) / 2) • p 1 +
      (polar Q u (p 2) / 2) • p 2 + (polar Q u (p 3) / 2) • p 3 + (polar Q u (p 4) / 2) • p 4 +
      (polar Q u (p 5) / 2) • p 5)) (p j) = 0 := by
  have e := h.polar_eq
  fin_cases j <;>
    simp [polar_sub_left, polar_add_left, e] <;> field_simp <;> ring

theorem Ortho6.La_comm (h : Ortho6 Q p) (h2 : (2 : F) ≠ 0) (hxy : x * x + y * y = -1) :
    (orthoFrame x y h2 hxy h.quad1).La r0 * (orthoFrame x y h2 hxy h.quad2).La r0 =
      (orthoFrame x y h2 hxy h.quad2).La r0 * (orthoFrame x y h2 hxy h.quad1).La r0 := by
  set F₁ := orthoFrame x y h2 hxy h.quad1 with hF₁
  set F₂ := orthoFrame x y h2 hxy h.quad2 with hF₂
  have P := h.orth
  have p1_0 : F₁.La r0 (p 0) = p 1 := orthoFrame_La_a
  have p1_1 : F₁.La r0 (p 1) = -p 0 := orthoFrame_La_b
  have p1_2 : F₁.La r0 (p 2) = p 3 := orthoFrame_La_c
  have p1_3 : F₁.La r0 (p 3) = -p 2 := orthoFrame_La_d
  have p1_p : ∀ v : V, polar Q v (p 0) = 0 → polar Q v (p 1) = 0 → polar Q v (p 2) = 0 →
      polar Q v (p 3) = 0 → F₁.La r0 v = v :=
    fun v h0 h1 h2' h3 => orthoFrame_La_perp h0 h1 h2' h3 r0
  have p2_0 : F₂.La r0 (p 0) = p 1 := orthoFrame_La_a
  have p2_1 : F₂.La r0 (p 1) = -p 0 := orthoFrame_La_b
  have p2_4 : F₂.La r0 (p 4) = p 5 := orthoFrame_La_c
  have p2_5 : F₂.La r0 (p 5) = -p 4 := orthoFrame_La_d
  have p2_p : ∀ v : V, polar Q v (p 0) = 0 → polar Q v (p 1) = 0 → polar Q v (p 4) = 0 →
      polar Q v (p 5) = 0 → F₂.La r0 v = v :=
    fun v h0 h1 h2' h3 => orthoFrame_La_perp h0 h1 h2' h3 r0
  have e := h.polar_eq
  have p1_4 : F₁.La r0 (p 4) = p 4 := p1_p _ (by simp [e]) (by simp [e]) (by simp [e]) (by simp [e])
  have p1_5 : F₁.La r0 (p 5) = p 5 := p1_p _ (by simp [e]) (by simp [e]) (by simp [e]) (by simp [e])
  have p2_2 : F₂.La r0 (p 2) = p 2 := p2_p _ (by simp [e]) (by simp [e]) (by simp [e]) (by simp [e])
  have p2_3 : F₂.La r0 (p 3) = p 3 := p2_p _ (by simp [e]) (by simp [e]) (by simp [e]) (by simp [e])
  have key : ∀ (c0 c1 c2 c3 c4 c5 : F) (w : V), (∀ j, polar Q w (p j) = 0) →
      F₁.La r0 (F₂.La r0
        (c0 • p 0 + c1 • p 1 + c2 • p 2 + c3 • p 3 + c4 • p 4 + c5 • p 5 + w)) =
      F₂.La r0 (F₁.La r0
        (c0 • p 0 + c1 • p 1 + c2 • p 2 + c3 • p 3 + c4 • p 4 + c5 • p 5 + w)) := by
    intro c0 c1 c2 c3 c4 c5 w hw
    have hw1 : F₁.La r0 w = w := p1_p w (hw 0) (hw 1) (hw 2) (hw 3)
    have hw2 : F₂.La r0 w = w := p2_p w (hw 0) (hw 1) (hw 4) (hw 5)
    simp only [map_add, map_smul, map_neg, p1_0, p1_1, p1_2, p1_3, p1_4, p1_5, p2_0, p2_1, p2_2,
      p2_3, p2_4, p2_5, hw1, hw2]
  refine LinearEquiv.ext fun u => ?_
  simp only [LinearEquiv.mul_apply]
  have := key (polar Q u (p 0) / 2) (polar Q u (p 1) / 2) (polar Q u (p 2) / 2)
    (polar Q u (p 3) / 2) (polar Q u (p 4) / 2) (polar Q u (p 5) / 2) _ (h.decomp h2 u)
  rwa [add_sub_cancel] at this

theorem Ortho6.not_scalar (h : Ortho6 Q p) (h2 : (2 : F) ≠ 0) (hxy : x * x + y * y = -1) (μ : F)
    (hμ : ∀ v, ((orthoFrame x y h2 hxy h.quad1).La r0 * (orthoFrame x y h2 hxy h.quad1).La r0 *
      ((orthoFrame x y h2 hxy h.quad2).La r0 * (orthoFrame x y h2 hxy h.quad2).La r0)) v =
        μ • v) : False := by
  set F₁ := orthoFrame x y h2 hxy h.quad1 with hF₁
  set F₂ := orthoFrame x y h2 hxy h.quad2 with hF₂
  have e := h.polar_eq
  have p1_0 : F₁.La r0 (p 0) = p 1 := orthoFrame_La_a
  have p1_1 : F₁.La r0 (p 1) = -p 0 := orthoFrame_La_b
  have p1_2 : F₁.La r0 (p 2) = p 3 := orthoFrame_La_c
  have p1_3 : F₁.La r0 (p 3) = -p 2 := orthoFrame_La_d
  have p2_0 : F₂.La r0 (p 0) = p 1 := orthoFrame_La_a
  have p2_1 : F₂.La r0 (p 1) = -p 0 := orthoFrame_La_b
  have p2_p : ∀ v : V, polar Q v (p 0) = 0 → polar Q v (p 1) = 0 → polar Q v (p 4) = 0 →
      polar Q v (p 5) = 0 → F₂.La r0 v = v :=
    fun v h0 h1 h2' h3 => orthoFrame_La_perp h0 h1 h2' h3 r0
  have p2_2 : F₂.La r0 (p 2) = p 2 := p2_p _ (by simp [e]) (by simp [e]) (by simp [e]) (by simp [e])
  have h0 := hμ (p 0)
  have h2' := hμ (p 2)
  simp only [LinearEquiv.mul_apply, p1_0, p1_1, p1_2, p1_3, p2_0, p2_1, p2_2, map_neg, neg_neg]
    at h0 h2'
  have hp0 : p 0 ≠ 0 := by
    intro hz
    have := h.q 0
    rw [hz] at this
    simp at this
  have hp2 : p 2 ≠ 0 := by
    intro hz
    have := h.q 2
    rw [hz] at this
    simp at this
  have e0 : (μ - 1) • p 0 = 0 := by rw [sub_smul, ← h0]; simp
  have e2 : (μ + 1) • p 2 = 0 := by rw [add_smul, ← h2']; simp
  have m0 : μ - 1 = 0 := (smul_eq_zero.mp e0).resolve_right hp0
  have m2 : μ + 1 = 0 := (smul_eq_zero.mp e2).resolve_right hp2
  apply h2
  linear_combination m2 - m0

end Six

section Spin

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

@[expose] def NC4On (t : StatedLieTag) (M : LieUniversal) : Prop :=
  ∃ R₁ ∈ fundamentalSubgroups t M.D, ∃ R₂ ∈ fundamentalSubgroups t M.D, ∃ y ∈ R₁, ∃ x₂ ∈ R₂,
    y * y * y * y = 1 ∧ y * y ≠ 1 ∧ x₂ * x₂ = 1 ∧ x₂ ≠ 1 ∧ x₂ * y = y * x₂ ∧
      (y * y) * x₂ ∉ Subgroup.center M.K

omit [DecidableEq ι] in
theorem nc4_of_spin (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q)
    (hV : 7 ≤ Module.finrank F (ι → F)) {t : StatedLieTag}
    (D : UniversalRootDatum (spinGroup Q))
    (hsurj : ∀ L ∈ fundSet Q, ∃ R ∈ fundamentalSubgroups t D, R.map (spinAction Q) = L)
    (hnc : ∀ R ∈ fundamentalSubgroups t D, ∀ r ∈ R, r ∈ Subgroup.center (spinGroup Q) → r = 1)
    (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1) :
    NC4On t ⟨spinGroup Q, D⟩ := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, -, hpQ, hpP⟩ := exists_orthonormal_fin hodd 6 ⊤ (polarNondegOn_top hQ)
    (by rw [finrank_top]; omega)
  have hO : Ortho6 Q p := ⟨hpQ, hpP⟩
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq h2 (-1 : F)
  set F₁ := orthoFrame x y h2 hxy hO.quad1 with hF₁
  set F₂ := orthoFrame x y h2 hxy hO.quad2 with hF₂
  set θ := spinAction Q with hθ
  obtain ⟨R₁, hR₁, hR₁L⟩ := hsurj F₁.La.range ⟨_, IsFundamental.of_frame F₁⟩
  obtain ⟨R₂, hR₂, hR₂L⟩ := hsurj F₂.La.range ⟨_, IsFundamental.of_frame F₂⟩
  obtain ⟨y₁, hy₁R, hy₁⟩ : ∃ y₁ ∈ R₁, θ y₁ = F₁.La r0 := by
    have : F₁.La r0 ∈ R₁.map θ := by rw [hR₁L]; exact ⟨r0, rfl⟩
    exact Subgroup.mem_map.mp this
  obtain ⟨y₂, hy₂R, hy₂⟩ : ∃ y₂ ∈ R₂, θ y₂ = F₂.La r0 := by
    have : F₂.La r0 ∈ R₂.map θ := by rw [hR₂L]; exact ⟨r0, rfl⟩
    exact Subgroup.mem_map.mp this
  have hker : ∀ r, θ r = 1 → r ∈ Subgroup.center (spinGroup Q) := fun r hr =>
    ker_spinAction_le_center Q hr
  have hinj₁ : ∀ r ∈ R₁, θ r = 1 → r = 1 := fun r hr h => hnc R₁ hR₁ r hr (hker r h)
  have hinj₂ : ∀ r ∈ R₂, θ r = 1 → r = 1 := fun r hr h => hnc R₂ hR₂ r hr (hker r h)
  have hr0 : (r0 : SL(2, F)) * r0 = -1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_r0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hm1 : (-1 : SL(2, F)) * -1 = 1 := by simp
  have hne1 : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have := congrArg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp at this
    exact h2 (by linear_combination -this)
  have hr04 : r0 * r0 * r0 * r0 = (1 : SL(2, F)) := by
    calc r0 * r0 * r0 * r0 = (r0 * r0) * (r0 * r0) := by simp only [mul_assoc]
      _ = 1 := by rw [hr0, hm1]
  have hsq₁ : θ (y₁ * y₁) = F₁.La (-1) := by rw [map_mul, hy₁, ← map_mul, hr0]
  have hsq₂ : θ (y₂ * y₂) = F₂.La (-1) := by rw [map_mul, hy₂, ← map_mul, hr0]
  have hfour₁ : y₁ * y₁ * y₁ * y₁ = 1 := by
    apply hinj₁ _ (R₁.mul_mem (R₁.mul_mem (R₁.mul_mem hy₁R hy₁R) hy₁R) hy₁R)
    rw [map_mul, map_mul, map_mul, hy₁, ← map_mul, ← map_mul, ← map_mul, hr04, map_one]
  have hfour₂ : y₂ * y₂ * y₂ * y₂ = 1 := by
    apply hinj₂ _ (R₂.mul_mem (R₂.mul_mem (R₂.mul_mem hy₂R hy₂R) hy₂R) hy₂R)
    rw [map_mul, map_mul, map_mul, hy₂, ← map_mul, ← map_mul, ← map_mul, hr04, map_one]
  have hsq₁ne : y₁ * y₁ ≠ 1 := by
    intro h
    rw [h, map_one] at hsq₁
    exact hne1 (F₁.La_injective (by rw [← hsq₁, map_one]))
  have hsq₂ne : y₂ * y₂ ≠ 1 := by
    intro h
    rw [h, map_one] at hsq₂
    exact hne1 (F₂.La_injective (by rw [← hsq₂, map_one]))
  have hcomm₀ : F₁.La r0 * F₂.La r0 = F₂.La r0 * F₁.La r0 := hO.La_comm h2 hxy
  set c := y₂ * y₁ * (y₁ * y₂)⁻¹ with hc
  have hθc : θ c = 1 := by
    rw [hc, map_mul, map_mul, map_inv, map_mul, hy₁, hy₂, ← hcomm₀]
    exact mul_inv_cancel _
  have hcc : c ∈ Subgroup.center (spinGroup Q) := hker c hθc
  have hc2 : c * c = 1 := hker2 c hθc
  have hcz : ∀ g, g * c = c * g := Subgroup.mem_center_iff.mp hcc
  have e1 : y₂ * y₁ = c * (y₁ * y₂) := by rw [hc]; group
  have hcomm : y₂ * y₂ * y₁ = y₁ * (y₂ * y₂) := by
    calc y₂ * y₂ * y₁ = y₂ * (y₂ * y₁) := by simp only [mul_assoc]
      _ = y₂ * (c * (y₁ * y₂)) := by rw [e1]
      _ = (y₂ * c) * (y₁ * y₂) := by simp only [mul_assoc]
      _ = (c * y₂) * (y₁ * y₂) := by rw [hcz y₂]
      _ = c * ((y₂ * y₁) * y₂) := by simp only [mul_assoc]
      _ = c * ((c * (y₁ * y₂)) * y₂) := by rw [e1]
      _ = (c * c) * (y₁ * y₂ * y₂) := by simp only [mul_assoc]
      _ = y₁ * (y₂ * y₂) := by rw [hc2, one_mul]; simp only [mul_assoc]
  have hx₂sq : (y₂ * y₂) * (y₂ * y₂) = 1 := by
    calc (y₂ * y₂) * (y₂ * y₂) = y₂ * y₂ * y₂ * y₂ := by simp only [mul_assoc]
      _ = 1 := hfour₂
  refine ⟨R₁, hR₁, R₂, hR₂, y₁, hy₁R, y₂ * y₂, R₂.mul_mem hy₂R hy₂R, hfour₁, hsq₁ne, hx₂sq,
    hsq₂ne, hcomm, ?_⟩
  intro hmem
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hmem
  refine hO.not_scalar h2 hxy μ (fun v => ?_)
  have := hμ v
  rwa [map_mul, map_mul, map_mul, hy₁, hy₂] at this

end Spin
end C25X

end CFSG.ClassicalInvolution.Asc77
