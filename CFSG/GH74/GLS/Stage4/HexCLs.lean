module

public import CFSG.GH74.GLS.Stage4.HexCNcalc
public import CFSG.GH74.GLS.Stage4.HexCComm

public section

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage4.Hex

variable {G : Type} [Group G] {H : Subgroup G} {r₁ r₂ : G} {U : Subgroup G}
  {root : ℤ → Subgroup G} {F : Type} [Field F]

section Ls

variable (R : RGD2 6 H r₁ r₂ U root) (hC : Hex6Comm root) (D : HexData root F)

include R in
theorem Nel_inj {e e' f f' : F} {u u' : G} (hu : u ∈ root 3) (hu' : u' ∈ root 3)
    (h : Nel D e u f = Nel D e' u' f') : e = e' ∧ u = u' ∧ f = f' := by
  obtain ⟨h1, h2, h3⟩ := rgd2_unique_234 R (D.p2_mem e) (D.p2_mem e') hu hu' (D.p4_mem f)
    (D.p4_mem f') h
  exact ⟨D.p2_inj h1, h2, D.p4_inj h3⟩

theorem conj_T_Nel (t : Fˣ) {e f : F} {u : G} (hu : u ∈ root 3) :
    D.T t * Nel D e u f * (D.T t)⁻¹ = Nel D ((t : F)⁻¹ * e) u ((t : F) * f) := by
  have hTu : D.T t * u * (D.T t)⁻¹ = u := by
    rw [mul_inv_eq_iff_eq_mul, D.T_eq]; exact D.cent3 _ u hu
  unfold Nel
  calc D.T t * (D.p2 e * u * D.p4 f) * (D.T t)⁻¹
      = (D.T t * D.p2 e * (D.T t)⁻¹) * (D.T t * u * (D.T t)⁻¹) * (D.T t * D.p4 f * (D.T t)⁻¹) := by
        group
    _ = _ := by rw [D.w2, hTu, D.w4]

variable {μ : G → F} (hμ : MuData D μ) {a2 a4 : F → F → F} {L : F → F → G}
  (hcd : CommData D a2 a4 L)

include R hC hμ hcd in
theorem comm15_add_s (s s' t : F) :
    a2 (s + s') t = a2 s' t + s * μ (L s' t) + a2 s t ∧ L (s + s') t = L s' t * L s t ∧
      a4 (s + s') t = a4 s' t + a4 s t := by
  have eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have h1 : ⁅D.p1 (s + s'), D.p5 t⁆ =
      D.p1 s * ⁅D.p1 s', D.p5 t⁆ * (D.p1 s)⁻¹ * ⁅D.p1 s, D.p5 t⁆ := by
    rw [D.p1_add]; simp only [commutatorElement_def]; group
  rw [eq (s + s') t, eq s' t, eq s t] at h1
  have h1' : D.p1 s * Nel D (a2 s' t) (L s' t) (a4 s' t) * (D.p1 s)⁻¹ *
      Nel D (a2 s t) (L s t) (a4 s t) =
      Nel D (a2 s' t + s * μ (L s' t) + a2 s t) (L s' t * L s t) (a4 s' t + a4 s t) := by
    rw [conj_p1_Nel hC D hμ s _ _ (hcd.L_mem s' t), Nel_mul hC D (hcd.L_mem s' t) (hcd.L_mem s t)]
  rw [h1'] at h1
  have := Nel_inj R D (hcd.L_mem _ _) ((root 3).mul_mem (hcd.L_mem _ _) (hcd.L_mem _ _)) h1
  exact ⟨this.1, this.2.1, this.2.2⟩

include R hC hμ hcd in
theorem comm15_add_t (s t t' : F) :
    a2 s (t + t') = a2 s t + a2 s t' ∧ L s (t + t') = L s t * L s t' ∧
      a4 s (t + t') = a4 s t + (a4 s t' + t * μ (L s t')) := by
  have eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have h1 : ⁅D.p1 s, D.p5 (t + t')⁆ =
      ⁅D.p1 s, D.p5 t⁆ * (D.p5 t * ⁅D.p1 s, D.p5 t'⁆ * (D.p5 t)⁻¹) := by
    rw [D.p5_add]; simp only [commutatorElement_def]; group
  rw [eq s (t + t'), eq s t, eq s t'] at h1
  have h1' : Nel D (a2 s t) (L s t) (a4 s t) *
      (D.p5 t * Nel D (a2 s t') (L s t') (a4 s t') * (D.p5 t)⁻¹) =
      Nel D (a2 s t + a2 s t') (L s t * L s t') (a4 s t + (a4 s t' + t * μ (L s t'))) := by
    rw [conj_p5_Nel hC D hμ t _ _ (hcd.L_mem s t'), Nel_mul hC D (hcd.L_mem s t) (hcd.L_mem s t')]
  rw [h1'] at h1
  have := Nel_inj R D (hcd.L_mem _ _) ((root 3).mul_mem (hcd.L_mem _ _) (hcd.L_mem _ _)) h1
  exact ⟨this.1, this.2.1, this.2.2⟩

include R hcd in
theorem comm15_torus (τ : Fˣ) (s t : F) :
    a2 ((τ : F)⁻¹ * s) ((τ : F) * t) = (τ : F)⁻¹ * a2 s t ∧ L ((τ : F)⁻¹ * s) ((τ : F) * t) = L s t ∧
      a4 ((τ : F)⁻¹ * s) ((τ : F) * t) = (τ : F) * a4 s t := by
  have eq : ∀ s t, ⁅D.p1 s, D.p5 t⁆ = Nel D (a2 s t) (L s t) (a4 s t) := fun s t => hcd.eq s t
  have hconj : D.T τ * ⁅D.p1 s, D.p5 t⁆ * (D.T τ)⁻¹ =
      ⁅D.p1 ((τ : F)⁻¹ * s), D.p5 ((τ : F) * t)⁆ := by
    have : D.T τ * ⁅D.p1 s, D.p5 t⁆ * (D.T τ)⁻¹ =
        ⁅D.T τ * D.p1 s * (D.T τ)⁻¹, D.T τ * D.p5 t * (D.T τ)⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [this, D.w1, D.w5]
  rw [eq s t, conj_T_Nel D τ (hcd.L_mem s t), eq] at hconj
  have := Nel_inj R D (hcd.L_mem _ _) (hcd.L_mem _ _) hconj
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

include R hcd in
theorem L_zero_left (t : F) : L 0 t = 1 := by
  have hp : D.p1 0 = 1 := map_zero_of_add' D.p1_add
  have h' : D.p2 (a2 0 t) * L 0 t * D.p4 (a4 0 t) = 1 := by
    have := hcd.eq 0 t
    rw [hp] at this
    simpa [commutatorElement_def] using this.symm
  have h0 : Nel D 0 1 0 = 1 := by
    unfold Nel
    rw [map_zero_of_add' D.p2_add, map_zero_of_add' D.p4_add]; group
  have h1 : Nel D (a2 0 t) (L 0 t) (a4 0 t) = Nel D 0 1 0 := by rw [h0]; exact h'
  exact (Nel_inj R D (hcd.L_mem _ _) (root 3).one_mem h1).2.1

include R hcd in
theorem L_zero_right (s : F) : L s 0 = 1 := by
  have hp : D.p5 0 = 1 := map_zero_of_add' D.p5_add
  have h' : D.p2 (a2 s 0) * L s 0 * D.p4 (a4 s 0) = 1 := by
    have := hcd.eq s 0
    rw [hp] at this
    simpa [commutatorElement_def] using this.symm
  have h0 : Nel D 0 1 0 = 1 := by
    unfold Nel
    rw [map_zero_of_add' D.p2_add, map_zero_of_add' D.p4_add]; group
  have h1 : Nel D (a2 s 0) (L s 0) (a4 s 0) = Nel D 0 1 0 := by rw [h0]; exact h'
  exact (Nel_inj R D (hcd.L_mem _ _) (root 3).one_mem h1).2.1

include R hcd in
theorem L_eq_mul (s t : F) : L s t = L 1 (s * t) := by
  by_cases hs : s = 0
  · subst hs
    rw [zero_mul, L_zero_left R D hcd, L_zero_right R D hcd]
  · have := (comm15_torus R D hcd (Units.mk0 s hs) s t).2.1
    simp only [Units.val_mk0, inv_mul_cancel₀ hs] at this
    exact this.symm

include R hC hμ hcd in
theorem mu_L (u : F) : μ (L 1 u) = μ (L 1 1) * u := by
  have h1 := (comm15_add_s R hC D hμ hcd 1 u 1).1
  have h2 := (comm15_add_s R hC D hμ hcd u 1 1).1
  rw [add_comm u 1, h1] at h2
  have h3 : μ (L u 1) = u * μ (L 1 1) := by linear_combination h2
  have h4 : L u 1 = L 1 u := by rw [L_eq_mul R D hcd u 1, mul_one]
  rw [← h4, h3, mul_comm]

end Ls

end CFSG.GH74.GLS.Stage4.Hex
