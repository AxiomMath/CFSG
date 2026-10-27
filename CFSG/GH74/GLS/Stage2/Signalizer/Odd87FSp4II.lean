module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4FixQS
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutIFrame

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

structure TypeIIData {F : Type} [Field F] (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (d : F) :
    Prop where
  two_ne : (2 : F) ≠ 0
  d_ne : d ≠ 0
  sq : A * A = d • 1
  sim : Aᵀ * formJ 2 F * A = d • formJ 2 F
  nonsq : ∀ l : F, l ^ 2 ≠ d

noncomputable def transvVec {F : Type} [Field F] (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (d α β : F) (v y : Fin 2 ⊕ Fin 2 → F) : Fin 2 ⊕ Fin 2 → F :=
  (α * ωJ F y v + β * ωJ F y (A *ᵥ v)) • v +
    (β * ωJ F y v + α * d⁻¹ * ωJ F y (A *ᵥ v)) • (A *ᵥ v)

namespace TypeIIData

variable {F : Type} [Field F] {A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} {d : F}
  (h : TypeIIData A d)
include h

theorem mulVec_mulVec (v : Fin 2 ⊕ Fin 2 → F) : A *ᵥ (A *ᵥ v) = d • v := by
  rw [Matrix.mulVec_mulVec, h.sq, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem ωJ_sim (x y : Fin 2 ⊕ Fin 2 → F) : ωJ F (A *ᵥ x) (A *ᵥ y) = d * ωJ F x y :=
  ωJ_similitude h.sim x y

theorem ωJ_swap (x y : Fin 2 ⊕ Fin 2 → F) : ωJ F (A *ᵥ x) y = ωJ F x (A *ᵥ y) := by
  have hy : y = d⁻¹ • A *ᵥ (A *ᵥ y) := by
    rw [h.mulVec_mulVec, smul_smul, inv_mul_cancel₀ h.d_ne, one_smul]
  conv_lhs => rw [hy]
  rw [map_smul, h.ωJ_sim, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h.d_ne, one_mul]

theorem ωJ_self_A (v : Fin 2 ⊕ Fin 2 → F) : ωJ F v (A *ᵥ v) = 0 := by
  have h1 : ωJ F (A *ᵥ v) v = ωJ F v (A *ᵥ v) := h.ωJ_swap v v
  have h2 : ωJ F (A *ᵥ v) v = -ωJ F v (A *ᵥ v) := ωJ_comm _ _
  have h3 : (2 : F) * ωJ F v (A *ᵥ v) = 0 := by linear_combination h2 - h1
  exact (mul_eq_zero.mp h3).resolve_left h.two_ne

omit h in
theorem exists_ωJ_one {w : Fin 2 ⊕ Fin 2 → F} (hw : w ≠ 0) : ∃ u, ωJ F u w = 1 := by
  by_contra hno
  push Not at hno
  apply hw
  apply ωJ_nondeg
  intro y
  by_contra hy
  have hyw : ωJ F y w ≠ 0 := by rw [ωJ_comm]; exact neg_ne_zero.mpr hy
  exact hno ((ωJ F y w)⁻¹ • y) (by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hyw])

theorem A_ne_zero {v : Fin 2 ⊕ Fin 2 → F} (hv : v ≠ 0) : A *ᵥ v ≠ 0 := by
  intro h0
  apply hv
  have h1 := h.mulVec_mulVec v
  rw [h0, Matrix.mulVec_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left h.d_ne

theorem exists_pair {v : Fin 2 ⊕ Fin 2 → F} (hv : v ≠ 0) :
    ∃ y, ωJ F y v = 1 ∧ ωJ F y (A *ᵥ v) = 0 := by
  by_contra hno
  push Not at hno
  have hker : ∀ y, ωJ F y (A *ᵥ v) = 0 → ωJ F y v = 0 := by
    intro y hy
    by_contra hy'
    refine hno ((ωJ F y v)⁻¹ • y) ?_ ?_
    · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hy']
    · rw [map_smul, LinearMap.smul_apply, hy, smul_zero]
  obtain ⟨u₁, hu₁⟩ := exists_ωJ_one (h.A_ne_zero hv)
  set μ := ωJ F u₁ v with hμ
  have hv_eq : v = μ • A *ᵥ v := by
    have h0 : v - μ • A *ᵥ v = 0 := by
      apply ωJ_nondeg
      intro y
      have hy' := hker (y - ωJ F y (A *ᵥ v) • u₁) (by
        rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hu₁,
          mul_one, sub_self])
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at hy'
      rw [ωJ_comm, map_sub, map_smul, smul_eq_mul]
      linear_combination -hy'
    exact (sub_eq_zero.mp h0)
  have hAv : A *ᵥ v = (μ * d) • v := by
    have h1 := congrArg (fun z => A *ᵥ z) hv_eq
    simp only [Matrix.mulVec_smul, h.mulVec_mulVec, smul_smul] at h1
    exact h1
  have h3 : v = (μ * (μ * d)) • v := by
    calc v = μ • A *ᵥ v := hv_eq
      _ = μ • (μ * d) • v := by rw [hAv]
      _ = (μ * (μ * d)) • v := by rw [smul_smul]
  have h4 : (1 - μ * (μ * d)) • v = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
  have h5 : 1 - μ * (μ * d) = 0 := (smul_eq_zero.mp h4).resolve_right hv
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at h5
    simp at h5
  apply h.nonsq μ⁻¹
  field_simp
  linear_combination h5

theorem ωJ_transv (α β : F) (v x y : Fin 2 ⊕ Fin 2 → F) :
    ωJ F (x + transvVec A d α β v x) (y + transvVec A d α β v y) = ωJ F x y := by
  have e1 : ωJ F v y = -ωJ F y v := ωJ_comm _ _
  have e2 : ωJ F (A *ᵥ v) y = -ωJ F y (A *ᵥ v) := ωJ_comm _ _
  have e3 : ωJ F v v = 0 := ωJ_self _
  have e4 : ωJ F v (A *ᵥ v) = 0 := h.ωJ_self_A v
  have e5 : ωJ F (A *ᵥ v) v = 0 := by rw [ωJ_comm, e4, neg_zero]
  have e6 : ωJ F (A *ᵥ v) (A *ᵥ v) = 0 := ωJ_self _
  simp only [transvVec, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, e1, e2, e3, e4, e5, e6]
  ring

theorem A_transv (α β : F) (v x : Fin 2 ⊕ Fin 2 → F) :
    A *ᵥ (x + transvVec A d α β v x) = (A *ᵥ x) + transvVec A d α β v (A *ᵥ x) := by
  have hd : d ≠ 0 := h.d_ne
  simp only [transvVec, Matrix.mulVec_add, Matrix.mulVec_smul, h.mulVec_mulVec, h.ωJ_swap,
    map_smul, smul_eq_mul]
  match_scalars <;> field_simp <;> ring

omit h in
theorem symp_of_forall {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hG : ∀ x y, ωJ F (G *ᵥ x) (G *ᵥ y) = ωJ F x y) : Gᵀ * formJ 2 F * G = formJ 2 F := by
  refine Matrix.toBilin'.injective ?_
  rw [← Matrix.toBilin'_comp]
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  simp only [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply]
  exact hG x y

theorem exists_transvection (α β : F) (v : Fin 2 ⊕ Fin 2 → F) :
    ∃ G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, Gᵀ * formJ 2 F * G = formJ 2 F ∧
      A * G = G * A ∧ ∀ y, G *ᵥ y = y + transvVec A d α β v y := by
  let N : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] (Fin 2 ⊕ Fin 2 → F) :=
    (α • (ωJ F).flip v + β • (ωJ F).flip (A *ᵥ v)).smulRight v +
    (β • (ωJ F).flip v + (α * d⁻¹) • (ωJ F).flip (A *ᵥ v)).smulRight (A *ᵥ v)
  have hN : ∀ y, N y = transvVec A d α β v y := by
    intro y
    simp [N, transvVec]
  let G := LinearMap.toMatrix' (LinearMap.id + N)
  have hG : ∀ y, G *ᵥ y = y + transvVec A d α β v y := by
    intro y
    rw [LinearMap.toMatrix'_mulVec]
    simp [hN]
  refine ⟨G, ?_, ?_, hG⟩
  · apply symp_of_forall
    intro x y
    rw [hG, hG]
    exact h.ωJ_transv α β v x y
  · rw [Matrix.ext_iff_mulVec]
    intro y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG, hG]
    exact h.A_transv α β v y

theorem indep {v : Fin 2 ⊕ Fin 2 → F} (hv : v ≠ 0) {a b : F}
    (hab : a • v + b • A *ᵥ v = 0) : a = 0 ∧ b = 0 := by
  have h2 : b • d • v + a • A *ᵥ v = 0 := by
    have h1 := congrArg (fun z => A *ᵥ z) hab
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rw [add_comm]
    exact h1
  have h3 : (a * a - d * (b * b)) • v = 0 := by
    have h4 : a • (a • v + b • A *ᵥ v) - b • (b • d • v + a • A *ᵥ v) = 0 := by
      rw [hab, h2]; simp
    rw [← h4]
    module
  have h5 : a * a - d * (b * b) = 0 := (smul_eq_zero.mp h3).resolve_right hv
  have hb : b = 0 := by
    by_contra hb
    apply h.nonsq (a * b⁻¹)
    field_simp
    linear_combination h5
  refine ⟨?_, hb⟩
  rw [hb] at h5
  have h6 : a * a = 0 := by linear_combination h5
  exact mul_self_eq_zero.mp h6

theorem mem_of_combo {v₀ w : Fin 2 ⊕ Fin 2 → F} {γ δ a₁ b₁ : F} (hγδ : γ ≠ 0 ∨ δ ≠ 0)
    (heq : γ • w + δ • A *ᵥ w = a₁ • v₀ + b₁ • A *ᵥ v₀) :
    ∃ a b : F, w = a • v₀ + b • A *ᵥ v₀ := by
  have hc : γ * γ - d * (δ * δ) ≠ 0 := by
    intro hc
    rcases hγδ with hγ | hδ
    · by_cases hδ : δ = 0
      · rw [hδ] at hc
        simp at hc
        exact hγ hc
      · apply h.nonsq (γ * δ⁻¹)
        field_simp
        linear_combination hc
    · apply h.nonsq (γ * δ⁻¹)
      field_simp
      linear_combination hc
  have h1 : (γ * γ - d * (δ * δ)) • w =
      (γ * a₁ - δ * (b₁ * d)) • v₀ + (γ * b₁ - δ * a₁) • A *ᵥ v₀ := by
    have h2 := congrArg (fun z => γ • z - δ • A *ᵥ z) heq
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h.mulVec_mulVec, smul_add] at h2
    rw [← sub_eq_zero] at h2 ⊢
    rw [← h2]
    module
  refine ⟨(γ * γ - d * (δ * δ))⁻¹ * (γ * a₁ - δ * (b₁ * d)),
    (γ * γ - d * (δ * δ))⁻¹ * (γ * b₁ - δ * a₁), ?_⟩
  rw [← smul_smul, ← smul_smul, ← smul_add, ← h1, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem frame_step {f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hcomm : ∀ α β v y, f *ᵥ transvVec A d α β v y = transvVec A d α β v (f *ᵥ y))
    {v : Fin 2 ⊕ Fin 2 → F} (hv : v ≠ 0) :
    ∃ a b : F, f *ᵥ v = a • v + b • A *ᵥ v ∧ f *ᵥ (A *ᵥ v) = (d * b) • v + a • A *ᵥ v := by
  obtain ⟨y, hy1, hy2⟩ := h.exists_pair hv
  have e1 := hcomm 1 0 v y
  have e2 := hcomm 0 1 v y
  simp only [transvVec, hy1, hy2, one_mul, zero_mul, add_zero, zero_add, mul_zero, one_smul,
    zero_smul] at e1 e2
  refine ⟨ωJ F (f *ᵥ y) v, d⁻¹ * ωJ F (f *ᵥ y) (A *ᵥ v), e1, ?_⟩
  have hd : d ≠ 0 := h.d_ne
  rw [e2, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem frame_comm {f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hcomm : ∀ α β v y, f *ᵥ transvVec A d α β v y = transvVec A d α β v (f *ᵥ y))
    (v : Fin 2 ⊕ Fin 2 → F) : f *ᵥ (A *ᵥ v) = A *ᵥ (f *ᵥ v) := by
  by_cases hv : v = 0
  · rw [hv]; simp
  · obtain ⟨a, b, h1, h2⟩ := h.frame_step hcomm hv
    rw [h2, h1]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h.mulVec_mulVec]
    module

theorem scalar_of_frame {f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hcomm : ∀ α β v y, f *ᵥ transvVec A d α β v y = transvVec A d α β v (f *ᵥ y)) :
    ∃ a b : F, f = a • 1 + b • A := by
  have hAf := h.frame_comm hcomm
  have hfv : ∀ v, ∃ a b : F, f *ᵥ v = a • v + b • A *ᵥ v := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, 0, by simp [hv]⟩
    · obtain ⟨a, b, h1, -⟩ := h.frame_step hcomm hv
      exact ⟨a, b, h1⟩
  set v₀ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1 with hv₀
  have hv₀ne : v₀ ≠ 0 := by
    intro h0
    have h1 := congrFun h0 (Sum.inl 0)
    simp [hv₀] at h1
  obtain ⟨a, b, hab⟩ := hfv v₀
  refine ⟨a, b, ?_⟩
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  by_cases hw : ∃ a₁ b₁ : F, w = a₁ • v₀ + b₁ • A *ᵥ v₀
  · obtain ⟨a₁, b₁, rfl⟩ := hw
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hAf v₀, hab, h.mulVec_mulVec]
    module
  · obtain ⟨a', b', hw'⟩ := hfv w
    obtain ⟨a'', b'', hw''⟩ := hfv (v₀ + w)
    have hsum : (a'' - a') • w + (b'' - b') • A *ᵥ w =
        (a - a'') • v₀ + (b - b'') • A *ᵥ v₀ := by
      have h1 : f *ᵥ (v₀ + w) = f *ᵥ v₀ + f *ᵥ w := Matrix.mulVec_add _ _ _
      rw [hw'', hab, hw'] at h1
      simp only [Matrix.mulVec_add] at h1
      have h2 := sub_eq_zero.mpr h1
      rw [← sub_eq_zero, ← h2]
      module
    have hγδ : a'' - a' = 0 ∧ b'' - b' = 0 := by
      by_contra hne
      apply hw
      refine h.mem_of_combo ?_ hsum
      by_contra hcon
      push Not at hcon
      exact hne ⟨hcon.1, hcon.2⟩
    obtain ⟨hγ, hδ⟩ := hγδ
    have h3 : (a - a'') • v₀ + (b - b'') • A *ᵥ v₀ = 0 := by
      rw [← hsum, hγ, hδ, zero_smul, zero_smul, add_zero]
    obtain ⟨h4, h5⟩ := h.indep hv₀ne h3
    have h6 : a' = a := by linear_combination -hγ - h4
    have h7 : b' = b := by linear_combination -hδ - h5
    rw [hw', h6, h7]

theorem ωJ_affine (a b : F) (u u' : Fin 2 ⊕ Fin 2 → F) :
    ωJ F (a • u + b • A *ᵥ u) (a • u' + b • A *ᵥ u') =
      (a * a + d * (b * b)) * ωJ F u u' + 2 * (a * b) * ωJ F u (A *ᵥ u') := by
  have e1 := h.ωJ_sim u u'
  have e2 := h.ωJ_swap u u'
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2]
  ring

theorem eq_one_or_neg_one {f : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hf : fᵀ * formJ 2 F * f = formJ 2 F)
    (hcomm : ∀ α β v y, f *ᵥ transvVec A d α β v y = transvVec A d α β v (f *ᵥ y)) :
    f = 1 ∨ f = -1 := by
  obtain ⟨a, b, hfab⟩ := h.scalar_of_frame hcomm
  have hmul : ∀ u, f *ᵥ u = a • u + b • A *ᵥ u := by
    intro u
    rw [hfab, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  set v₀ : Fin 2 ⊕ Fin 2 → F := Pi.single (Sum.inl 0) 1 with hv₀
  have hv₀ne : v₀ ≠ 0 := by
    intro h0
    have h1 := congrFun h0 (Sum.inl 0)
    simp [hv₀] at h1
  obtain ⟨y₁, hy1, hy2⟩ := h.exists_pair hv₀ne
  have hd : d ≠ 0 := h.d_ne
  have hy3 : ωJ F (d⁻¹ • A *ᵥ y₁) v₀ = 0 := by
    rw [map_smul, LinearMap.smul_apply, h.ωJ_swap, hy2, smul_zero]
  have hy4 : ωJ F (d⁻¹ • A *ᵥ y₁) (A *ᵥ v₀) = 1 := by
    rw [map_smul, LinearMap.smul_apply, h.ωJ_sim, hy1, smul_eq_mul, mul_one,
      inv_mul_cancel₀ hd]
  have e1 := ωJ_mulVec hf y₁ v₀
  have e2 := ωJ_mulVec hf (d⁻¹ • A *ᵥ y₁) v₀
  simp only [hmul, h.ωJ_affine, hy1, hy2, hy3, hy4, mul_one, mul_zero, zero_add, add_zero] at e1 e2
  have hab0 : a * b = 0 := (mul_eq_zero.mp e2).resolve_left h.two_ne
  rcases mul_eq_zero.mp hab0 with ha | hb
  · exfalso
    rw [ha] at e1
    have hb : b ≠ 0 := by
      rintro rfl
      simp at e1
    apply h.nonsq b⁻¹
    field_simp
    linear_combination -e1
  · rw [hb] at e1
    have h1 : a * a = 1 := by linear_combination e1
    rcases mul_self_eq_one_iff.mp h1 with ha | ha
    · left
      rw [hfab, ha, hb]
      simp
    · right
      rw [hfab, ha, hb]
      simp

end TypeIIData

theorem mem_fixOf_conjSp_of_comm {F : Type} [Field F] (A : gsp 2 F) {Z : StatedSp 2 F}
    (h : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((Z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((Z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) :
    Z ∈ fixOf (conjSp 2 F A) := by
  show conjSp 2 F A Z = Z
  apply sp_ext
  rw [coe_conjSp, Units.val_mul, Units.val_mul, h, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one]

theorem typeII_centralizer_scalar {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (A : gsp 2 F) (d : Fˣ)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = (d : F) • 1)
    (hdm : (d : F) = (multiplierUnit A : F)) (hsq : ∀ l : F, l ^ 2 ≠ (multiplierUnit A : F))
    (x : StatedSp 2 F) (hx : ∀ g ∈ fixOf (conjSp 2 F A), x * g = g * x) :
    x ∈ spScalars 2 F := by
  have hdata : TypeIIData ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
      (d : F) :=
    ⟨Ring.two_ne_zero hodd, d.ne_zero, hAA, by rw [hdm]; exact multiplierUnit_spec A,
      by rw [hdm]; exact hsq⟩
  rw [mem_spScalars_iff]
  refine hdata.eq_one_or_neg_one (symplectic_of_mem x) ?_
  intro α β v y
  obtain ⟨G, hGs, hGA, hGy⟩ := hdata.exists_transvection α β v
  have hg : toSp G hGs ∈ fixOf (conjSp 2 F A) :=
    mem_fixOf_conjSp_of_comm A (by rw [coe_toSp]; exact hGA)
  have hxg := hx (toSp G hGs) hg
  have hmat : ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) * G =
      G * ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    have h1 := congrArg (fun z : StatedSp 2 F =>
      ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hxg
    simpa only [Subgroup.coe_mul, Units.val_mul, coe_toSp] using h1
  have h2 := congrArg (fun M => M *ᵥ y) hmat
  simp only [← Matrix.mulVec_mulVec, hGy, Matrix.mulVec_add] at h2
  exact add_left_cancel h2

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
