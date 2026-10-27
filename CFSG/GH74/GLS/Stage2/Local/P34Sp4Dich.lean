module

public import CFSG.ClassicalGroups.Alternating.Generation
import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Module Submodule
open LinearMap (BilinForm)
open CFSG.ClassicalGroups.Alternating CFSG.LocalAnalysis.ComponentInitial

section Setup

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

@[expose] def eig1 (τ : Module.End F V) : Submodule F V := LinearMap.ker (τ - 1)

@[expose] def eig2 (τ : Module.End F V) : Submodule F V := LinearMap.ker (τ + 1)

theorem mem_eig1 {τ : Module.End F V} {x : V} : x ∈ eig1 τ ↔ τ x = x := by
  simp [eig1, sub_eq_zero]

theorem mem_eig2 {τ : Module.End F V} {x : V} : x ∈ eig2 τ ↔ τ x = -x := by
  simp [eig2, add_eq_zero_iff_eq_neg]

structure InvData (B : BilinForm F V) (τ : Module.End F V) : Prop where
  two_ne_zero : (2 : F) ≠ 0
  sq : τ * τ = 1
  isometry : ∀ x y, B (τ x) (τ y) = B x y
  alt : B.IsAlt
  nondeg : B.Nondegenerate
  finrank_eq : finrank F (eig1 τ) = finrank F (eig2 τ)

variable {B : BilinForm F V} {τ : Module.End F V}

theorem InvData.apply_apply (h : InvData B τ) (y : V) : τ (τ y) = y := by
  have := congrArg (fun f : Module.End F V => f y) h.sq
  simpa using this

theorem InvData.decomp (h : InvData B τ) (x : V) : ∃ x₁ ∈ eig1 τ, ∃ x₂ ∈ eig2 τ, x = x₁ + x₂ := by
  refine ⟨(2 : F)⁻¹ • (x + τ x), ?_, (2 : F)⁻¹ • (x - τ x), ?_, ?_⟩
  · rw [mem_eig1, map_smul, map_add, h.apply_apply, add_comm]
  · rw [mem_eig2, map_smul, map_sub, h.apply_apply, ← smul_neg, neg_sub]
  · rw [← smul_add]
    have : x + τ x + (x - τ x) = (2 : F) • x := by module
    rw [this, smul_smul, inv_mul_cancel₀ h.two_ne_zero, one_smul]

theorem InvData.orth (h : InvData B τ) {x y : V} (hx : x ∈ eig1 τ) (hy : y ∈ eig2 τ) : B x y = 0 := by
  have h1 := h.isometry x y
  rw [mem_eig1.1 hx, mem_eig2.1 hy, map_neg] at h1
  have h2 : (2 : F) * B x y = 0 := by linear_combination -h1
  exact (mul_eq_zero.1 h2).resolve_left h.two_ne_zero

theorem InvData.eig_inf (h : InvData B τ) {x : V} (h1 : x ∈ eig1 τ) (h2 : x ∈ eig2 τ) : x = 0 := by
  have hxx : x = -x := (mem_eig1.1 h1).symm.trans (mem_eig2.1 h2)
  have h3 : x + x = 0 := by
    nth_rewrite 2 [hxx]
    exact add_neg_cancel x
  have h4 : (2 : F) • x = 0 := by rw [two_smul]; exact h3
  exact (smul_eq_zero.1 h4).resolve_left h.two_ne_zero

variable [FiniteDimensional F V]

theorem InvData.restrict_nondeg_aux (h : InvData B τ) {W W' : Submodule F V}
    (hdecomp : ∀ x : V, ∃ x₁ ∈ W, ∃ x₂ ∈ W', x = x₁ + x₂) (horth : ∀ x ∈ W, ∀ y ∈ W', B x y = 0) :
    (B.restrict W).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
  intro x hx
  have hx0 : (x : V) = 0 := by
    apply h.nondeg.1
    intro y
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hdecomp y
    rw [map_add, horth x x.2 y₂ hy₂, add_zero]
    exact hx ⟨y₁, hy₁⟩
  exact Subtype.ext hx0

theorem InvData.restrict1_nondeg (h : InvData B τ) : (B.restrict (eig1 τ)).Nondegenerate :=
  h.restrict_nondeg_aux h.decomp (fun _ hx _ hy => h.orth hx hy)

theorem InvData.restrict2_nondeg (h : InvData B τ) : (B.restrict (eig2 τ)).Nondegenerate :=
  h.restrict_nondeg_aux (W := eig2 τ) (W' := eig1 τ)
    (fun x => by
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.decomp x
      exact ⟨x₂, hx₂, x₁, hx₁, add_comm _ _⟩)
    (fun _ hx _ hy => by rw [← h.alt.neg_eq]; rw [h.orth hy hx, neg_zero])


omit [FiniteDimensional F V] in
theorem gl_apply_inv_apply' (g : LinearMap.GeneralLinearGroup F V) (x : V) :
    (g : V →ₗ[F] V) (((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Module.End.one_apply]

omit [FiniteDimensional F V] in
theorem conj_transvection (hB : B.IsAlt) {g : LinearMap.GeneralLinearGroup F V}
    (hg : g ∈ bilinIsometryGroup B) (a : V) (c : F) :
    g * symplecticTransvection B hB a c * g⁻¹ = symplecticTransvection B hB ((g : V →ₗ[F] V) a) c := by
  refine Units.ext (LinearMap.ext fun x => ?_)
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    symplecticTransvection_apply, symplecticTransvection_apply, map_add, map_smul,
    gl_apply_inv_apply']
  have hB' : B (((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) x) a = B x ((g : V →ₗ[F] V) a) := by
    have := hg (((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) x) a
    rw [gl_apply_inv_apply'] at this
    exact this.symm
  rw [hB']

omit [FiniteDimensional F V] in
theorem InvData.transvection_comm (h : InvData B τ) {a : V} (ha : a ∈ eig1 τ ∨ a ∈ eig2 τ) (c : F) :
    ((symplecticTransvection B h.alt a c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) * τ =
      τ * ((symplecticTransvection B h.alt a c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) := by
  refine LinearMap.ext fun x => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, symplecticTransvection_apply,
    symplecticTransvection_apply, map_add, map_smul]
  rcases ha with ha | ha
  · have h1 : B (τ x) a = B x a := by
      have := h.isometry x a
      rwa [mem_eig1.1 ha] at this
    rw [h1, mem_eig1.1 ha]
  · have h1 : B (τ x) a = -B x a := by
      have := h.isometry x a
      rw [mem_eig2.1 ha, map_neg] at this
      linear_combination -this
    rw [h1, mem_eig2.1 ha]
    simp only [smul_neg, mul_neg, neg_smul]


@[expose] def transSub (B : BilinForm F V) (hB : B.IsAlt) (W : Submodule F V) :
    Subgroup (LinearMap.GeneralLinearGroup F V) :=
  Subgroup.closure {g | ∃ v ∈ W, ∃ c : F, g = symplecticTransvection B hB v c}

omit [FiniteDimensional F V] in
theorem transSub_fix (hB : B.IsAlt) {W W' : Submodule F V} (horth : ∀ x ∈ W, ∀ y ∈ W', B x y = 0) :
    ∀ g ∈ transSub B hB W, ∀ y ∈ W', (g : V →ₗ[F] V) y = y := by
  intro g hg
  change g ∈ Subgroup.closure _ at hg
  refine Subgroup.closure_induction
    (p := fun (g : LinearMap.GeneralLinearGroup F V) _ => ∀ y ∈ W', (g : V →ₗ[F] V) y = y) ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨v, hv, c, rfl⟩ y hy
    apply symplecticTransvection_apply_of_apply_eq_zero hB c
    rw [← hB.neg_eq, horth v hv y hy, neg_zero]
  · intro y _; rfl
  · intro g₁ g₂ _ _ h1 h2 y hy
    rw [Units.val_mul, Module.End.mul_apply, h2 y hy, h1 y hy]
  · intro g _ h1 y hy
    have := h1 y hy
    calc ((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) y
        = ((g⁻¹ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) ((g : V →ₗ[F] V) y) := by rw [this]
      _ = y := by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

omit [FiniteDimensional F V] in
theorem exists_common_nonorth {W : Submodule F V} [FiniteDimensional F V] (hB : B.IsAlt)
    (hW : (B.restrict W).Nondegenerate) {a a' : V} (ha : a ∈ W) (ha' : a' ∈ W) (h0 : a ≠ 0)
    (h0' : a' ≠ 0) : ∃ w ∈ W, B a w ≠ 0 ∧ B a' w ≠ 0 := by
  obtain ⟨w, hw1, hw2⟩ := alternating_common_nonorthogonal_vector (B := B.restrict W)
    (isAlt_restrict hB W) hW (u := ⟨a, ha⟩) (v := ⟨a', ha'⟩) (fun h => h0 (congrArg Subtype.val h))
    (fun h => h0' (congrArg Subtype.val h))
  exact ⟨w, w.2, hw1, hw2⟩

theorem transSub_move (hB : B.IsAlt) {W : Submodule F V} (hW : (B.restrict W).Nondegenerate)
    {a a' : V} (ha : a ∈ W) (ha' : a' ∈ W) (h0 : a ≠ 0) (h0' : a' ≠ 0) :
    ∃ g ∈ transSub B hB W, (g : V →ₗ[F] V) a = a' := by
  by_cases hab : B a a' = 0
  · obtain ⟨w, hw, hw1, hw2⟩ := exists_common_nonorth hB hW ha ha' h0 h0'
    have hwa' : B w a' ≠ 0 := by
      rw [← hB.neg_eq]
      exact neg_ne_zero.mpr hw2
    refine ⟨symplecticTransvection B hB (a' - w) (B w a')⁻¹ *
      symplecticTransvection B hB (w - a) (B a w)⁻¹, ?_, ?_⟩
    · refine mul_mem (Subgroup.subset_closure ⟨a' - w, sub_mem ha' hw, _, rfl⟩)
        (Subgroup.subset_closure ⟨w - a, sub_mem hw ha, _, rfl⟩)
    · rw [Units.val_mul, Module.End.mul_apply, symplecticTransvection_sub_apply_self hB hw1,
        symplecticTransvection_sub_apply_self hB hwa']
  · exact ⟨symplecticTransvection B hB (a' - a) (B a a')⁻¹,
      Subgroup.subset_closure ⟨a' - a, sub_mem ha' ha, _, rfl⟩,
      symplecticTransvection_sub_apply_self hB hab⟩


omit [FiniteDimensional F V] in
theorem finrank_map_gl (g : LinearMap.GeneralLinearGroup F V) (W : Submodule F V) :
    finrank F (W.map (g : V →ₗ[F] V)) = finrank F W :=
  LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv F V g) W

@[expose] def CommPm (τ : Module.End F V) (g : LinearMap.GeneralLinearGroup F V) : Prop :=
  (g : V →ₗ[F] V) * τ = τ * (g : V →ₗ[F] V) ∨ (g : V →ₗ[F] V) * τ = -(τ * (g : V →ₗ[F] V))

theorem InvData.comm_of_map_eig1_le (h : InvData B τ) {g : LinearMap.GeneralLinearGroup F V}
    (hg : g ∈ bilinIsometryGroup B) (h1 : ∀ a ∈ eig1 τ, (g : V →ₗ[F] V) a ∈ eig1 τ) :
    (g : V →ₗ[F] V) * τ = τ * (g : V →ₗ[F] V) := by
  have hmap : (eig1 τ).map (g : V →ₗ[F] V) = eig1 τ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨a, ha, rfl⟩
      exact h1 a ha
    · exact finrank_map_gl g _
  have h2 : ∀ b ∈ eig2 τ, (g : V →ₗ[F] V) b ∈ eig2 τ := by
    intro b hb
    obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := h.decomp ((g : V →ₗ[F] V) b)
    have hy₁0 : y₁ = 0 := by
      have := h.restrict1_nondeg.1 ⟨y₁, hy₁⟩ (fun a => by
        have ha : (a : V) ∈ (eig1 τ).map (g : V →ₗ[F] V) := by rw [hmap]; exact a.2
        obtain ⟨a', ha', haa⟩ := ha
        change B y₁ (a : V) = 0
        have h3 : B ((g : V →ₗ[F] V) b) (a : V) = 0 := by
          rw [← haa, hg b a']
          rw [← h.alt.neg_eq, h.orth ha' hb, neg_zero]
        have h4 : B y₂ (a : V) = 0 := by
          rw [← h.alt.neg_eq, h.orth a.2 hy₂, neg_zero]
        rw [hy, map_add, LinearMap.add_apply, h4, add_zero] at h3
        exact h3)
      exact congrArg Subtype.val this
    rw [hy, hy₁0, zero_add]
    exact hy₂
  refine LinearMap.ext fun x => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.decomp x
  simp only [Module.End.mul_apply, map_add, mem_eig1.1 hx₁, mem_eig2.1 hx₂, map_neg,
    mem_eig1.1 (h1 x₁ hx₁), mem_eig2.1 (h2 x₂ hx₂)]


theorem InvData.anticomm_of_map_eig1_le_eig2 (h : InvData B τ) {g : LinearMap.GeneralLinearGroup F V}
    (hg : g ∈ bilinIsometryGroup B) (h1 : ∀ a ∈ eig1 τ, (g : V →ₗ[F] V) a ∈ eig2 τ) :
    (g : V →ₗ[F] V) * τ = -(τ * (g : V →ₗ[F] V)) := by
  have hmap : (eig1 τ).map (g : V →ₗ[F] V) = eig2 τ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨a, ha, rfl⟩
      exact h1 a ha
    · rw [finrank_map_gl, h.finrank_eq]
  have h2 : ∀ b ∈ eig2 τ, (g : V →ₗ[F] V) b ∈ eig1 τ := by
    intro b hb
    obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := h.decomp ((g : V →ₗ[F] V) b)
    have hy₂0 : y₂ = 0 := by
      have := h.restrict2_nondeg.1 ⟨y₂, hy₂⟩ (fun c => by
        have hc : (c : V) ∈ (eig1 τ).map (g : V →ₗ[F] V) := by rw [hmap]; exact c.2
        obtain ⟨a', ha', haa⟩ := hc
        change B y₂ (c : V) = 0
        have h3 : B ((g : V →ₗ[F] V) b) (c : V) = 0 := by
          rw [← haa, hg b a']
          rw [← h.alt.neg_eq, h.orth ha' hb, neg_zero]
        have h4 : B y₁ (c : V) = 0 := h.orth hy₁ c.2
        rw [hy, map_add, LinearMap.add_apply, h4, zero_add] at h3
        exact h3)
      exact congrArg Subtype.val this
    rw [hy, hy₂0, add_zero]
    exact hy₁
  refine LinearMap.ext fun x => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := h.decomp x
  simp only [Module.End.mul_apply, map_add, mem_eig1.1 hx₁, mem_eig2.1 hx₂, map_neg,
    mem_eig2.1 (h1 x₁ hx₁), mem_eig1.1 (h2 x₂ hx₂), LinearMap.neg_apply, neg_neg]


omit [FiniteDimensional F V] in
theorem InvData.transvection_mem (h : InvData B τ) (M : Subgroup (LinearMap.GeneralLinearGroup F V))
    (hC : ∀ g ∈ bilinIsometryGroup B, CommPm τ g → g ∈ M) {v : V} (hv : v ∈ eig1 τ ∨ v ∈ eig2 τ) (c : F) :
    symplecticTransvection B h.alt v c ∈ M :=
  hC _ (symplecticTransvection_mem_bilinIsometryGroup h.alt v c) (Or.inl (h.transvection_comm hv c))

theorem InvData.dichotomy (h : InvData B τ) (M : Subgroup (LinearMap.GeneralLinearGroup F V))
    (hMG : M ≤ bilinIsometryGroup B) (hC : ∀ g ∈ bilinIsometryGroup B, CommPm τ g → g ∈ M) :
    (∀ g ∈ M, CommPm τ g) ∨ M = bilinIsometryGroup B := by
  by_cases hall : ∀ g ∈ M, CommPm τ g
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨g, hgM, hgC⟩ := hall
  have hgG : g ∈ bilinIsometryGroup B := hMG hgM
  have hA : ∃ a ∈ eig1 τ, (g : V →ₗ[F] V) a ∉ eig1 τ ∧ (g : V →ₗ[F] V) a ∉ eig2 τ := by
    by_contra hno
    push Not at hno
    by_cases hcase : ∀ a ∈ eig1 τ, (g : V →ₗ[F] V) a ∈ eig1 τ
    · exact hgC (Or.inl (h.comm_of_map_eig1_le hgG hcase))
    · push Not at hcase
      obtain ⟨a₀, ha₀, ha₀n⟩ := hcase
      have ha₀2 : (g : V →ₗ[F] V) a₀ ∈ eig2 τ := hno a₀ ha₀ ha₀n
      have hall2 : ∀ a ∈ eig1 τ, (g : V →ₗ[F] V) a ∈ eig2 τ := by
        intro a ha
        by_cases ha1 : (g : V →ₗ[F] V) a ∈ eig1 τ
        · have hsum : (g : V →ₗ[F] V) (a + a₀) ∈ eig2 τ := by
            by_contra hn2
            have hs1 : (g : V →ₗ[F] V) (a + a₀) ∈ eig1 τ := by
              by_contra hn1
              exact hn2 (hno _ (add_mem ha ha₀) hn1)
            apply ha₀n
            have : (g : V →ₗ[F] V) a₀ = (g : V →ₗ[F] V) (a + a₀) - (g : V →ₗ[F] V) a := by
              rw [map_add]; abel
            rw [this]
            exact sub_mem hs1 ha1
          have : (g : V →ₗ[F] V) a = (g : V →ₗ[F] V) (a + a₀) - (g : V →ₗ[F] V) a₀ := by
            rw [map_add]; abel
          rw [this]
          exact sub_mem hsum ha₀2
        · exact hno a ha ha1
      exact hgC (Or.inr (h.anticomm_of_map_eig1_le_eig2 hgG hall2))
  obtain ⟨a, ha, han1, han2⟩ := hA
  obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := h.decomp ((g : V →ₗ[F] V) a)
  have hw₁0 : w₁ ≠ 0 := fun h0 => han2 (by rw [hw, h0, zero_add]; exact hw₂)
  have hw₂0 : w₂ ≠ 0 := fun h0 => han1 (by rw [hw, h0, add_zero]; exact hw₁)
  have hL1 : transSub B h.alt (eig1 τ) ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro _ ⟨v, hv, c, rfl⟩
    exact h.transvection_mem M hC (Or.inl hv) c
  have hL2 : transSub B h.alt (eig2 τ) ≤ M := by
    refine (Subgroup.closure_le M).2 ?_
    rintro _ ⟨v, hv, c, rfl⟩
    exact h.transvection_mem M hC (Or.inr hv) c
  have hTw : ∀ c, symplecticTransvection B h.alt ((g : V →ₗ[F] V) a) c ∈ M := by
    intro c
    rw [← conj_transvection h.alt hgG a c]
    exact mul_mem (mul_mem hgM (h.transvection_mem M hC (Or.inl ha) c)) (inv_mem hgM)
  have hTgen : ∀ (w₁' w₂' : V), w₁' ∈ eig1 τ → w₂' ∈ eig2 τ → w₁' ≠ 0 → w₂' ≠ 0 → ∀ c,
      symplecticTransvection B h.alt (w₁' + w₂') c ∈ M := by
    intro w₁' w₂' hw₁' hw₂' hw₁'0 hw₂'0 c
    obtain ⟨l₁, hl₁, hl₁a⟩ := transSub_move h.alt h.restrict1_nondeg hw₁ hw₁' hw₁0 hw₁'0
    obtain ⟨l₂, hl₂, hl₂a⟩ := transSub_move h.alt h.restrict2_nondeg hw₂ hw₂' hw₂0 hw₂'0
    have hl₁fix : (l₁ : V →ₗ[F] V) w₂ = w₂ :=
      transSub_fix h.alt (W := eig1 τ) (W' := eig2 τ) (fun x hx y hy => h.orth hx hy) l₁ hl₁ w₂ hw₂
    have hl₂fix : (l₂ : V →ₗ[F] V) w₁' = w₁' :=
      transSub_fix h.alt (W := eig2 τ) (W' := eig1 τ)
        (fun x hx y hy => by rw [← h.alt.neg_eq, h.orth hy hx, neg_zero]) l₂ hl₂ w₁' hw₁'
    have hlM : l₂ * l₁ ∈ M := mul_mem (hL2 hl₂) (hL1 hl₁)
    have hlw : ((l₂ * l₁ : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) ((g : V →ₗ[F] V) a) =
        w₁' + w₂' := by
      rw [hw, Units.val_mul, Module.End.mul_apply, map_add, hl₁a, hl₁fix, map_add, hl₂fix, hl₂a]
    have hconj := conj_transvection h.alt (hMG hlM) ((g : V →ₗ[F] V) a) c
    rw [hlw] at hconj
    rw [← hconj]
    exact mul_mem (mul_mem hlM (hTw c)) (inv_mem hlM)
  have hall' : ∀ a' c, symplecticTransvection B h.alt a' c ∈ M := by
    intro a' c
    obtain ⟨u₁, hu₁, u₂, hu₂, hu⟩ := h.decomp a'
    by_cases hu1z : u₁ = 0
    · have : a' ∈ eig2 τ := by rw [hu, hu1z, zero_add]; exact hu₂
      exact h.transvection_mem M hC (Or.inr this) c
    by_cases hu2z : u₂ = 0
    · have : a' ∈ eig1 τ := by rw [hu, hu2z, add_zero]; exact hu₁
      exact h.transvection_mem M hC (Or.inl this) c
    rw [hu]
    exact hTgen u₁ u₂ hu₁ hu₂ hu1z hu2z c
  apply le_antisymm hMG
  rw [alternating_transvection_generation h.alt h.nondeg]
  exact (Subgroup.closure_le M).2 (fun t ⟨a', c, ht⟩ => ht ▸ hall' a' c)


omit [FiniteDimensional F V] in
theorem InvData.not_commPm_transvection [FiniteDimensional F V] (h : InvData B τ) {a₁ a₂ : V}
    (ha₁ : a₁ ∈ eig1 τ) (ha₂ : a₂ ∈ eig2 τ) (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) {c : F} (hc : c ≠ 0) :
    ¬ CommPm τ (symplecticTransvection B h.alt (a₁ + a₂) c) := by
  intro hcomm
  obtain ⟨x, hx, hbx⟩ : ∃ x ∈ eig1 τ, B x a₁ ≠ 0 := by
    by_contra hno
    push Not at hno
    apply h₁
    have := h.restrict1_nondeg.1 ⟨a₁, ha₁⟩ (fun y => by
      change B a₁ (y : V) = 0
      rw [← h.alt.neg_eq, hno y y.2, neg_zero])
    exact congrArg Subtype.val this
  set b : F := c * B x a₁ with hb
  have hb0 : b ≠ 0 := mul_ne_zero hc hbx
  have hxa₂ : B x a₂ = 0 := h.orth hx ha₂
  have hτ : τ (a₁ + a₂) = a₁ - a₂ := by
    rw [map_add, mem_eig1.1 ha₁, mem_eig2.1 ha₂, sub_eq_add_neg]
  have hT : ((symplecticTransvection B h.alt (a₁ + a₂) c : LinearMap.GeneralLinearGroup F V) : V →ₗ[F] V) x =
      x + b • (a₁ + a₂) := by
    rw [symplecticTransvection_apply, map_add, hxa₂, add_zero]
  rcases hcomm with hc1 | hc2
  · have h1 := congrArg (fun f : Module.End F V => f x) hc1
    simp only [Module.End.mul_apply, mem_eig1.1 hx] at h1
    rw [hT, map_add, map_smul, hτ, mem_eig1.1 hx] at h1
    have h2 : (2 * b) • a₂ = 0 := by
      have e : (2 * b) • a₂ = (x + b • (a₁ + a₂)) - (x + b • (a₁ - a₂)) := by module
      rw [e, h1, sub_self]
    exact h₂ ((smul_eq_zero.1 h2).resolve_left (mul_ne_zero h.two_ne_zero hb0))
  · have h1 := congrArg (fun f : Module.End F V => f x) hc2
    simp only [Module.End.mul_apply, mem_eig1.1 hx, LinearMap.neg_apply] at h1
    rw [hT, map_add, map_smul, hτ, mem_eig1.1 hx] at h1
    have h2 : (2 : F) • (x + b • a₁) = 0 := by
      have e : (2 : F) • (x + b • a₁) = (x + b • (a₁ + a₂)) + (x + b • (a₁ - a₂)) := by module
      rw [e, h1, neg_add_cancel]
    have h3 : x + b • a₁ = 0 := (smul_eq_zero.1 h2).resolve_left h.two_ne_zero
    have h4 : x = -(b • a₁) := eq_neg_of_add_eq_zero_left h3
    apply hbx
    rw [h4, map_neg, LinearMap.neg_apply, map_smul, LinearMap.smul_apply, h.alt.self_eq_zero]
    simp

end Setup

end CFSG.GH74.GLS.Stage2.Local.P34
