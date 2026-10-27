module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensorDecomp

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open TensorProduct Module

universe u v

section Flip

variable {F : Type u} [Field F] {U : Type u} [AddCommGroup U] [Module F U]

theorem smul_tmul_smul' (c d : F) (a b : U) :
    (c • a) ⊗ₜ[F] (d • b) = (c * d) • (a ⊗ₜ[F] b) := by
  rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, mul_comm]

theorem exists_dual_apply_eq_one {x : U} (hx : x ≠ 0) : ∃ φ : U →ₗ[F] F, φ x = 1 := by
  obtain ⟨φ₀, hφ₀⟩ := Module.Projective.exists_dual_ne_zero F hx
  exact ⟨(φ₀ x)⁻¹ • φ₀, by simp [hφ₀]⟩

theorem exists_mul_self_eq [Finite F] [CharP F 2] (l : F) : ∃ μ : F, μ * μ = l := by
  have hinj : Function.Injective (fun c : F => c * c) := by
    intro c d h
    rcases mul_self_eq_mul_self_iff.1 h with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  exact (Finite.injective_iff_surjective.1 hinj) l

theorem exists_smul_of_tensor_comm [Nontrivial U] (x y : U ≃ₗ[F] U)
    (h : ∀ u v : U, y v ⊗ₜ[F] x u = x v ⊗ₜ[F] y u) : ∃ l : F, ∀ v, y v = l • x v := by
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : U)
  have hx : x u₀ ≠ 0 := fun h0 => hu₀ (x.injective (by rw [h0, map_zero]))
  obtain ⟨φ, hφ⟩ := exists_dual_apply_eq_one (F := F) hx
  refine ⟨φ (y u₀), fun v => ?_⟩
  have h1 := congrArg (TensorProduct.comm F U U) (h u₀ v)
  rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul] at h1
  have h2 := congrArg (sliceL φ) h1
  rw [sliceL_tmul, sliceL_tmul, hφ, one_smul] at h2
  exact h2

theorem exists_tensor_square [Finite F] [CharP F 2] [Nontrivial U] (x y : U ≃ₗ[F] U)
    (h : ∀ u v : U, y v ⊗ₜ[F] x u = x v ⊗ₜ[F] y u) :
    ∃ g : U ≃ₗ[F] U, ∀ u v, x u ⊗ₜ[F] y v = g u ⊗ₜ[F] g v := by
  obtain ⟨l, hl⟩ := exists_smul_of_tensor_comm x y h
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : U)
  have hl0 : l ≠ 0 := by
    intro h0
    have := hl (x.symm u₀)
    rw [h0, zero_smul] at this
    exact hu₀ (by simpa using y.injective (this.trans (map_zero y).symm))
  obtain ⟨μ, hμ⟩ := exists_mul_self_eq (F := F) l
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hl0 (by rw [← hμ, mul_zero])
  refine ⟨x.trans (LinearEquiv.smulOfNeZero F U μ hμ0), fun u v => ?_⟩
  show x u ⊗ₜ[F] y v = (μ • x u) ⊗ₜ[F] (μ • x v)
  rw [hl v, TensorProduct.tmul_smul, smul_tmul_smul', hμ]

theorem eq_of_tensor_square_eq [CharP F 2] [Nontrivial U] (g h : U ≃ₗ[F] U)
    (hgh : ∀ u v : U, g u ⊗ₜ[F] g v = h u ⊗ₜ[F] h v) : g = h := by
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : U)
  have hg : g u₀ ≠ 0 := fun h0 => hu₀ (g.injective (by rw [h0, map_zero]))
  have hh : h u₀ ≠ 0 := fun h0 => hu₀ (h.injective (by rw [h0, map_zero]))
  obtain ⟨ψ, hψ⟩ := exists_dual_apply_eq_one (F := F) hg
  have h1 : ∀ v, g v = (ψ (h u₀)) • h v := by
    intro v
    have := congrArg (sliceL ψ) (hgh u₀ v)
    rw [sliceL_tmul, sliceL_tmul, hψ, one_smul] at this
    exact this
  have h2 : (ψ (h u₀) * ψ (h u₀) - 1) • (h u₀ ⊗ₜ[F] h u₀) = 0 := by
    have := hgh u₀ u₀
    rw [h1 u₀, smul_tmul_smul'] at this
    rw [sub_smul, one_smul, this, sub_self]
  have h3 : h u₀ ⊗ₜ[F] h u₀ ≠ 0 := by
    intro h0
    obtain ⟨φ, hφ⟩ := exists_dual_apply_eq_one (F := F) hh
    have := congrArg (sliceL φ) h0
    rw [sliceL_tmul, hφ, one_smul, map_zero] at this
    exact hh this
  have h4 : ψ (h u₀) * ψ (h u₀) - 1 = 0 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h h3
  have h5 : ψ (h u₀) = 1 := by
    have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
    have : (ψ (h u₀) - 1) * (ψ (h u₀) - 1) = 0 := by
      linear_combination h4 + (1 - ψ (h u₀)) * h2'
    have := mul_self_eq_zero.1 this
    exact sub_eq_zero.1 this
  ext v
  rw [h1 v, h5, one_smul]


theorem exists_gamma [Finite F] [CharP F 2] [Nontrivial U]
    (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)))
    (hform : ∀ b ∈ B, ∃ x y : U ≃ₗ[F] U, ∀ u v, b (u ⊗ₜ[F] v) = x u ⊗ₜ[F] y v)
    (hcomm : ∀ b ∈ B, ∀ w, b (TensorProduct.comm F U U w) = TensorProduct.comm F U U (b w)) :
    ∃ γ : B →* (U ≃ₗ[F] U), ∀ (b : B) (u v : U),
      (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = γ b u ⊗ₜ[F] γ b v := by
  have hex : ∀ b : B, ∃ g : U ≃ₗ[F] U, ∀ u v : U,
      (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = g u ⊗ₜ[F] g v := by
    intro b
    obtain ⟨x, y, hxy⟩ := hform b b.2
    have h : ∀ u v, y v ⊗ₜ[F] x u = x v ⊗ₜ[F] y u := by
      intro u v
      have h1 := hcomm b b.2 (u ⊗ₜ[F] v)
      rw [TensorProduct.comm_tmul, hxy, hxy, TensorProduct.comm_tmul] at h1
      exact h1.symm
    obtain ⟨g, hg⟩ := exists_tensor_square x y h
    exact ⟨g, fun u v => by rw [hxy, hg]⟩
  choose g hg using hex
  refine ⟨MonoidHom.mk' g (fun b b' => ?_), hg⟩
  apply eq_of_tensor_square_eq
  intro u v
  calc g (b * b') u ⊗ₜ[F] g (b * b') v
      = (b * b' : B).1 (u ⊗ₜ[F] v) := (hg (b * b') u v).symm
    _ = b.1 (b'.1 (u ⊗ₜ[F] v)) := rfl
    _ = b.1 (g b' u ⊗ₜ[F] g b' v) := by rw [hg b' u v]
    _ = g b (g b' u) ⊗ₜ[F] g b (g b' v) := hg b _ _
    _ = ((g b * g b') u) ⊗ₜ[F] ((g b * g b') v) := rfl

theorem gamma_injective (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U))) (γ : B →* (U ≃ₗ[F] U))
    (hγ : ∀ (b : B) (u v : U),
      (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = γ b u ⊗ₜ[F] γ b v) :
    Function.Injective γ := by
  rw [injective_iff_map_eq_one]
  intro b hb
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  induction w with
  | tmul u v => rw [hγ, hb]; rfl
  | add x y hx hy => rw [map_add, hx, hy]; rfl

theorem tensor_identity_of_fix
    (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U))) (γ : B →* (U ≃ₗ[F] U))
    (hγ : ∀ (b : B) (u v : U),
      (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = γ b u ⊗ₜ[F] γ b v)
    (hfix : ∀ b ∈ B, ∀ w, b (TensorProduct.comm F U U w - w) = TensorProduct.comm F U U w - w)
    (b : B) (u v : U) :
    γ b v ⊗ₜ[F] γ b u - γ b u ⊗ₜ[F] γ b v = v ⊗ₜ[F] u - u ⊗ₜ[F] v := by
  have := hfix b b.2 (u ⊗ₜ[F] v)
  rw [TensorProduct.comm_tmul, map_sub, hγ b v u, hγ b u v] at this
  exact this


theorem pair_indep {u v : U} (hu : u ≠ 0) (hv : v ∉ Submodule.span F {u}) :
    LinearIndependent F ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, add_zero] at hab
    exact ⟨(smul_eq_zero.1 hab).resolve_right hu, rfl⟩
  · exfalso
    apply hv
    have : v = (-(b⁻¹ * a)) • u := by
      have h1 : b • v = -(a • u) := eq_neg_of_add_eq_zero_right hab
      calc v = b⁻¹ • (b • v) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
        _ = (-(b⁻¹ * a)) • u := by rw [h1, smul_neg, smul_smul, neg_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem exists_dual_pair {u v : U} (huv : LinearIndependent F ![u, v]) :
    (∃ ψ : U →ₗ[F] F, ψ u = 0 ∧ ψ v = 1) ∧ (∃ ψ : U →ₗ[F] F, ψ u = 1 ∧ ψ v = 0) := by
  have hpair := LinearIndependent.pair_iff.1 huv
  have key : ∀ {a b : U}, (∀ s t : F, s • a + t • b = 0 → s = 0 ∧ t = 0) →
      ∃ ψ : U →ₗ[F] F, ψ a = 0 ∧ ψ b = 1 := by
    intro a b h
    have hb : b ∉ Submodule.span F {a} := by
      intro hmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
      have := h (-c) 1 (by rw [neg_smul, one_smul, hc, neg_add_cancel])
      exact one_ne_zero this.2
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hb inferInstance
    have hfa : f a = 0 := by
      have : f a ∈ (Submodule.span F {a}).map f :=
        Submodule.mem_map_of_mem (Submodule.subset_span rfl)
      rw [hf'] at this
      exact (Submodule.mem_bot F).1 this
    exact ⟨(f b)⁻¹ • f, by simp [hfa], by simp [hf]⟩
  refine ⟨key hpair, ?_⟩
  obtain ⟨ψ, h0, h1⟩ := key (a := v) (b := u) (fun s t hst => by
    have := hpair t s (by rw [add_comm]; exact hst)
    exact ⟨this.2, this.1⟩)
  exact ⟨ψ, h1, h0⟩

theorem plane_le (g : U ≃ₗ[F] U)
    (hD : ∀ u v : U, g v ⊗ₜ[F] g u - g u ⊗ₜ[F] g v = v ⊗ₜ[F] u - u ⊗ₜ[F] v)
    {u v : U} (huv : LinearIndependent F ![u, v]) :
    Submodule.span F {u, v} ≤ Submodule.span F {g u, g v} := by
  have hE : ∀ ψ : U →ₗ[F] F, ψ (g v) • g u - ψ (g u) • g v = ψ v • u - ψ u • v := by
    intro ψ
    have := congrArg (sliceL ψ) (hD u v)
    simpa [map_sub, sliceL_tmul] using this
  obtain ⟨⟨ψ₁, h1u, h1v⟩, ⟨ψ₂, h2u, h2v⟩⟩ := exists_dual_pair huv
  have hmem : ∀ a b : F, a • g u - b • g v ∈ Submodule.span F {g u, g v} := fun a b =>
    Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hu : u ∈ Submodule.span F {g u, g v} := by
    have h1 := hE ψ₁
    rw [h1u, h1v, zero_smul, one_smul, sub_zero] at h1
    have h2 := hmem (ψ₁ (g v)) (ψ₁ (g u))
    rwa [h1] at h2
  have hv : v ∈ Submodule.span F {g u, g v} := by
    have h1 := hE ψ₂
    rw [h2u, h2v, zero_smul, one_smul, zero_sub] at h1
    have h2 := hmem (ψ₂ (g v)) (ψ₂ (g u))
    rw [h1] at h2
    exact (Submodule.neg_mem_iff _).1 h2
  rw [Submodule.span_le]
  rintro x (hx | hx)
  · rw [hx]; exact hu
  · rw [hx]; exact hv


theorem plane_stable (g g' : U ≃ₗ[F] U) (hg' : ∀ u, g' (g u) = u)
    (hD' : ∀ u v : U, g' v ⊗ₜ[F] g' u - g' u ⊗ₜ[F] g' v = v ⊗ₜ[F] u - u ⊗ₜ[F] v)
    {u v : U} (huv : LinearIndependent F ![u, v]) :
    g u ∈ Submodule.span F {u, v} ∧ g v ∈ Submodule.span F {u, v} := by
  have hind : LinearIndependent F ![g u, g v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have : s • u + t • v = 0 := by
      apply g.injective
      rw [map_add, map_smul, map_smul, hst, map_zero]
    exact LinearIndependent.pair_iff.1 huv s t this
  have h := plane_le g' hD' hind
  rw [hg', hg'] at h
  exact ⟨h (Submodule.subset_span (by simp)), h (Submodule.subset_span (by simp))⟩

theorem exists_not_mem_span_finset [Module.Finite F U] (t : Finset U)
    (h : t.card < Module.finrank F U) : ∃ w : U, w ∉ Submodule.span F (t : Set U) := by
  by_contra hcon
  push Not at hcon
  have htop : Submodule.span F (t : Set U) = ⊤ := eq_top_iff.2 (fun w _ => hcon w)
  have := finrank_span_finset_le_card (R := F) t
  rw [Set.finrank, htop, finrank_top] at this
  omega

theorem exists_smul_eq_of_planes [Module.Finite F U] (g : U ≃ₗ[F] U)
    (h3 : 3 ≤ Module.finrank F U)
    (hplane : ∀ u v : U, LinearIndependent F ![u, v] →
      g u ∈ Submodule.span F {u, v} ∧ g v ∈ Submodule.span F {u, v})
    (u : U) (hu : u ≠ 0) : ∃ c : F, g u = c • u := by
  classical
  obtain ⟨v, hv⟩ := exists_not_mem_span_finset (F := F) ({u} : Finset U) (by simp; omega)
  have hv' : v ∉ Submodule.span F {u} := by simpa using hv
  obtain ⟨w, hw⟩ := exists_not_mem_span_finset (F := F) ({u, v} : Finset U)
    (lt_of_le_of_lt Finset.card_le_two (by omega))
  have hw' : w ∉ Submodule.span F {u, v} := by simpa using hw
  have hw1 : w ∉ Submodule.span F {u} := fun h =>
    hw' (Submodule.span_mono (by intro x hx; simp at hx; simp [hx]) h)
  have h1 := (hplane u v (pair_indep hu hv')).1
  have h2 := (hplane u w (pair_indep hu hw1)).1
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 h1
  obtain ⟨a', b', hab'⟩ := Submodule.mem_span_pair.1 h2
  by_cases hb' : b' = 0
  · exact ⟨a', by rw [← hab', hb', zero_smul, add_zero]⟩
  · exfalso
    apply hw'
    have e1 : a • u + b • v = a' • u + b' • w := hab.trans hab'.symm
    have e2 : b' • w = (a - a') • u + b • v := by
      rw [sub_smul, eq_sub_of_add_eq' e1.symm]
      abel
    have : w = b'⁻¹ • ((a - a') • u + b • v) := by
      rw [← e2, smul_smul, inv_mul_cancel₀ hb', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))


theorem tmul_sub_ne_zero {u v : U} (huv : LinearIndependent F ![u, v]) :
    v ⊗ₜ[F] u - u ⊗ₜ[F] v ≠ 0 := by
  obtain ⟨⟨ψ, hψu, hψv⟩, _⟩ := exists_dual_pair huv
  intro h0
  have := congrArg (sliceL ψ) h0
  rw [map_sub, sliceL_tmul, sliceL_tmul, hψu, hψv, one_smul, zero_smul, sub_zero,
    LinearMap.map_zero] at this
  exact huv.ne_zero 0 this

theorem eq_smul_one_of_lines (g : U ≃ₗ[F] U) (hline : ∀ u : U, ∃ c : F, g u = c • u) :
    ∃ a : F, ∀ u, g u = a • u := by
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := (g : U →ₗ[F] U)) (fun v hli => by
      obtain ⟨c, hc⟩ := hline v
      have := LinearIndependent.pair_iff.1 hli c (-1) (by simp [hc])
      exact absurd this.2 (by simp))
  exact ⟨a, fun u => by simpa using congrArg (fun f : U →ₗ[F] U => f u) ha⟩

theorem eq_bot_of_three_le [Finite F] [CharP F 2] [Module.Finite F U]
    (h3 : 3 ≤ Module.finrank F U) (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)))
    (γ : B →* (U ≃ₗ[F] U))
    (hγ : ∀ (b : B) (u v : U),
      (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = γ b u ⊗ₜ[F] γ b v)
    (hfix : ∀ b ∈ B, ∀ w, b (TensorProduct.comm F U U w - w) = TensorProduct.comm F U U w - w) :
    B = ⊥ := by
  have hnt : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (M := U) (by omega)
  have hinj := gamma_injective B γ hγ
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  let b' : B := ⟨b, hb⟩
  have hD : ∀ (c : B) (u v : U),
      γ c v ⊗ₜ[F] γ c u - γ c u ⊗ₜ[F] γ c v = v ⊗ₜ[F] u - u ⊗ₜ[F] v :=
    tensor_identity_of_fix B γ hγ hfix
  have hplane : ∀ u v : U, LinearIndependent F ![u, v] →
      γ b' u ∈ Submodule.span F {u, v} ∧ γ b' v ∈ Submodule.span F {u, v} := by
    intro u v huv
    refine plane_stable (γ b') (γ b'⁻¹) ?_ (hD b'⁻¹) huv
    intro w
    rw [map_inv]
    exact gl_inv_apply_apply _ _
  have hline : ∀ u : U, ∃ c : F, γ b' u = c • u := by
    intro u
    by_cases hu : u = 0
    · exact ⟨0, by simp [hu]⟩
    · exact exists_smul_eq_of_planes (γ b') h3 hplane u hu
  obtain ⟨a, hga⟩ := eq_smul_one_of_lines (γ b') hline
  obtain ⟨u, v, huv⟩ : ∃ u v : U, LinearIndependent F ![u, v] := by
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    obtain ⟨v, hv⟩ := exists_not_mem_span_finset (F := F) ({u} : Finset U) (by simp; omega)
    exact ⟨u, v, pair_indep hu (by simpa using hv)⟩
  have h1 := hD b' u v
  simp only [hga] at h1
  rw [smul_tmul_smul', smul_tmul_smul', ← smul_sub] at h1
  have hne := tmul_sub_ne_zero huv
  have h2 : (a * a - 1) • (v ⊗ₜ[F] u - u ⊗ₜ[F] v) = 0 := by
    rw [sub_smul, one_smul, h1, sub_self]
  have h3' : a * a - 1 = 0 := (smul_eq_zero.1 h2).resolve_right hne
  have h4 : a = 1 := by
    have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
    have : (a - 1) * (a - 1) = 0 := by linear_combination h3' + (1 - a) * h2'
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have h5 : γ b' = 1 := LinearEquiv.ext fun u => by rw [hga, h4, one_smul]; rfl
  have h6 : b' = 1 := hinj (by rw [h5, map_one])
  exact congrArg Subtype.val h6


theorem det_eq_one_of_two [Module.Finite F U] (hD2 : Module.finrank F U = 2) (g : U ≃ₗ[F] U)
    (hD : ∀ u v : U, g v ⊗ₜ[F] g u - g u ⊗ₜ[F] g v = v ⊗ₜ[F] u - u ⊗ₜ[F] v) :
    LinearMap.det (g : U →ₗ[F] U) = 1 := by
  let bs : Basis (Fin 2) F U := Module.finBasisOfFinrankEq F U hD2
  let M := LinearMap.toMatrix bs bs (g : U →ₗ[F] U)
  have hdet : LinearMap.det (g : U →ₗ[F] U) = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    rw [← LinearMap.det_toMatrix bs, Matrix.det_fin_two]
  have hrepr : ∀ j, g (bs j) = M 0 j • bs 0 + M 1 j • bs 1 := by
    intro j
    have := bs.sum_repr (g (bs j))
    rw [Fin.sum_univ_two] at this
    simpa [M, LinearMap.toMatrix_apply] using this.symm
  have hli : LinearIndependent F ![bs 0, bs 1] := by
    have : (![bs 0, bs 1] : Fin 2 → U) = bs := by
      funext i; fin_cases i <;> rfl
    rw [this]; exact bs.linearIndependent
  have h1 := hD (bs 0) (bs 1)
  rw [hrepr 0, hrepr 1] at h1
  simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, smul_tmul_smul'] at h1
  have h2 : (M 0 0 * M 1 1 - M 0 1 * M 1 0 - 1) • (bs 1 ⊗ₜ[F] bs 0 - bs 0 ⊗ₜ[F] bs 1) = 0 := by
    have h3 := sub_eq_zero.2 h1
    rw [← h3]
    module
  have hne := tmul_sub_ne_zero hli
  rw [hdet]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hne)


theorem unitriangular_of_fixed [Module.Finite F U] (hD2 : Module.finrank F U = 2) {e f : U}
    (hli : LinearIndependent F ![e, f]) (g : U ≃ₗ[F] U) (hge : g e = e)
    (hdet : LinearMap.det (g : U →ₗ[F] U) = 1) : ∃ c : F, g f = c • e + f := by
  have hcard : Fintype.card (Fin 2) = Module.finrank F U := by simp [hD2]
  let bs : Basis (Fin 2) F U := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have he : bs 0 = e := by simp [bs]
  have hf : bs 1 = f := by simp [bs]
  let M := LinearMap.toMatrix bs bs (g : U →ₗ[F] U)
  have hdet' : LinearMap.det (g : U →ₗ[F] U) = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    rw [← LinearMap.det_toMatrix bs, Matrix.det_fin_two]
  have hrepr : ∀ j, g (bs j) = M 0 j • bs 0 + M 1 j • bs 1 := by
    intro j
    have := bs.sum_repr (g (bs j))
    rw [Fin.sum_univ_two] at this
    simpa [M, LinearMap.toMatrix_apply] using this.symm
  have h1 := hrepr 0
  rw [he, hf, hge] at h1
  have h2 : (M 0 0 - 1) • e + M 1 0 • f = 0 := by
    calc (M 0 0 - 1) • e + M 1 0 • f = (M 0 0 • e + M 1 0 • f) - e := by
          rw [sub_smul, one_smul]; abel
      _ = 0 := sub_eq_zero.2 h1.symm
  obtain ⟨h00, h10⟩ := LinearIndependent.pair_iff.1 hli _ _ h2
  have h00' : M 0 0 = 1 := sub_eq_zero.1 h00
  have h11 : M 1 1 = 1 := by
    rw [hdet', h00', h10] at hdet
    simpa using hdet
  have h3 := hrepr 1
  rw [he, hf, h11, one_smul] at h3
  exact ⟨M 0 1, h3⟩

theorem span_pair_eq_top [Module.Finite F U] (hD2 : Module.finrank F U = 2) {e f : U}
    (hli : LinearIndependent F ![e, f]) : Submodule.span F (Set.range ![e, f]) = ⊤ := by
  have := (basisOfLinearIndependentOfCardEqFinrank hli (by simp [hD2])).span_eq
  simpa using this

theorem exists_fixed_vector [Finite F] [CharP F 2] [Module.Finite F U] [Nontrivial U]
    (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U))) (hB : IsPGroup 2 B) (γ : B →* (U ≃ₗ[F] U)) :
    ∃ e : U, e ≠ 0 ∧ ∀ b : B, γ b e = e := by
  let _ : MulAction B U := MulAction.compHom U γ
  have hfinU : Finite U := Module.finite_of_finite F
  have h := hB.card_modEq_card_fixedPoints U
  have h2F : 2 ∣ Nat.card F := by
    let _ := Fintype.ofFinite F
    obtain ⟨n, hp, hcard⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 2 (PNat.ne_zero n)
  have hpos : 0 < Module.finrank F U := Module.finrank_pos
  have h2U : 2 ∣ Nat.card U := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    exact dvd_pow h2F hpos.ne'
  by_contra hcon
  push Not at hcon
  have hone : Nat.card (MulAction.fixedPoints B U) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨0, fun b => ?_⟩⟩⟩
    · have hx : (x : U) = 0 := by
        by_contra hx0
        obtain ⟨b, hb⟩ := hcon x hx0
        exact hb (x.2 b)
      have hy : (y : U) = 0 := by
        by_contra hy0
        obtain ⟨b, hb⟩ := hcon y hy0
        exact hb (y.2 b)
      exact Subtype.ext (hx.trans hy.symm)
    · show γ b 0 = 0
      exact map_zero _
  rw [hone] at h
  have h' : Nat.card U % 2 = 1 % 2 := h
  obtain ⟨m, hm⟩ := h2U
  omega


theorem two_group_bounds [Finite F] [CharP F 2] [Module.Finite F U]
    (hD2 : Module.finrank F U = 2) (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)))
    (hB : IsPGroup 2 B) (γ : B →* (U ≃ₗ[F] U))
    (hγ : ∀ (b : B) (u v : U),
      (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = γ b u ⊗ₜ[F] γ b v)
    (hfix : ∀ b ∈ B, ∀ w, b (TensorProduct.comm F U U w - w) = TensorProduct.comm F U U w - w) :
    Nat.card B ≤ Nat.card F ∧ (B ≠ ⊥ → Module.finrank F (fixGL B) ≤ 2) := by
  have hnt : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (M := U) (by omega)
  have hinj := gamma_injective B γ hγ
  have hD : ∀ (c : B) (u v : U),
      γ c v ⊗ₜ[F] γ c u - γ c u ⊗ₜ[F] γ c v = v ⊗ₜ[F] u - u ⊗ₜ[F] v :=
    tensor_identity_of_fix B γ hγ hfix
  have hdet : ∀ c : B, LinearMap.det (γ c : U →ₗ[F] U) = 1 := fun c =>
    det_eq_one_of_two hD2 (γ c) (hD c)
  obtain ⟨e, he0, hfixe⟩ := exists_fixed_vector B hB γ
  obtain ⟨f, hf⟩ := exists_not_mem_span_finset (F := F) ({e} : Finset U) (by simp; omega)
  have hli : LinearIndependent F ![e, f] := pair_indep he0 (by simpa using hf)
  have hup : ∀ c : B, ∃ t : F, γ c f = t • e + f := fun c =>
    unitriangular_of_fixed hD2 hli (γ c) (hfixe c) (hdet c)
  choose t ht using hup
  have hspan := span_pair_eq_top hD2 hli
  have hext : ∀ c c' : B, t c = t c' → c = c' := by
    intro c c' hcc'
    apply hinj
    have : (γ c : U →ₗ[F] U) = γ c' := by
      refine LinearMap.ext_on_range hspan (fun i => ?_)
      fin_cases i
      · simp [hfixe c, hfixe c']
      · simp [ht c, ht c', hcc']
    exact LinearEquiv.toLinearMap_injective this
  refine ⟨Nat.card_le_card_of_injective t (fun c c' h => hext c c' h), fun hne => ?_⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : B, c₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact congrArg Subtype.val (hcon ⟨x, hx⟩)
  have ht1 : t 1 = 0 := by
    have h1 := ht 1
    have h2 : f = t 1 • e + f := by simpa using h1
    have h3 : t 1 • e = 0 := by
      have := congrArg (fun x => x - f) h2
      simpa using this.symm
    exact (smul_eq_zero.1 h3).resolve_right he0
  have ht0 : t c₀ ≠ 0 := by
    intro h0
    exact hc₀ (hext c₀ 1 (by rw [h0, ht1]))
  let T0 : Module.End F (U ⊗[F] U) :=
    ((c₀ : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) : Module.End F (U ⊗[F] U)) - LinearMap.id
  have hker : fixGL B ≤ LinearMap.ker T0 := by
    intro w hw
    rw [LinearMap.mem_ker]
    show c₀.1 w - w = 0
    rw [sub_eq_zero]
    exact mem_fixGL.1 hw c₀.1 c₀.2
  have hv1 : T0 (f ⊗ₜ[F] e) = t c₀ • (e ⊗ₜ[F] e) := by
    show c₀.1 (f ⊗ₜ[F] e) - f ⊗ₜ[F] e = _
    rw [hγ, ht c₀, hfixe c₀, TensorProduct.add_tmul, ← TensorProduct.smul_tmul']
    abel
  have hv2 : T0 (f ⊗ₜ[F] f) =
      (t c₀ * t c₀) • (e ⊗ₜ[F] e) + t c₀ • (e ⊗ₜ[F] f + f ⊗ₜ[F] e) := by
    show c₀.1 (f ⊗ₜ[F] f) - f ⊗ₜ[F] f = _
    rw [hγ, ht c₀]
    simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, ← TensorProduct.smul_tmul',
      TensorProduct.tmul_smul]
    module
  have hind : LinearIndependent F ![t c₀ • (e ⊗ₜ[F] e),
      (t c₀ * t c₀) • (e ⊗ₜ[F] e) + t c₀ • (e ⊗ₜ[F] f + f ⊗ₜ[F] e)] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    obtain ⟨_, ⟨ψ, hψe, hψf⟩⟩ := exists_dual_pair hli
    have h1 := congrArg (sliceL ψ) hab
    simp only [map_add, map_smul, sliceL_tmul, hψe, hψf, one_smul, zero_smul, add_zero,
      LinearMap.map_zero] at h1
    have h2 : (a * t c₀ + b * (t c₀ * t c₀)) • e + (b * t c₀) • f = 0 := by
      rw [← h1]
      module
    obtain ⟨h3, h4⟩ := LinearIndependent.pair_iff.1 hli _ _ h2
    have hb : b = 0 := (mul_eq_zero.1 h4).resolve_right ht0
    rw [hb, zero_mul, add_zero] at h3
    exact ⟨(mul_eq_zero.1 h3).resolve_right ht0, hb⟩
  have hrank : 2 ≤ Module.finrank F (LinearMap.range T0) := by
    have hsub : Submodule.span F (Set.range ![t c₀ • (e ⊗ₜ[F] e),
        (t c₀ * t c₀) • (e ⊗ₜ[F] e) + t c₀ • (e ⊗ₜ[F] f + f ⊗ₜ[F] e)]) ≤ LinearMap.range T0 := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact ⟨f ⊗ₜ[F] e, hv1⟩
      · exact ⟨f ⊗ₜ[F] f, hv2⟩
    have := finrank_span_eq_card hind
    calc 2 = Module.finrank F (Submodule.span F (Set.range ![t c₀ • (e ⊗ₜ[F] e),
            (t c₀ * t c₀) • (e ⊗ₜ[F] e) + t c₀ • (e ⊗ₜ[F] f + f ⊗ₜ[F] e)])) := by
          simpa using this.symm
      _ ≤ Module.finrank F (LinearMap.range T0) := Submodule.finrank_mono hsub
  have hdim : Module.finrank F (LinearMap.range T0) + Module.finrank F (LinearMap.ker T0) = 4 := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_tensorProduct, hD2]
  calc Module.finrank F (fixGL B) ≤ Module.finrank F (LinearMap.ker T0) :=
        Submodule.finrank_mono hker
    _ ≤ 2 := by omega


theorem card_lt_pairs (D : ℕ) :
    (Finset.univ.filter (fun p : Fin D × Fin D => p.1 < p.2)).card * 2 = D * (D - 1) := by
  have h1 : (Finset.univ.filter (fun p : Fin D × Fin D => p.1 < p.2)).card =
      ∑ j : Fin D, (j : ℕ) := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.card_filter]
    have : Finset.univ.filter (fun i : Fin D => i < j) = Finset.Iio j := by ext; simp
    rw [this, Fin.card_Iio]
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => j) D]
  exact Finset.sum_range_id_mul_two D

theorem finrank_range_flip_sub_id [Module.Finite F U] :
    Module.finrank F (LinearMap.range
      ((TensorProduct.comm F U U : (U ⊗[F] U) →ₗ[F] (U ⊗[F] U)) - LinearMap.id)) =
        Module.finrank F U * (Module.finrank F U - 1) / 2 := by
  classical
  let b : Basis (Fin (Module.finrank F U)) F U := Module.finBasis F U
  let bb : Basis (Fin (Module.finrank F U) × Fin (Module.finrank F U)) F (U ⊗[F] U) :=
    b.tensorProduct b
  let τ1 : Module.End F (U ⊗[F] U) :=
    (TensorProduct.comm F U U : (U ⊗[F] U) →ₗ[F] (U ⊗[F] U)) - LinearMap.id
  let w : {p : Fin (Module.finrank F U) × Fin (Module.finrank F U) // p.1 < p.2} → U ⊗[F] U :=
    fun p => b p.1.2 ⊗ₜ[F] b p.1.1 - b p.1.1 ⊗ₜ[F] b p.1.2
  have hτ : ∀ i j, τ1 (b i ⊗ₜ[F] b j) = b j ⊗ₜ[F] b i - b i ⊗ₜ[F] b j := by
    intro i j; simp [τ1]
  have hrange : LinearMap.range τ1 = Submodule.span F (Set.range w) := by
    apply le_antisymm
    · rw [LinearMap.range_eq_map, ← bb.span_eq, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
      show τ1 (bb (i, j)) ∈ _
      rw [Basis.tensorProduct_apply, hτ]
      rcases lt_trichotomy i j with h | h | h
      · exact Submodule.subset_span ⟨⟨(i, j), h⟩, rfl⟩
      · rw [h, sub_self]; exact Submodule.zero_mem _
      · have : b j ⊗ₜ[F] b i - b i ⊗ₜ[F] b j = -(w ⟨(j, i), h⟩) := by
          simp [w]
        rw [this]
        exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact ⟨b p.1.1 ⊗ₜ[F] b p.1.2, hτ _ _⟩
  have hli : LinearIndependent F w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p₀
    have h1 := congrArg (fun x => bb.repr x (p₀.1.1, p₀.1.2)) hg
    have hw : ∀ p : {p : Fin (Module.finrank F U) × Fin (Module.finrank F U) // p.1 < p.2},
        bb.repr (w p) (p₀.1.1, p₀.1.2) = if p = p₀ then -1 else 0 := by
      intro p
      have e1 : b p.1.2 ⊗ₜ[F] b p.1.1 = bb (p.1.2, p.1.1) :=
        (Basis.tensorProduct_apply b b _ _).symm
      have e2 : b p.1.1 ⊗ₜ[F] b p.1.2 = bb (p.1.1, p.1.2) :=
        (Basis.tensorProduct_apply b b _ _).symm
      show bb.repr (b p.1.2 ⊗ₜ[F] b p.1.1 - b p.1.1 ⊗ₜ[F] b p.1.2) _ = _
      rw [e1, e2, map_sub, Basis.repr_self, Basis.repr_self, Finsupp.sub_apply,
        Finsupp.single_apply, Finsupp.single_apply]
      by_cases hp : p = p₀
      · subst hp
        have : (p.1.2, p.1.1) ≠ (p.1.1, p.1.2) := fun h => by
          have := congrArg Prod.fst h
          exact absurd this (ne_of_gt p.2)
        simp [this]
      · have hne : (p.1.1, p.1.2) ≠ (p₀.1.1, p₀.1.2) := fun h =>
          hp (Subtype.ext (Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)))
        have hne' : (p.1.2, p.1.1) ≠ (p₀.1.1, p₀.1.2) := fun h => by
          have h1 : p.1.2 = p₀.1.1 := congrArg Prod.fst h
          have h2 : p.1.1 = p₀.1.2 := congrArg Prod.snd h
          have hp1 : p.1.1 < p.1.2 := p.2
          have hp2 : p₀.1.1 < p₀.1.2 := p₀.2
          rw [← h1, ← h2] at hp2
          exact lt_asymm hp1 hp2
        simp [hne, hne', hp]
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, hw, mul_ite, mul_neg, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
    exact neg_eq_zero.1 h1
  show Module.finrank F (LinearMap.range τ1) = _
  rw [hrange, finrank_span_eq_card hli, Fintype.card_subtype]
  exact (Nat.div_eq_of_eq_mul_left (by norm_num) (card_lt_pairs _).symm).symm ▸ rfl


theorem quadratic_tensor_flip_factor_kernel [Finite F] [CharP F 2] [Module.Finite F U]
    (hD : 2 ≤ Module.finrank F U) (B : Subgroup ((U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)))
    (hform : ∀ b ∈ B, ∃ x y : U ≃ₗ[F] U, ∀ u v, b (u ⊗ₜ[F] v) = x u ⊗ₜ[F] y v)
    (hcomm : ∀ b ∈ B, ∀ w, b (TensorProduct.comm F U U w) = TensorProduct.comm F U U (b w))
    (hfix : ∀ b ∈ B, ∀ w, b (TensorProduct.comm F U U w - w) = TensorProduct.comm F U U w - w) :
    ∃ γ : B →* (U ≃ₗ[F] U),
      (∀ (b : B) (u v : U),
        (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = γ b u ⊗ₜ[F] γ b v) ∧
      (∀ (b : B) (g : U ≃ₗ[F] U),
        (∀ u v : U, (b : (U ⊗[F] U) ≃ₗ[F] (U ⊗[F] U)) (u ⊗ₜ[F] v) = g u ⊗ₜ[F] g v) → g = γ b) ∧
      Function.Injective γ ∧
      (3 ≤ Module.finrank F U → B = ⊥) ∧
      (Module.finrank F U = 2 → ∀ b : B, LinearMap.det (γ b : U →ₗ[F] U) = 1) ∧
      (Module.finrank F U = 2 → IsPGroup 2 B →
        Nat.card B ≤ Nat.card F ∧ (B ≠ ⊥ → Module.finrank F (fixGL B) ≤ 2)) ∧
      Module.finrank F (LinearMap.range
        ((TensorProduct.comm F U U : (U ⊗[F] U) →ₗ[F] (U ⊗[F] U)) - LinearMap.id)) =
          Module.finrank F U * (Module.finrank F U - 1) / 2 := by
  have hnt : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (M := U) (by omega)
  obtain ⟨γ, hγ⟩ := exists_gamma B hform hcomm
  refine ⟨γ, hγ, fun b g hg => eq_of_tensor_square_eq g (γ b) (fun u v => by
      rw [← hg u v, hγ b u v]), gamma_injective B γ hγ,
    fun h3 => eq_bot_of_three_le h3 B γ hγ hfix,
    fun hD2 b => det_eq_one_of_two hD2 (γ b) (tensor_identity_of_fix B γ hγ hfix b),
    fun hD2 hB => two_group_bounds hD2 B hB γ hγ hfix, finrank_range_flip_sub_id⟩

end Flip

end CFSG.QuasithinUnique.Setup.Offender
