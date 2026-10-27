module

public import CFSG.LocalAnalysis.AGLEmbedding.TrialityTwo.SevenFixed

public section

namespace CFSG.AGLEmbedding.TrialityTwo.Seven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {t : Module.End K V}

@[expose] def fixedSet (Q : QuadraticForm K V) (t : Module.End K V) : Set (Submodule K V) :=
  {W | ((finrank K W = 1 ∧ ∀ v ∈ W, Q v = 0) ∨ (finrank K W = 4 ∧ ∀ v ∈ W, Q v = 0)) ∧
    W.map t = W}

theorem apply_eq_of_map_span_eq (hK : Nat.card K = 2) (σ : V ≃ₗ[K] V) {w : V} (hw : w ≠ 0)
    (h : (Submodule.span K {w}).map (σ : V →ₗ[K] V) = Submodule.span K {w}) : σ w = w := by
  have hmem : σ w ∈ Submodule.span K {w} :=
    h ▸ Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  rcases eq_zero_or_eq_one_of_card hK c with rfl | rfl
  · rw [zero_smul, eq_comm, LinearEquiv.map_eq_zero_iff] at hc
    exact absurd hc hw
  · rw [← hc, one_smul]

section Stab

variable (h7 : t ^ 7 = 1) (h2 : (2 : K) = 0) (hQt : ∀ v, Q (t v) = Q v) (F : Frame Q t)
include h7 h2 hQt

omit hQt in
theorem sup_inf_sup_spU₁ :
    (spU₁ t ⊔ Submodule.span K {F.w₁}) ⊓ (spU₁ t ⊔ Submodule.span K {F.w₂}) = spU₁ t := by
  apply le_antisymm
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hx₁
    obtain ⟨u', hu', y', hy', he⟩ := Submodule.mem_sup.1 hx₂
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    have hP := congrArg (projC t) he
    simp only [map_add, map_smul, projC_apply_of_mem_spU₁ h7 h2 hu,
      projC_apply_of_mem_spU₁ h7 h2 hu', projC_apply_of_mem_fixC h7 h2 F.mem_C₁,
      projC_apply_of_mem_fixC h7 h2 F.mem_C₂, zero_add] at hP
    have hpol := congrArg (fun z => polar Q z F.w₂) hP
    simp only [polar_smul_left_eq, F.polar_w, polar_self_eq_zero (F.Q_b _), mul_zero,
      mul_one] at hpol
    rw [← hpol, zero_smul, add_zero]
    exact hu
  · exact le_inf le_sup_left le_sup_left

omit hQt in
theorem sup_inf_sup_spU₂ :
    (spU₂ t ⊔ Submodule.span K {F.w₁}) ⊓ (spU₂ t ⊔ Submodule.span K {F.w₂}) = spU₂ t := by
  apply le_antisymm
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hx₁
    obtain ⟨u', hu', y', hy', he⟩ := Submodule.mem_sup.1 hx₂
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy'
    have hP := congrArg (projC t) he
    simp only [map_add, map_smul, projC_apply_of_mem_spU₂ h7 h2 hu,
      projC_apply_of_mem_spU₂ h7 h2 hu', projC_apply_of_mem_fixC h7 h2 F.mem_C₁,
      projC_apply_of_mem_fixC h7 h2 F.mem_C₂, zero_add] at hP
    have hpol := congrArg (fun z => polar Q z F.w₂) hP
    simp only [polar_smul_left_eq, F.polar_w, polar_self_eq_zero (F.Q_b _), mul_zero,
      mul_one] at hpol
    rw [← hpol, zero_smul, add_zero]
    exact hu
  · exact le_inf le_sup_left le_sup_left

omit h7 h2 hQt in
theorem span_mem_fixedSet {w : V} (hw : w ∈ fixC t) (hQw : Q w = 0) (hw0 : w ≠ 0) :
    Submodule.span K {w} ∈ fixedSet Q t := by
  refine ⟨.inl ⟨finrank_span_singleton hw0, fun v hv => ?_⟩, map_span_of_mem_fixC hw⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  rw [map_smul_eq_sq, hQw, mul_zero]

theorem sup_spU₁_mem_fixedSet [FiniteDimensional K V] (hd : finrank K (spU₁ t) = 3) {w : V}
    (hw : w ∈ fixC t) (hQw : Q w = 0) (hw0 : w ≠ 0) :
    spU₁ t ⊔ Submodule.span K {w} ∈ fixedSet Q t := by
  refine ⟨.inr ⟨?_, fun v hv => ?_⟩, ?_⟩
  · have hinf : spU₁ t ⊓ Submodule.span K {w} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx₁, hx₂⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
      exact (Submodule.mem_bot K).2
        (eq_zero_of_mem_spU₁_of_mem_fixC h7 h2 hx₁ (Submodule.smul_mem _ _ hw))
    have e := Submodule.finrank_sup_add_finrank_inf_eq (spU₁ t) (Submodule.span K {w})
    rw [hinf, finrank_bot, add_zero, hd, finrank_span_singleton hw0] at e
    exact e
  · obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [QuadraticMap.map_add (⇑Q), map_eq_zero_of_mem_spU₁ hQt h7 h2 hu, map_smul_eq_sq, hQw,
      polar_comm, polar_eq_zero_of_mem_fixC_of_mem_spU₁ hQt h7 h2 (Submodule.smul_mem _ _ hw) hu]
    ring
  · rw [Submodule.map_sup, map_spU₁ h7, map_span_of_mem_fixC hw]

theorem sup_spU₂_mem_fixedSet [FiniteDimensional K V] (hd : finrank K (spU₂ t) = 3) {w : V}
    (hw : w ∈ fixC t) (hQw : Q w = 0) (hw0 : w ≠ 0) :
    spU₂ t ⊔ Submodule.span K {w} ∈ fixedSet Q t := by
  refine ⟨.inr ⟨?_, fun v hv => ?_⟩, ?_⟩
  · have hinf : spU₂ t ⊓ Submodule.span K {w} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx₁, hx₂⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
      exact (Submodule.mem_bot K).2
        (eq_zero_of_mem_spU₂_of_mem_fixC h7 h2 hx₁ (Submodule.smul_mem _ _ hw))
    have e := Submodule.finrank_sup_add_finrank_inf_eq (spU₂ t) (Submodule.span K {w})
    rw [hinf, finrank_bot, add_zero, hd, finrank_span_singleton hw0] at e
    exact e
  · obtain ⟨u, hu, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [QuadraticMap.map_add (⇑Q), map_eq_zero_of_mem_spU₂ hQt h7 h2 hu, map_smul_eq_sq, hQw,
      polar_comm, polar_eq_zero_of_mem_fixC_of_mem_spU₂ hQt h7 h2 (Submodule.smul_mem _ _ hw) hu]
    ring
  · rw [Submodule.map_sup, map_spU₂ h7, map_span_of_mem_fixC hw]

end Stab

section Iff

variable [FiniteDimensional K V] (hK : Nat.card K = 2) (h7 : t ^ 7 = 1) (ht : t ≠ 1)
  (hQt : ∀ v, Q (t v) = Q v) (hB : (polarBilin Q).Nondegenerate) (hV : finrank K V = 8)
  (F : Frame Q t)
include hK h7 ht hQt hB hV

theorem forall_map_eq_iff (σ : V ≃ₗ[K] V) :
    (∀ W ∈ fixedSet Q t, W.map (σ : V →ₗ[K] V) = W) ↔
      σ F.w₁ = F.w₁ ∧ σ F.w₂ = F.w₂ ∧ (spU₁ t).map (σ : V →ₗ[K] V) = spU₁ t ∧
        (spU₂ t).map (σ : V →ₗ[K] V) = spU₂ t := by
  have h2 := two_eq_zero_of_card hK
  have hd₁ := finrank_spU₁_eq_three hK h7 ht hQt hB hV
  have hd₂ := finrank_spU₂_eq_three hK h7 ht hQt hB hV
  have m₁ := span_mem_fixedSet (Q := Q) F.mem_C₁ (F.Q_b _) F.w₁_ne_zero
  have m₂ := span_mem_fixedSet (Q := Q) F.mem_C₂ (F.Q_b _) F.w₂_ne_zero
  have m₁₁ := sup_spU₁_mem_fixedSet h7 h2 hQt hd₁ F.mem_C₁ (F.Q_b _) F.w₁_ne_zero
  have m₁₂ := sup_spU₁_mem_fixedSet h7 h2 hQt hd₁ F.mem_C₂ (F.Q_b _) F.w₂_ne_zero
  have m₂₁ := sup_spU₂_mem_fixedSet h7 h2 hQt hd₂ F.mem_C₁ (F.Q_b _) F.w₁_ne_zero
  have m₂₂ := sup_spU₂_mem_fixedSet h7 h2 hQt hd₂ F.mem_C₂ (F.Q_b _) F.w₂_ne_zero
  have hinj : Function.Injective (σ : V →ₗ[K] V) := σ.injective
  constructor
  · intro h
    refine ⟨apply_eq_of_map_span_eq hK σ F.w₁_ne_zero (h _ m₁),
      apply_eq_of_map_span_eq hK σ F.w₂_ne_zero (h _ m₂), ?_, ?_⟩
    · rw [← sup_inf_sup_spU₁ h7 h2 F, Submodule.map_inf _ hinj, h _ m₁₁, h _ m₁₂]
    · rw [← sup_inf_sup_spU₂ h7 h2 F, Submodule.map_inf _ hinj, h _ m₂₁, h _ m₂₂]
  · rintro ⟨e₁, e₂, hU₁, hU₂⟩ W ⟨hW, hWt⟩
    have hs₁ : (Submodule.span K {F.w₁}).map (σ : V →ₗ[K] V) = Submodule.span K {F.w₁} := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, e₁]
    have hs₂ : (Submodule.span K {F.w₂}).map (σ : V →ₗ[K] V) = Submodule.span K {F.w₂} := by
      rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, e₂]
    rcases hW with ⟨h1, hs⟩ | ⟨h4, hs⟩
    · rcases eq_span_of_fixed_point hK h7 ht hQt hB hV F h1 hs hWt with rfl | rfl
      · exact hs₁
      · exact hs₂
    · rcases eq_of_fixed_solid hK h7 ht hQt hB hV F h4 hs hWt with rfl | rfl | rfl | rfl <;>
        rw [Submodule.map_sup] <;> simp only [hU₁, hU₂, hs₁, hs₂]

end Iff

end CFSG.AGLEmbedding.TrialityTwo.Seven
