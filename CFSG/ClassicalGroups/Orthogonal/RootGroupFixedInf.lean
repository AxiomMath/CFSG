module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_polar_eq_zero_not_mem_span [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 2 < finrank K V) {u : V} (hu : u ≠ 0) :
    ∃ w, polar Q u w = 0 ∧ w ∉ K ∙ u := by
  set f : V →ₗ[K] K := polarBilin Q u with hf
  have hfw : ∀ w, f w = polar Q u w := fun w => rfl
  have hf0 : f ≠ 0 := by
    intro h0
    exact hu (hQ.1 u fun w => by simpa [hf] using LinearMap.congr_fun h0 w)
  have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
  by_contra hcon
  push Not at hcon
  have hle : LinearMap.ker f ≤ K ∙ u := fun w hw => hcon w (by rw [← hfw]; exact hw)
  have h1 : finrank K (LinearMap.ker f) ≤ finrank K (K ∙ u) := Submodule.finrank_mono hle
  rw [finrank_span_singleton hu] at h1
  omega

theorem Lom_ne_bot [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 2 < finrank K V) {u : V} (hu : Q u = 0) (hu0 : u ≠ 0) : Lom Q u ≠ ⊥ := by
  obtain ⟨w, hw, hwu⟩ := exists_polar_eq_zero_not_mem_span hQ h3 hu0
  obtain ⟨x, hx⟩ : ∃ x, polar Q x u ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (hQ.2 u h)
  intro hbot
  have hmem : Eom Q u w ∈ Lom Q u := Eom_mem_Lom hw
  rw [hbot, Subgroup.mem_bot] at hmem
  have h1 := congrArg (fun g : Gom Q => g.app x) hmem
  simp only [Gom.app_one] at h1
  rw [Eom_app hu hw x] at h1
  apply hwu
  have h2 : polar Q x u • w = (polar Q x w + Q w * polar Q x u) • u := by
    have h3' : polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u = 0 := by
      have := h1
      rw [add_sub_assoc] at this
      simpa using this
    exact sub_eq_zero.mp h3'
  have h4 : w = ((polar Q x u)⁻¹ * (polar Q x w + Q w * polar Q x u)) • u := by
    rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ hx, one_smul]
  rw [h4]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

theorem Lom_inf_ne_bot_of_polar_eq_zero [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 2 < finrank K V) {u u' : V} (hu : Q u = 0)
    (hu' : Q u' = 0) (hu0 : u ≠ 0) (hu'0 : u' ≠ 0) (h : polar Q u u' = 0) :
    Lom Q u ⊓ Lom Q u' ≠ ⊥ := by
  by_cases hmul : ∃ s : K, s ≠ 0 ∧ u' = s • u
  · obtain ⟨s, hs, rfl⟩ := hmul
    rw [Lom_smul hs, inf_idem]
    exact Lom_ne_bot hQ h3 hu hu0
  · push Not at hmul
    have h' : polar Q u' u = 0 := by rw [polar_comm]; exact h
    have hV : ∀ v : V, v + v = 0 := fun v => by
      rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
    have hsw : Eom Q u u' = Eom Q u' u := by
      refine Gom.ext' fun x => ?_
      rw [Eom_app hu h, Eom_app hu' h', hu', hu]
      simp only [zero_mul, zero_smul, add_zero, sub_zero]
      rw [sub_eq_add_of_exp2 hV, sub_eq_add_of_exp2 hV]
      abel
    have hg1 : Eom Q u u' ∈ Lom Q u := Eom_mem_Lom h
    have hg2 : Eom Q u u' ∈ Lom Q u' := by
      rw [hsw]
      exact Eom_mem_Lom h'
    intro hbot
    have hg3 : Eom Q u u' ∈ Lom Q u ⊓ Lom Q u' := ⟨hg1, hg2⟩
    rw [hbot, Subgroup.mem_bot] at hg3
    have hy : ∀ y : V, polar Q y u • u' + polar Q y u' • u = 0 := by
      intro y
      have h1 := congrArg (fun g : Gom Q => g.app y) hg3
      simp only [Gom.app_one] at h1
      rw [Eom_app hu h y, hu'] at h1
      simp only [zero_mul, zero_smul, add_zero, sub_zero] at h1
      rw [sub_eq_add_of_exp2 hV, add_assoc] at h1
      simpa using h1
    refine hu0 (hQ.2 u fun y => ?_)
    by_contra hne0
    have hne : polar Q y u ≠ 0 := hne0
    apply hmul (-(polar Q y u' / polar Q y u)) (by
      intro h0
      have h5 : polar Q y u' = 0 := by
        have := neg_eq_zero.mp h0
        rw [div_eq_zero_iff] at this
        exact this.resolve_right hne
      have h6 := hy y
      rw [h5, zero_smul, add_zero] at h6
      exact hu'0 ((smul_eq_zero.mp h6).resolve_left hne))
    have h6 := hy y
    have h7 : polar Q y u • u' = -(polar Q y u' • u) := eq_neg_of_add_eq_zero_left h6
    calc u' = (polar Q y u)⁻¹ • (polar Q y u • u') := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (polar Q y u)⁻¹ • (-(polar Q y u' • u)) := by rw [h7]
      _ = -(polar Q y u' / polar Q y u) • u := by
          rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem Lom_inf_eq_bot_iff [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 2 < finrank K V) {u u' : V} (hu : Q u = 0)
    (hu' : Q u' = 0) (hu0 : u ≠ 0) (hu'0 : u' ≠ 0) :
    Lom Q u ⊓ Lom Q u' = ⊥ ↔ polar Q u u' ≠ 0 := by
  constructor
  · intro h hzero
    exact Lom_inf_ne_bot_of_polar_eq_zero hQ h3 hu hu' hu0 hu'0 hzero h
  · intro h
    rw [eq_bot_iff]
    rintro g ⟨hg1, hg2⟩
    have hinf : (g : V ≃ₗ[K] V) ∈ rootGroup Q u ⊓ rootGroup Q u' := ⟨hg1, hg2⟩
    rw [rootGroup_inf_eq_bot hu h, Subgroup.mem_bot] at hinf
    exact Subgroup.mem_bot.mpr (Subtype.ext hinf)

end CFSG.ClassicalGroups.Orthogonal
