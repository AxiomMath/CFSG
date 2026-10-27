module

public import CFSG.LargeExtraspecial.OrthoF2PairsCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S12I4M

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

set_option synthInstance.maxSize 2048 in
theorem zmod2_pair_solve : ∀ a b c d x y : ZMod 2, ¬ (a = 0 ∧ b = 0) → ¬ (c = 0 ∧ d = 0) →
    ¬ (c = a ∧ d = b) → a * x + b * y = 0 → c * x + d * y = 1 → x = b ∧ y = a := by
  decide

theorem sub_eq_of_polar (hq : q.polarBilin.Nondegenerate) {α : V ≃ₗ[ZMod 2] V}
    (hα : IsTypeA q α 2) {c w v : V} (hc : c ∈ commSpace α) (hw : w ∈ commSpace α) (hc0 : c ≠ 0)
    (hw0 : w ≠ 0) (hwc : w ≠ c) (hvc : polar q v c = 0) (hvw : polar q v w = 1) :
    α v - v = c := by
  obtain ⟨a1, a2, -, hspan, -, -, -, hE⟩ := exists_sub_apply_of_isTypeA hq hα
  rw [hspan] at hc hw
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hc
  obtain ⟨u, r, rfl⟩ := Submodule.mem_span_pair.mp hw
  rw [polar_add_right, polar_smul_right, polar_smul_right, smul_eq_mul, smul_eq_mul] at hvc hvw
  have h1 : ¬ (s = 0 ∧ t = 0) := fun h => hc0 (by rw [h.1, h.2, zero_smul, zero_smul, add_zero])
  have h2 : ¬ (u = 0 ∧ r = 0) := fun h => hw0 (by rw [h.1, h.2, zero_smul, zero_smul, add_zero])
  have h3 : ¬ (u = s ∧ r = t) := fun h => hwc (by rw [h.1, h.2])
  obtain ⟨hx, hy⟩ := zmod2_pair_solve s t u r _ _ h1 h2 h3 hvc hvw
  rw [hE, hx, hy, add_comm]

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_eq_of_polar (hq : q.polarBilin.Nondegenerate) {α : V ≃ₗ[ZMod 2] V} {l : ℕ}
    (hα : IsTypeA q α l) {v : V} (hv : ∀ x ∈ commSpace α, polar q v x = 0) : α v = v :=
  (mem_orthogonal_commSpace_iff hq (mem_orthogonalGroup_of_isTypeA hα)).mp
    (LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => by
      rw [polarBilin_apply_apply, polar_comm]
      exact hv x hx)

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_eq_zero_of_isTypeA {α : V ≃ₗ[ZMod 2] V} {l : ℕ} (hα : IsTypeA q α l) {x y : V}
    (hx : x ∈ commSpace α) (hy : y ∈ commSpace α) : polar q x y = 0 := by
  rw [polar, hα.2.2.2.2 _ ((commSpace α).add_mem hx hy), hα.2.2.2.2 x hx, hα.2.2.2.2 y hy,
    sub_zero, sub_zero]

theorem span_pair_eq {U : Submodule (ZMod 2) V} (hU : finrank (ZMod 2) U = 2) {x y : V}
    (hx : x ∈ U) (hy : y ∈ U) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxy : x ≠ y) :
    Submodule.span (ZMod 2) {x, y} = U := by
  have hli := linearIndependent_pair_iff.mpr ⟨hx0, hy0, hxy⟩
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_span_pair hli, hU])
  rw [Submodule.span_le]
  rintro z (rfl | rfl)
  · exact hx
  · exact hy

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_eq_zero_of_mem_span_pair {v x y z : V} (hx : polar q v x = 0)
    (hy : polar q v y = 0) (hz : z ∈ Submodule.span (ZMod 2) {x, y}) : polar q v z = 0 := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [polar_add_right, polar_smul_right, polar_smul_right, hx, hy, smul_zero, smul_zero,
    add_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_eq_zero_of_mem_sup {v z : V} {U W : Submodule (ZMod 2) V}
    (hU : ∀ x ∈ U, polar q v x = 0) (hW : ∀ x ∈ W, polar q v x = 0) (hz : z ∈ U ⊔ W) :
    polar q v z = 0 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
  rw [polar_add_right, hU x hx, hW y hy, add_zero]

theorem exists_polar_ne_zero (hq : q.polarBilin.Nondegenerate) {U₁ U₂ : Submodule (ZMod 2) V}
    (h : finrank (ZMod 2) U₁ < finrank (ZMod 2) U₂) :
    ∃ v : V, (∀ x ∈ U₁, polar q v x = 0) ∧ ∃ u ∈ U₂, polar q v u ≠ 0 := by
  have h1 := LinearMap.BilinForm.finrank_orthogonal hq U₁
  have h2 := LinearMap.BilinForm.finrank_orthogonal hq U₂
  have hle1 := Submodule.finrank_le U₁
  have hle2 := Submodule.finrank_le U₂
  have hnot : ¬ LinearMap.BilinForm.orthogonal q.polarBilin U₁ ≤
      LinearMap.BilinForm.orthogonal q.polarBilin U₂ := fun hle => by
    have := Submodule.finrank_mono hle
    omega
  obtain ⟨v, hv1, hv2⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  refine ⟨v, fun x hx => ?_, ?_⟩
  · have := (LinearMap.BilinForm.mem_orthogonal_iff.mp hv1) x hx
    rwa [polarBilin_apply_apply, polar_comm] at this
  · by_contra hc
    push Not at hc
    exact hv2 (LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu => by
      rw [polarBilin_apply_apply, polar_comm]
      exact hc u hu)

theorem finrank_le_four_of_isotropic (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {U : Submodule (ZMod 2) V}
    (hU : ∀ x ∈ U, ∀ y ∈ U, polar q x y = 0) : finrank (ZMod 2) U ≤ 4 := by
  have hle : U ≤ LinearMap.BilinForm.orthogonal q.polarBilin U := fun y hy =>
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => by
      rw [polarBilin_apply_apply]
      exact hU x hx y hy
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hq, hV] at h1
  omega

theorem finrank_sup_of_disjoint {ℓ₄ ℓ₅ : Submodule (ZMod 2) V} (h4 : finrank (ZMod 2) ℓ₄ = 2)
    (h5 : finrank (ZMod 2) ℓ₅ = 2) (hd : ℓ₄ ⊓ ℓ₅ = ⊥) : finrank (ZMod 2) (ℓ₄ ⊔ ℓ₅ :
      Submodule (ZMod 2) V) = 4 := by
  have := Submodule.finrank_sup_add_finrank_inf_eq ℓ₄ ℓ₅
  rw [hd, finrank_bot, h4, h5] at this
  omega

theorem le_sup_of_isotropic (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {ℓ ℓ₄ ℓ₅ : Submodule (ZMod 2) V} (h4 : finrank (ZMod 2) ℓ₄ = 2)
    (h5 : finrank (ZMod 2) ℓ₅ = 2) (hd : ℓ₄ ⊓ ℓ₅ = ⊥)
    (hi : ∀ x ∈ ℓ, ∀ y ∈ ℓ, polar q x y = 0) (hi4 : ∀ x ∈ ℓ₄, ∀ y ∈ ℓ₄, polar q x y = 0)
    (hi5 : ∀ x ∈ ℓ₅, ∀ y ∈ ℓ₅, polar q x y = 0) (h04 : ∀ x ∈ ℓ, ∀ y ∈ ℓ₄, polar q x y = 0)
    (h05 : ∀ x ∈ ℓ, ∀ y ∈ ℓ₅, polar q x y = 0) (h45 : ∀ x ∈ ℓ₄, ∀ y ∈ ℓ₅, polar q x y = 0) :
    ℓ ≤ ℓ₄ ⊔ ℓ₅ := by
  have hiso : ∀ x ∈ ℓ ⊔ (ℓ₄ ⊔ ℓ₅), ∀ y ∈ ℓ ⊔ (ℓ₄ ⊔ ℓ₅), polar q x y = 0 := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, x', hx', rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨x₄, hx₄, x₅, hx₅, rfl⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨y₀, hy₀, y', hy', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨y₄, hy₄, y₅, hy₅, rfl⟩ := Submodule.mem_sup.mp hy'
    simp only [polar_add_left, polar_add_right]
    rw [hi x₀ hx₀ y₀ hy₀, h04 x₀ hx₀ y₄ hy₄, h05 x₀ hx₀ y₅ hy₅, polar_comm q x₄ y₀,
      h04 y₀ hy₀ x₄ hx₄, hi4 x₄ hx₄ y₄ hy₄, h45 x₄ hx₄ y₅ hy₅, polar_comm q x₅ y₀,
      h05 y₀ hy₀ x₅ hx₅, polar_comm q x₅ y₄, h45 y₄ hy₄ x₅ hx₅, hi5 x₅ hx₅ y₅ hy₅]
    simp
  have hle := finrank_le_four_of_isotropic hq hV hiso
  have heq : ℓ₄ ⊔ ℓ₅ = ℓ ⊔ (ℓ₄ ⊔ ℓ₅) :=
    Submodule.eq_of_le_of_finrank_le le_sup_right
      (by rw [finrank_sup_of_disjoint h4 h5 hd]; exact hle)
  rw [heq]
  exact le_sup_left

omit [FiniteDimensional (ZMod 2) V] in
theorem finrank_span_singleton_le (v : V) : finrank (ZMod 2) (ZMod 2 ∙ v) ≤ 1 := by
  by_cases hv : v = 0
  · rw [hv, Submodule.span_zero_singleton, finrank_bot]
    omega
  · rw [finrank_span_singleton hv]

section TwoLines

variable (hq : q.polarBilin.Nondegenerate) {α₄ α₅ : V ≃ₗ[ZMod 2] V} (h4 : IsTypeA q α₄ 2)
  (h5 : IsTypeA q α₅ 2) (hd : commSpace α₄ ⊓ commSpace α₅ = ⊥)
  (h45 : ∀ x ∈ commSpace α₄, ∀ y ∈ commSpace α₅, polar q x y = 0) {a₄ c₄ a₅ c₅ : V}
  (ha₄ : a₄ ∈ commSpace α₄) (hc₄ : c₄ ∈ commSpace α₄) (ha₅ : a₅ ∈ commSpace α₅)
  (hc₅ : c₅ ∈ commSpace α₅) (ha₄0 : a₄ ≠ 0) (hc₄0 : c₄ ≠ 0) (ha₅0 : a₅ ≠ 0) (hc₅0 : c₅ ≠ 0)
  (hac₄ : a₄ ≠ c₄) (hac₅ : a₅ ≠ c₅)
include hq h4 h5 hd h45 ha₄ hc₄ ha₅ hc₅ ha₄0 hc₄0 ha₅0 hc₅0 hac₄ hac₅

theorem exists_sub_eq_add :
    ∃ v : V, polar q v (a₄ + a₅) = 0 ∧ α₄ (α₅ v) - v = c₄ + c₅ := by
  have hspan4 := span_pair_eq h4.2.2.2.1 hc₄ ha₄ hc₄0 ha₄0 (Ne.symm hac₄)
  have hspan5 := span_pair_eq h5.2.2.2.1 hc₅ ha₅ hc₅0 ha₅0 (Ne.symm hac₅)
  have hU : finrank (ZMod 2) ((ZMod 2 ∙ c₄) ⊔ (ZMod 2 ∙ c₅) ⊔ (ZMod 2 ∙ (a₄ + a₅)) :
      Submodule (ZMod 2) V) < finrank (ZMod 2) (commSpace α₄ ⊔ commSpace α₅ :
        Submodule (ZMod 2) V) := by
    rw [finrank_sup_of_disjoint h4.2.2.2.1 h5.2.2.2.1 hd]
    have e1 := Submodule.finrank_add_le_finrank_add_finrank ((ZMod 2 ∙ c₄) ⊔ (ZMod 2 ∙ c₅))
      (ZMod 2 ∙ (a₄ + a₅))
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (ZMod 2 ∙ c₄) (ZMod 2 ∙ c₅)
    have e3 := finrank_span_singleton_le c₄
    have e4 := finrank_span_singleton_le c₅
    have e5 := finrank_span_singleton_le (a₄ + a₅)
    omega
  obtain ⟨v, hv1, u, hu, hvu⟩ := exists_polar_ne_zero hq hU
  have hvc₄ : polar q v c₄ = 0 := hv1 c₄
    (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self c₄)))
  have hvc₅ : polar q v c₅ = 0 := hv1 c₅
    (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self c₅)))
  have hva : polar q v (a₄ + a₅) = 0 :=
    hv1 _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hva₄ : polar q v a₄ = 1 := by
    by_contra h
    have h0 : polar q v a₄ = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right h
    have h0' : polar q v a₅ = 0 := by
      rw [polar_add_right, h0, zero_add] at hva
      exact hva
    apply hvu
    refine polar_eq_zero_of_mem_sup (fun x hx => ?_) (fun x hx => ?_) hu
    · rw [← hspan4] at hx
      exact polar_eq_zero_of_mem_span_pair hvc₄ h0 hx
    · rw [← hspan5] at hx
      exact polar_eq_zero_of_mem_span_pair hvc₅ h0' hx
  have hva₅ : polar q v a₅ = 1 := by
    rw [polar_add_right, hva₄] at hva
    exact (zmod2_eq_of_add_eq_zero hva).symm
  have e5 : α₅ v - v = c₅ := sub_eq_of_polar hq h5 hc₅ ha₅ hc₅0 ha₅0 hac₅ hvc₅ hva₅
  have e4 : α₄ v - v = c₄ := sub_eq_of_polar hq h4 hc₄ ha₄ hc₄0 ha₄0 hac₄ hvc₄ hva₄
  have hfix : α₄ c₅ = c₅ := apply_eq_of_polar hq h4 fun x hx => by
    rw [polar_comm]
    exact h45 x hx c₅ hc₅
  refine ⟨v, hva, ?_⟩
  have e5' : α₅ v = v + c₅ := by rw [← e5]; abel
  rw [e5', map_add, hfix, show α₄ v + c₅ - v = (α₄ v - v) + c₅ by abel, e4]

omit h45 hc₅ ha₅0 hc₅0 hac₅ in
theorem exists_sub_eq_left : ∃ v : V, polar q v (a₄ + a₅) = 0 ∧ α₄ (α₅ v) - v = a₄ := by
  have hspan4 := span_pair_eq h4.2.2.2.1 hc₄ ha₄ hc₄0 ha₄0 (Ne.symm hac₄)
  have hU : finrank (ZMod 2) ((ZMod 2 ∙ a₄) ⊔ commSpace α₅ : Submodule (ZMod 2) V) <
      finrank (ZMod 2) (commSpace α₄ ⊔ commSpace α₅ : Submodule (ZMod 2) V) := by
    rw [finrank_sup_of_disjoint h4.2.2.2.1 h5.2.2.2.1 hd]
    have e1 := Submodule.finrank_add_le_finrank_add_finrank (ZMod 2 ∙ a₄) (commSpace α₅)
    have e3 := finrank_span_singleton_le a₄
    rw [h5.2.2.2.1] at e1
    omega
  obtain ⟨v, hv1, u, hu, hvu⟩ := exists_polar_ne_zero hq hU
  have hva₄ : polar q v a₄ = 0 :=
    hv1 a₄ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a₄))
  have hv5 : ∀ x ∈ commSpace α₅, polar q v x = 0 := fun x hx =>
    hv1 x (Submodule.mem_sup_right hx)
  have hvc₄ : polar q v c₄ = 1 := by
    by_contra h
    have h0 : polar q v c₄ = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right h
    apply hvu
    refine polar_eq_zero_of_mem_sup (fun x hx => ?_) hv5 hu
    rw [← hspan4] at hx
    exact polar_eq_zero_of_mem_span_pair h0 hva₄ hx
  have e4 : α₄ v - v = a₄ := sub_eq_of_polar hq h4 ha₄ hc₄ ha₄0 hc₄0 (Ne.symm hac₄) hva₄ hvc₄
  refine ⟨v, by rw [polar_add_right, hva₄, hv5 a₅ ha₅, add_zero], ?_⟩
  rw [apply_eq_of_polar hq h5 hv5, e4]

end TwoLines

end CFSG.LargeExtraspecial.S12I4M
