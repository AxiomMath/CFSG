module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero_zmod2 (x : V) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem neg_eq_self_zmod2 (x : V) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero_zmod2 x)

theorem eq_zero_or_eq_of_mem_span_singleton {c v : V} (h : v ∈ (ZMod 2) ∙ c) :
    v = 0 ∨ v = c := by
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp h
  rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
  · left
    exact zero_smul _ c
  · right
    exact one_smul _ c

theorem not_mem_span_singleton_of_ne {c v : V} (hv : v ≠ 0) (hvc : v ≠ c) :
    v ∉ (ZMod 2) ∙ c := by
  intro h
  rcases eq_zero_or_eq_of_mem_span_singleton h with h | h
  · exact hv h
  · exact hvc h

variable {Γ : Type*} [Group Γ] (ρ : Γ →* (V ≃ₗ[ZMod 2] V))

@[expose] def ActsTv (γ : Γ) (c : V) (μ : Dual (ZMod 2) V) : Prop :=
  ∀ x, ρ γ x = x + μ x • c

variable {ρ}

theorem actsTv_one (c : V) : ActsTv ρ 1 c 0 := fun x => by simp

theorem actsTv_one_zero (μ : Dual (ZMod 2) V) : ActsTv ρ 1 0 μ := fun x => by simp

theorem ActsTv.apply_apply {γ : Γ} {c : V} {μ : Dual (ZMod 2) V} (h : ActsTv ρ γ c μ)
    (hc : μ c = 0) (x : V) : ρ γ (ρ γ x) = x := by
  rw [h (ρ γ x), h x, map_add, map_smul, hc, smul_zero, add_zero, add_assoc,
    add_self_eq_zero_zmod2, add_zero]

theorem ActsTv.inv_apply {γ : Γ} {c : V} {μ : Dual (ZMod 2) V} (h : ActsTv ρ γ c μ)
    (hc : μ c = 0) (x : V) : ρ γ⁻¹ x = ρ γ x := by
  apply (ρ γ).injective
  rw [h.apply_apply hc, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem ActsTv.mul {γ₁ γ₂ : Γ} {c : V} {μ₁ μ₂ : Dual (ZMod 2) V} (h₁ : ActsTv ρ γ₁ c μ₁)
    (h₂ : ActsTv ρ γ₂ c μ₂) (hc : μ₁ c = 0) : ActsTv ρ (γ₁ * γ₂) c (μ₁ + μ₂) := by
  intro x
  rw [map_mul, LinearEquiv.mul_apply, h₂ x, h₁, map_add, map_smul, hc, smul_zero, add_zero,
    LinearMap.add_apply, add_smul]
  abel

theorem ActsTv.mul_same {γ₁ γ₂ : Γ} {c₁ c₂ : V} {μ : Dual (ZMod 2) V} (h₁ : ActsTv ρ γ₁ c₁ μ)
    (h₂ : ActsTv ρ γ₂ c₂ μ) (hc : μ c₂ = 0) : ActsTv ρ (γ₁ * γ₂) (c₁ + c₂) μ := by
  intro x
  rw [map_mul, LinearEquiv.mul_apply, h₂ x, h₁, map_add, map_smul, hc, smul_zero, add_zero,
    smul_add]
  abel

theorem ActsTv.conj {γ δ : Γ} {c d : V} {μ φ : Dual (ZMod 2) V} (hγ : ActsTv ρ γ d φ)
    (hd : φ d = 0) (hδ : ActsTv ρ δ c μ) :
    ActsTv ρ (γ * δ * γ⁻¹) (c + φ c • d) (μ + μ d • φ) := by
  intro x
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hγ.inv_apply hd, hδ,
    map_add, map_smul, hγ.apply_apply hd, hγ c, hγ x, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, mul_comm (φ x), smul_eq_mul]

theorem forall_actsTv_of_exists [FiniteDimensional (ZMod 2) V]
    (hT : ∀ c v : V, c ≠ 0 → v ∉ (ZMod 2) ∙ c →
      ∃ γ : Γ, ∃ μ : Dual (ZMod 2) V, μ c = 0 ∧ μ v ≠ 0 ∧ ActsTv ρ γ c μ)
    (c : V) (μ : Dual (ZMod 2) V) (hμ : μ c = 0) : ∃ γ : Γ, ActsTv ρ γ c μ := by
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, actsTv_one_zero μ⟩
  let U : Submodule (ZMod 2) (Dual (ZMod 2) V) :=
    { carrier := {φ | φ c = 0 ∧ ∃ γ : Γ, ActsTv ρ γ c φ}
      add_mem' := by
        rintro φ₁ φ₂ ⟨h₁, γ₁, hγ₁⟩ ⟨h₂, γ₂, hγ₂⟩
        refine ⟨?_, γ₁ * γ₂, hγ₁.mul hγ₂ h₁⟩
        rw [LinearMap.add_apply, h₁, h₂, add_zero]
      zero_mem' := ⟨rfl, 1, actsTv_one c⟩
      smul_mem' := by
        rintro s φ ⟨h, γ, hγ⟩
        rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
        · rw [zero_smul]
          exact ⟨rfl, 1, actsTv_one c⟩
        · rw [one_smul]
          exact ⟨h, γ, hγ⟩ }
  have hcoann : U.dualCoannihilator ≤ (ZMod 2) ∙ c := by
    intro x hx
    by_contra hxc
    obtain ⟨γ, φ, hφc, hφx, hγ⟩ := hT c x hc hxc
    exact hφx ((Submodule.mem_dualCoannihilator x).mp hx φ ⟨hφc, γ, hγ⟩)
  have hμU : μ ∈ U := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := U), Submodule.mem_dualAnnihilator]
    intro x hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp (hcoann hx)
    rw [map_smul, hμ, smul_zero]
  exact hμU.2

section Normal

variable (hT : ∀ (c : V) (μ : Dual (ZMod 2) V), μ c = 0 → ∃ γ : Γ, ActsTv ρ γ c μ)
  {Δ : Subgroup Γ} (hΔ : Δ.Normal)
include hT hΔ

theorem exists_actsTv_centre {c₀ : V} {μ₀ : Dual (ZMod 2) V} (hc₀ : c₀ ≠ 0) (hμc : μ₀ c₀ = 0)
    (h : ∃ δ ∈ Δ, ActsTv ρ δ c₀ μ₀) {d : V} (hd : μ₀ d = 0) : ∃ δ ∈ Δ, ActsTv ρ δ d μ₀ := by
  by_cases hdc : d ∈ (ZMod 2) ∙ c₀
  · rcases eq_zero_or_eq_of_mem_span_singleton hdc with rfl | rfl
    · exact ⟨1, one_mem _, actsTv_one_zero μ₀⟩
    · exact h
  have hcd : c₀ ∉ (ZMod 2) ∙ d := by
    intro hc
    rcases eq_zero_or_eq_of_mem_span_singleton hc with h0 | h0
    · exact hc₀ h0
    · exact hdc (h0 ▸ Submodule.mem_span_singleton_self c₀)
  obtain ⟨φ, hφc, hφd⟩ := Submodule.exists_le_ker_of_notMem hcd
  have hφd' : φ d = 0 := hφd (Submodule.mem_span_singleton_self d)
  obtain ⟨γ, hγ⟩ := hT d φ hφd'
  obtain ⟨δ, hδ, hδt⟩ := h
  have h1 := hγ.conj hφd' hδt
  rw [zmod2_eq_one_of_ne_zero hφc, one_smul, hd, zero_smul, add_zero] at h1
  have h2 := hδt.mul_same h1 (by rw [map_add, hμc, hd, add_zero])
  rw [← add_assoc, add_self_eq_zero_zmod2, zero_add] at h2
  exact ⟨_, mul_mem hδ (hΔ.conj_mem δ hδ γ), h2⟩

theorem exists_actsTv_functional {d : V} {μ₁ : Dual (ZMod 2) V} (hμ₁ : μ₁ ≠ 0)
    (hd : μ₁ d = 0) (h : ∃ δ ∈ Δ, ActsTv ρ δ d μ₁) {μ : Dual (ZMod 2) V} (hμd : μ d = 0) :
    ∃ δ ∈ Δ, ActsTv ρ δ d μ := by
  by_cases he : ∃ e, μ e = 0 ∧ μ₁ e ≠ 0
  · obtain ⟨e, hμe, hμ₁e⟩ := he
    obtain ⟨γ, hγ⟩ := hT e μ hμe
    obtain ⟨δ, hδ, hδt⟩ := h
    have h1 := hγ.conj hμe hδt
    rw [hμd, zero_smul, add_zero, zmod2_eq_one_of_ne_zero hμ₁e, one_smul] at h1
    have h2 := hδt.mul h1 hd
    rw [← add_assoc, add_self_eq_zero_zmod2 μ₁, zero_add] at h2
    exact ⟨_, mul_mem hδ (hΔ.conj_mem δ hδ γ), h2⟩
  push Not at he
  by_cases hμ0 : μ = 0
  · subst hμ0
    exact ⟨1, one_mem _, actsTv_one d⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, μ x₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hμ0 (LinearMap.ext hcon)
  have hx₀' : μ x₀ = 1 := zmod2_eq_one_of_ne_zero hx₀
  have key : ∀ x, μ₁ x = μ x * μ₁ x₀ := by
    intro x
    have h0 := he (x - μ x • x₀) (by rw [map_sub, map_smul, hx₀']; simp)
    rwa [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  have h1 : μ₁ x₀ = 1 := by
    refine zmod2_eq_one_of_ne_zero fun h0 => hμ₁ (LinearMap.ext fun x => ?_)
    rw [key, h0, mul_zero, LinearMap.zero_apply]
  have : μ₁ = μ := LinearMap.ext fun x => by rw [key, h1, mul_one]
  exact this ▸ h

theorem exists_actsTv_ne_zero [FiniteDimensional (ZMod 2) V] (h3 : 3 ≤ finrank (ZMod 2) V)
    {δ₀ : Γ} (hδ₀ : δ₀ ∈ Δ) {v : V} (hv : ρ δ₀ v ≠ v) :
    ∃ c : V, c ≠ 0 ∧ ∃ μ : Dual (ZMod 2) V, μ ≠ 0 ∧ μ c = 0 ∧ ∃ δ ∈ Δ, ActsTv ρ δ c μ := by
  classical
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hv (map_zero _)
  have hw0 : ρ δ₀ v ≠ 0 := fun h => hv0 ((ρ δ₀).injective (h.trans (map_zero _).symm))
  have hwv : ρ δ₀ v ∉ (ZMod 2) ∙ v := not_mem_span_singleton_of_ne hw0 hv
  have hvw : v ∉ (ZMod 2) ∙ ρ δ₀ v := not_mem_span_singleton_of_ne hv0 (Ne.symm hv)
  obtain ⟨l, hlw, hlv⟩ := Submodule.exists_le_ker_of_notMem hwv
  have hlv' : l v = 0 := hlv (Submodule.mem_span_singleton_self v)
  obtain ⟨γ, hγ⟩ := hT v l hlv'
  have hε : δ₀ * (γ * δ₀⁻¹ * γ⁻¹) ∈ Δ := mul_mem hδ₀ (hΔ.conj_mem _ (inv_mem hδ₀) γ)
  have hεx : ∀ x, ρ (δ₀ * (γ * δ₀⁻¹ * γ⁻¹)) x =
      x + l x • v + l (ρ δ₀⁻¹ (ρ γ x)) • ρ δ₀ v := by
    intro x
    rw [map_mul, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, hγ.inv_apply hlv', hγ (ρ δ₀⁻¹ (ρ γ x)), map_add, map_smul,
      ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, hγ x]
    rfl
  obtain ⟨ε, hεe⟩ : ∃ ε, ε = δ₀ * (γ * δ₀⁻¹ * γ⁻¹) := ⟨_, rfl⟩
  rw [← hεe] at hε hεx
  set w := ρ δ₀ v with hwdef
  have hεw : ρ ε w ≠ w := by
    intro he
    rw [hεx, zmod2_eq_one_of_ne_zero hlw, one_smul, add_assoc, add_eq_left] at he
    apply hvw
    rw [eq_neg_of_add_eq_zero_left he, neg_eq_self_zmod2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hP : Submodule.span (ZMod 2) {v, w} < ⊤ := by
    refine Submodule.lt_top_of_finrank_lt_finrank ?_
    have := finrank_span_le_card (R := ZMod 2) ({v, w} : Set V)
    have h2 : ({v, w} : Set V).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_insert_le _ _
    omega
  obtain ⟨ν, hν0, hνP⟩ := Submodule.exists_le_ker_of_lt_top _ hP
  have hνv : ν v = 0 := hνP (Submodule.subset_span (Set.mem_insert v {w}))
  have hνw : ν w = 0 := hνP (Submodule.subset_span (Set.mem_insert_of_mem v rfl))
  have hνε : ∀ x, ν (ρ ε x) = ν x := by
    intro x
    rw [hεx, map_add, map_add, map_smul, map_smul, hνv, hνw, smul_zero, smul_zero, add_zero,
      add_zero]
  by_cases hA : ∀ u, ν u = 0 → ρ ε u = u
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀, ν x₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hν0 (LinearMap.ext hcon)
    have hx₀' : ν x₀ = 1 := zmod2_eq_one_of_ne_zero hx₀
    have hu₀ : ActsTv ρ ε (ρ ε x₀ - x₀) ν := by
      intro x
      have hker : ν (x - ν x • x₀) = 0 := by
        rw [map_sub, map_smul, hx₀', smul_eq_mul, mul_one, sub_self]
      have h1 := hA _ hker
      rw [map_sub, map_smul] at h1
      calc ρ ε x = (ρ ε x - ν x • ρ ε x₀) + ν x • ρ ε x₀ := by abel
        _ = (x - ν x • x₀) + ν x • ρ ε x₀ := by rw [h1]
        _ = x + ν x • (ρ ε x₀ - x₀) := by rw [smul_sub]; abel
    have hνu₀ : ν (ρ ε x₀ - x₀) = 0 := by rw [map_sub, hνε, sub_self]
    have hu₀0 : ρ ε x₀ - x₀ ≠ 0 := by
      intro h0
      apply hεw
      rw [hu₀ w, h0, smul_zero, add_zero]
    exact ⟨_, hu₀0, ν, hν0, hνu₀, ε, hε, hu₀⟩
  push Not at hA
  obtain ⟨u, hνu, hεu⟩ := hA
  obtain ⟨γ₂, hγ₂⟩ := hT u ν hνu
  have hε₂ : ε * (γ₂ * ε⁻¹ * γ₂⁻¹) ∈ Δ := mul_mem hε (hΔ.conj_mem _ (inv_mem hε) γ₂)
  have hεε : ∀ y, ρ ε (ρ ε⁻¹ y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hνεi : ∀ y, ν (ρ ε⁻¹ y) = ν y := by
    intro y
    conv_rhs => rw [← hεε y]
    rw [hνε]
  have hε₂x : ActsTv ρ (ε * (γ₂ * ε⁻¹ * γ₂⁻¹)) (u + ρ ε u) ν := by
    intro x
    have e1 : ρ (ε * (γ₂ * ε⁻¹ * γ₂⁻¹)) x = ρ ε (ρ γ₂ (ρ ε⁻¹ (ρ γ₂⁻¹ x))) := by
      simp only [map_mul, LinearEquiv.mul_apply]
    rw [e1, hγ₂.inv_apply hνu, hγ₂ (ρ ε⁻¹ _), map_add, map_smul, hεε, hνεi, hγ₂ x, map_add,
      map_smul, hνu, smul_zero, add_zero, smul_add, add_assoc]
  have hνc : ν (u + ρ ε u) = 0 := by rw [map_add, hνε, hνu, add_zero]
  have hc0 : u + ρ ε u ≠ 0 := by
    intro h0
    apply hεu
    rw [eq_neg_of_add_eq_zero_right h0, neg_eq_self_zmod2]
  exact ⟨_, hc0, ν, hν0, hνc, _, hε₂, hε₂x⟩

theorem forall_actsTv_of_normal [FiniteDimensional (ZMod 2) V] (h3 : 3 ≤ finrank (ZMod 2) V)
    {δ₀ : Γ} (hδ₀ : δ₀ ∈ Δ) {v : V} (hv : ρ δ₀ v ≠ v) (c : V) (μ : Dual (ZMod 2) V)
    (hμ : μ c = 0) : ∃ δ ∈ Δ, ActsTv ρ δ c μ := by
  classical
  by_cases hc : c = 0
  · subst hc
    exact ⟨1, one_mem _, actsTv_one_zero μ⟩
  obtain ⟨c₀, hc₀, μ₀, hμ₀, hμc₀, h₀⟩ := exists_actsTv_ne_zero hT hΔ h3 hδ₀ hv
  have hP : Submodule.span (ZMod 2) {c₀, c} < ⊤ := by
    refine Submodule.lt_top_of_finrank_lt_finrank ?_
    have := finrank_span_le_card (R := ZMod 2) ({c₀, c} : Set V)
    have h2 : ({c₀, c} : Set V).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]
      exact Finset.card_insert_le _ _
    omega
  obtain ⟨φ, hφ0, hφP⟩ := Submodule.exists_le_ker_of_lt_top _ hP
  have hφc₀ : φ c₀ = 0 := hφP (Submodule.subset_span (Set.mem_insert c₀ {c}))
  have hφc : φ c = 0 := hφP (Submodule.subset_span (Set.mem_insert_of_mem c₀ rfl))
  have h1 := exists_actsTv_functional hT hΔ hμ₀ hμc₀ h₀ hφc₀
  have h2 := exists_actsTv_centre hT hΔ hc₀ hφc₀ h1 hφc
  exact exists_actsTv_functional hT hΔ hφ0 hφc h2 hμ

end Normal

end CFSG.LargeExtraspecial.S9
