module

public import CFSG.LargeExtraspecial.DW2ModOne
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLForm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection commutatorSpace tv tv_apply
  GenByTransvections IsIrreducibleOn NoDihedralPair InG isF2Transvection_iff exists_apply_eq_one
  exists_preConfig eq_top_of_dihedral)

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_apply_eq_one_apply_eq_zero {φ ψ : Dual (ZMod 2) W} (hφ : φ ≠ 0) (hφψ : φ ≠ ψ) :
    ∃ y, φ y = 1 ∧ ψ y = 0 := by
  by_contra h
  push Not at h
  obtain ⟨y₀, hy₀⟩ := exists_apply_eq_one hφ
  apply hφψ
  refine LinearMap.ext fun y => ?_
  have hψ1 : ∀ y, φ y = 1 → ψ y = 1 := fun y hy => by
    rcases zmod2_cases (ψ y) with h0 | h1
    · exact absurd h0 (h y hy)
    · exact h1
  rcases zmod2_cases (φ y) with h0 | h1
  · have h2 : φ (y + y₀) = 1 := by rw [map_add, h0, hy₀, zero_add]
    have h3 := hψ1 _ h2
    rw [map_add, hψ1 y₀ hy₀] at h3
    rw [h0]
    have h4 : ψ y = 0 := by
      have := congrArg (· + 1) h3
      simpa [add_assoc, show (1 : ZMod 2) + 1 = 0 from rfl] using this
    rw [h4]
  · rw [h1, hψ1 y h1]

variable (β : LinearMap.BilinForm (ZMod 2) W)

theorem tv_eq_of_isometry (hself : ∀ v, β v v = 0) (hcomm : ∀ u v, β u v = β v u)
    (hnd : ∀ u, (∀ v, β u v = 0) → u = 0) {φ : Dual (ZMod 2) W} {c : W} (h : φ c = 0)
    (hφ : φ ≠ 0) (hc : c ≠ 0)
    (hiso : ∀ x y, β ((tv φ c h : W →ₗ[ZMod 2] W) x) ((tv φ c h : W →ₗ[ZMod 2] W) y) = β x y) :
    φ = β c := by
  have hβc : β c ≠ 0 := fun h0 => hc (hnd c fun v => by rw [h0, LinearMap.zero_apply])
  obtain ⟨y₀, hy₀⟩ := exists_apply_eq_one hβc
  have key : ∀ x, φ x = φ y₀ * β c x := by
    intro x
    have e := hiso x y₀
    simp only [tv_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hself, hy₀, mul_zero, add_zero, mul_one] at e
    have e' : φ y₀ * β c x + φ x = 0 := by linear_combination e - φ y₀ * hcomm x c
    calc φ x = φ x + (φ y₀ * β c x + φ x) := by rw [e', add_zero]
      _ = φ y₀ * β c x + (φ x + φ x) := by ring
      _ = φ y₀ * β c x := by rw [show φ x + φ x = 0 from add_self_zmod2 (φ x), add_zero]
  have hy1 : φ y₀ = 1 := by
    rcases zmod2_cases (φ y₀) with h0 | h1
    · exact absurd (LinearMap.ext fun x => by rw [key x, h0, zero_mul, LinearMap.zero_apply])
        hφ
    · exact h1
  exact LinearMap.ext fun x => by rw [key x, hy1, one_mul]

theorem not_isF2Transvection_tv_mul_tv (hnd : ∀ u, (∀ v, β u v = 0) → u = 0) {c₁ c₂ : W}
    (h₁ : β c₁ c₁ = 0) (h₂ : β c₂ c₂ = 0) (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (hne : c₁ ≠ c₂) :
    ¬ IsF2Transvection (tv (β c₁) c₁ h₁ * tv (β c₂) c₂ h₂) := by
  intro ht
  have hβ : ∀ c : W, c ≠ 0 → β c ≠ 0 := fun c hc h0 =>
    hc (hnd c fun v => by rw [h0, LinearMap.zero_apply])
  have hβne : β c₁ ≠ β c₂ := fun h => hne (sub_eq_zero.mp (hnd _ fun v => by
    rw [map_sub, LinearMap.sub_apply, h, sub_self]))
  obtain ⟨y, hy1, hy2⟩ := exists_apply_eq_one_apply_eq_zero (hβ c₁ hc₁) hβne
  obtain ⟨y', hy'2, hy'1⟩ := exists_apply_eq_one_apply_eq_zero (hβ c₂ hc₂) hβne.symm
  set t := tv (β c₁) c₁ h₁ * tv (β c₂) c₂ h₂ with htdef
  have happ : ∀ v, ((LinearMap.id + (t : W →ₗ[ZMod 2] W)) : W →ₗ[ZMod 2] W) v =
      v + ((tv (β c₁) c₁ h₁ : W →ₗ[ZMod 2] W) ((tv (β c₂) c₂ h₂ : W →ₗ[ZMod 2] W) v)) :=
    fun v => rfl
  have hm1 : c₁ ∈ commutatorSpace t := by
    refine ⟨y, ?_⟩
    rw [happ, tv_apply, tv_apply, hy2, zero_smul, add_zero, hy1, one_smul, ← add_assoc,
      add_self_zmod2, zero_add]
  have hm2 : c₂ + β c₁ c₂ • c₁ ∈ commutatorSpace t := by
    refine ⟨y', ?_⟩
    rw [happ, tv_apply, tv_apply, hy'2, one_smul, map_add, hy'1, zero_add, ← add_assoc,
      ← add_assoc, add_self_zmod2, zero_add]
  obtain ⟨l, -, -, hl⟩ := exists_unique_ne_zero_of_finrank_eq_one ht.2
  have hcl : c₁ = l := hl _ hm1 hc₁
  have hc₂mem : c₂ = 0 ∨ c₂ = c₁ := by
    by_cases h0 : c₂ + β c₁ c₂ • c₁ = 0
    · rcases zmod2_cases (β c₁ c₂) with e | e <;> rw [e] at h0
      · rw [zero_smul, add_zero] at h0
        exact Or.inl h0
      · rw [one_smul] at h0
        exact Or.inr (by rw [← sub_eq_zero, sub_eq_add_zmod2]; exact h0)
    · have h3 := hl _ hm2 h0
      rw [← hcl] at h3
      rcases zmod2_cases (β c₁ c₂) with e | e <;> rw [e] at h3
      · rw [zero_smul, add_zero] at h3
        exact Or.inr h3
      · rw [one_smul] at h3
        refine Or.inl ?_
        have := congrArg (· + c₁) h3
        simpa [add_assoc, add_self_zmod2] using this
  rcases hc₂mem with h | h
  · exact hc₂ h
  · exact hne h.symm

theorem false_of_fourGroup_of_isometry (hself : ∀ v, β v v = 0)
    (hcomm : ∀ u v, β u v = β v u) (hnd : ∀ u, (∀ v, β u v = 0) → u = 0)
    {τ₁ τ₂ : LinearMap.GeneralLinearGroup (ZMod 2) W} (ht₁ : IsF2Transvection τ₁)
    (ht₂ : IsF2Transvection τ₂) (hne : τ₁ ≠ τ₂) (ht₁₂ : IsF2Transvection (τ₁ * τ₂))
    (hiso₁ : ∀ x y, β ((τ₁ : W →ₗ[ZMod 2] W) x) ((τ₁ : W →ₗ[ZMod 2] W) y) = β x y)
    (hiso₂ : ∀ x y, β ((τ₂ : W →ₗ[ZMod 2] W) x) ((τ₂ : W →ₗ[ZMod 2] W) y) = β x y) : False := by
  obtain ⟨φ₁, c₁, h₁, hφ₁, hc₁, rfl⟩ := (isF2Transvection_iff τ₁).mp ht₁
  obtain ⟨φ₂, c₂, h₂, hφ₂, hc₂, rfl⟩ := (isF2Transvection_iff τ₂).mp ht₂
  have e₁ := tv_eq_of_isometry β hself hcomm hnd h₁ hφ₁ hc₁ hiso₁
  have e₂ := tv_eq_of_isometry β hself hcomm hnd h₂ hφ₂ hc₂ hiso₂
  subst e₁ e₂
  refine not_isF2Transvection_tv_mul_tv β hnd h₁ h₂ hc₁ hc₂ (fun h => hne ?_) ht₁₂
  subst h
  rfl

variable [FiniteDimensional (ZMod 2) W]

theorem not_noDihedralPair_of_fourGroup {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hgen : GenByTransvections G) (hirr : IsIrreducibleOn G)
    {τ₁ τ₂ : LinearMap.GeneralLinearGroup (ZMod 2) W} (hτ₁ : τ₁ ∈ G) (hτ₂ : τ₂ ∈ G)
    (ht₁ : IsF2Transvection τ₁) (ht₂ : IsF2Transvection τ₂) (hne : τ₁ ≠ τ₂)
    (ht₁₂ : IsF2Transvection (τ₁ * τ₂)) : ¬ NoDihedralPair G := by
  intro hno
  obtain ⟨φ₁, c₁, h₁, hφ₁, hc₁, rfl⟩ := (isF2Transvection_iff τ₁).mp ht₁
  obtain ⟨φ₂, c₂, h₂, hφ₂, hc₂, rfl⟩ := (isF2Transvection_iff τ₂).mp ht₂
  have hne' : (CFSG.ComponentClassification.OutcomeLocal.centres G).Nonempty :=
    ⟨c₁, hc₁, φ₁, hφ₁, h₁, hτ₁⟩
  obtain ⟨P, -, hF4, -⟩ := exists_preConfig hgen hirr hno hne'
  have e₁ := hF4 φ₁ c₁ hc₁ hφ₁ ⟨h₁, hτ₁⟩
  have e₂ := hF4 φ₂ c₂ hc₂ hφ₂ ⟨h₂, hτ₂⟩
  subst e₁ e₂
  refine not_isF2Transvection_tv_mul_tv P.b P.nondeg h₁ h₂ hc₁ hc₂ (fun h => hne ?_) ht₁₂
  subst h
  rfl

theorem eq_top_of_fourGroup {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) W)}
    (hgen : GenByTransvections G) (hirr : IsIrreducibleOn G)
    {τ₁ τ₂ : LinearMap.GeneralLinearGroup (ZMod 2) W} (hτ₁ : τ₁ ∈ G) (hτ₂ : τ₂ ∈ G)
    (ht₁ : IsF2Transvection τ₁) (ht₂ : IsF2Transvection τ₂) (hne : τ₁ ≠ τ₂)
    (ht₁₂ : IsF2Transvection (τ₁ * τ₂)) : G = ⊤ := by
  have h := not_noDihedralPair_of_fourGroup hgen hirr hτ₁ hτ₂ ht₁ ht₂ hne ht₁₂
  simp only [NoDihedralPair, not_forall, not_false_eq_true, exists_prop] at h
  obtain ⟨φ, ψ, a, b, ha, hψ, hφa, hψb, hφb, hψa, -⟩ := h
  exact eq_top_of_dihedral hgen hirr ha hψ hφa hψb hφb hψa

end CFSG.LargeExtraspecial.DW
