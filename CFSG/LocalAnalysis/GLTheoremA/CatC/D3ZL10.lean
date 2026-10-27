module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL9
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITitsD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


theorem d3InnerLevi_holds : D3InnerLevi := by
  intro K _ _ n hK t ht3 htE z hz2 hz1 hzI hzt V hV1 hVp hVt hVz hVc hVtop hVS
  classical
  haveI := charP_three_of_card hK
  have hn : 1 ≤ n := one_le_of_card_field hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (D4Model K) := inferInstance
  have hcen : Subgroup.center (D4Model K) = ⊥ :=
    (d4Facts2 Nat.prime_three (by norm_num) hn hK).2.2
  obtain ⟨y₀, rfl⟩ := hzI
  have hVm : ∀ h, t h ∈ V ↔ h ∈ V := by
    intro h
    constructor
    · intro hh
      rw [← hVt] at hh
      obtain ⟨v, hv, hvh⟩ := hh
      have : v = h := t.injective hvh
      rw [← this]; exact hv
    · intro hh
      have := Subgroup.mem_map_of_mem t.toMonoidHom hh
      rwa [hVt] at this
  have hVzm : ∀ h, y₀ * h * y₀⁻¹ ∈ V ↔ h ∈ V := by
    intro h
    constructor
    · intro hh
      rw [← hVz] at hh
      obtain ⟨v, hv, hvh⟩ := hh
      have : v = h := (MulAut.conj y₀).injective hvh
      rw [← this]; exact hv
    · intro hh
      have := Subgroup.mem_map_of_mem (MulAut.conj y₀).toMonoidHom hh
      rwa [hVz] at this
  have hPt : ∀ x ∈ Subgroup.normalizer (V : Set (D4Model K)), t x ∈
      Subgroup.normalizer (V : Set (D4Model K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro h
    obtain ⟨h', rfl⟩ := t.surjective h
    have e : t x * t h' * (t x)⁻¹ = t (x * h' * x⁻¹) := by simp
    rw [e, hVm, hVm, hx h']
  have hy₀P : y₀ ∈ Subgroup.normalizer (V : Set (D4Model K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact (hVzm h).symm
  have hy₀2 : y₀ * y₀ = 1 := by
    have h1 : y₀ * y₀ ∈ Subgroup.center (D4Model K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut (D4Model K) => φ g) hz2
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply,
        MulAut.conj_apply] at this
      have h2 : y₀ * y₀ * g = g * (y₀ * y₀) := by
        calc y₀ * y₀ * g = (y₀ * (y₀ * g * y₀⁻¹) * y₀⁻¹) * (y₀ * y₀) := by group
          _ = g * (y₀ * y₀) := by rw [this]
      exact h2.symm
    rw [hcen] at h1
    exact Subgroup.mem_bot.1 h1
  have hty₀ : t y₀ = y₀ := by
    have h1 : (t y₀)⁻¹ * y₀ ∈ Subgroup.center (D4Model K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := t.surjective g
      have := congrArg (fun φ : MulAut (D4Model K) => φ g') hzt
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at this
      calc t g' * ((t y₀)⁻¹ * y₀) = (t y₀)⁻¹ * (t y₀ * t g' * (t y₀)⁻¹) * y₀ := by group
        _ = (t y₀)⁻¹ * (y₀ * t g' * y₀⁻¹) * y₀ := by rw [← this]
        _ = (t y₀)⁻¹ * y₀ * t g' := by group
    rw [hcen] at h1
    have := Subgroup.mem_bot.1 h1
    have h2 : y₀ = t y₀ := by
      calc y₀ = t y₀ * ((t y₀)⁻¹ * y₀) := by group
        _ = t y₀ := by rw [this, mul_one]
    exact h2.symm
  obtain ⟨S₀, hS₀⟩ := hVS
  have hS₀P : (S₀ : Subgroup (D4Model K)) ≤ Subgroup.normalizer (V : Set (D4Model K)) :=
    Subgroup.le_normalizer.trans hS₀
  obtain ⟨S₁, hS₁P, hS₁t⟩ := exists_stable_sylow_in t ht3 _ hPt S₀ hS₀P
  have hNS₁ := normalizer_le_of_sylow _ S₀ S₁ hS₀P hS₁P hS₀
  obtain ⟨c, hcP, hc1, hc2⟩ := levi_main hK ht3 htE hPt hVtop hNS₁ hS₁t hy₀P hy₀2 hty₀
  have e : ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)) =
      (S₁ : Subgroup (D4Model K)).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl
  refine ⟨c • S₁, ?_, ?_, ?_⟩
  · rw [e]
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hcP (hS₁P hs)) (inv_mem hcP)
  · rw [e]; exact map_conj_stable t _ hS₁t c hc1
  · rw [e]; exact map_conj_stable_inner y₀ c _ hc2

end CFSG.LocalAnalysis.GLTheoremA
