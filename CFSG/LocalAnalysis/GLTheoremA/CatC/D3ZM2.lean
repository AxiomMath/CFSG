module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZM1
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ITitsD4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


theorem mem_normalizer_of_map_conj {G : Type*} [Group G] (S : Subgroup G) (y : G)
    (h : S.map (MulAut.conj y).toMonoidHom = S) : y ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : y * x * y⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h] at this
  · intro hx
    rw [← h] at hx
    obtain ⟨s, hs, hsx⟩ := hx
    have h2 : y * s * y⁻¹ = y * x * y⁻¹ := by simpa [MulAut.conj_apply] using hsx
    have : s = x := by simpa using h2
    rwa [this] at hs

section Main

variable {K : Type} [Field K] [Finite K]

theorem d3_fourgroup_false {n : ℕ} (hK : Nat.card K = 3 ^ n) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) {y₀ y₁ : D4Model K} (hy₀2 : y₀ * y₀ = 1) (hy₁2 : y₁ * y₁ = 1)
    (hcomm : y₀ * y₁ = y₁ * y₀) (hy₀1 : y₀ ≠ 1) (hy₁1 : y₁ ≠ 1) (hne : y₀ ≠ y₁)
    (hty₀ : t y₀ = y₀) (hty₁ : t y₁ = y₁) {A : Subgroup (D4Model K)} (hA : IsElemAbelian 3 A)
    (hA1 : A ≠ ⊥) (hAt : ∀ a ∈ A, t a = a) (hA₀ : ∀ a ∈ A, y₀ * a * y₀⁻¹ = a)
    (hA₁ : ∀ a ∈ A, y₁ * a * y₁⁻¹ = a) : False := by
  classical
  haveI := charP_three_of_card hK
  have hn : 1 ≤ n := one_le_of_card_field hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (D4Model K) := inferInstance
  have hBT := holds_D4Model_three hK hn
  have hAp : IsPGroup 3 A := fun a => ⟨1, by
    apply Subtype.ext
    simpa using hA.2 a.1 a.2⟩
  have hmap : ∀ φ : MulAut (D4Model K), (∀ a ∈ A, φ a = a) → A.map φ.toMonoidHom = A := by
    intro φ hφ
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      change φ a ∈ A
      rw [hφ a ha]; exact ha
    · intro hx
      exact ⟨x, hx, hφ x hx⟩
  obtain ⟨V, hAV, hV1, hVp, hVφ, hVtop, hVc, hVS⟩ := exists_canonical_parabolic 3 hBT hA1 hAp
  have hVt : V.map t.toMonoidHom = V := hVφ t (hmap t hAt)
  have hVz₀ : V.map (MulAut.conj y₀).toMonoidHom = V := hVφ (MulAut.conj y₀)
    (hmap _ fun a ha => by simpa [MulAut.conj_apply] using hA₀ a ha)
  have hVz₁ : V.map (MulAut.conj y₁).toMonoidHom = V := hVφ (MulAut.conj y₁)
    (hmap _ fun a ha => by simpa [MulAut.conj_apply] using hA₁ a ha)
  have hy₀P : y₀ ∈ Subgroup.normalizer (V : Set (D4Model K)) := mem_normalizer_of_map_conj V y₀ hVz₀
  have hy₁P : y₁ ∈ Subgroup.normalizer (V : Set (D4Model K)) := mem_normalizer_of_map_conj V y₁ hVz₁
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
  have hPt : ∀ x ∈ Subgroup.normalizer (V : Set (D4Model K)), t x ∈
      Subgroup.normalizer (V : Set (D4Model K)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro h
    obtain ⟨h', rfl⟩ := t.surjective h
    have e : t x * t h' * (t x)⁻¹ = t (x * h' * x⁻¹) := by simp
    rw [e, hVm, hVm, hx h']
  obtain ⟨S₀, hS₀⟩ := hVS
  have hS₀P : (S₀ : Subgroup (D4Model K)) ≤ Subgroup.normalizer (V : Set (D4Model K)) :=
    Subgroup.le_normalizer.trans hS₀
  obtain ⟨S₁, hS₁P, hS₁t⟩ := exists_stable_sylow_in t ht3 _ hPt S₀ hS₀P
  have hNS₁ := normalizer_le_of_sylow _ S₀ S₁ hS₀P hS₁P hS₀
  obtain ⟨c, hcP, hc1, hc2, hc3⟩ := levi_main_pair hK ht3 htE hPt hVtop hNS₁ hS₁t hy₀P hy₁P hy₀2 hy₁2
    hcomm hty₀ hty₁
  have e : ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)) =
      (S₁ : Subgroup (D4Model K)).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]; rfl
  have hSP : ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)) ≤
      Subgroup.normalizer (V : Set (D4Model K)) := by
    rw [e]
    rintro _ ⟨s, hs, rfl⟩
    exact mul_mem (mul_mem hcP (hS₁P hs)) (inv_mem hcP)
  have hSt : ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)).map t.toMonoidHom = c • S₁ := by
    rw [e]; exact map_conj_stable t _ hS₁t c hc1
  have hSz₀ : ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)).map
      (MulAut.conj y₀).toMonoidHom = c • S₁ := by
    rw [e]; exact map_conj_stable_inner y₀ c _ hc2
  have hSz₁ : ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)).map
      (MulAut.conj y₁).toMonoidHom = c • S₁ := by
    rw [e]; exact map_conj_stable_inner y₁ c _ hc3
  have hAS : A ≤ ((c • S₁ : Sylow 3 (D4Model K)) : Subgroup (D4Model K)) := by
    refine hAV.trans ?_
    rw [← hVc]
    exact pCoreOf_le_sylow 3 (c • S₁) hSP
  exact hA1 (four_group_borel hK ht3 htE hSt (mem_normalizer_of_map_conj _ y₀ hSz₀)
    (mem_normalizer_of_map_conj _ y₁ hSz₁) hy₀2 hy₁2 hcomm hy₀1 hy₁1 hne hty₀ hty₁ hAS hA₀ hA₁)

end Main

end CFSG.LocalAnalysis.GLTheoremA
