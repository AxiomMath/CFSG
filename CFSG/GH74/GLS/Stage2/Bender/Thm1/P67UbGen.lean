module

public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

structure FrameRel (σ : K ≃+* K) {n : ℕ} (e₁ f₁ e₂ f₂ : Fin n → K) : Prop where
  e1e1 : herm σ e₁ e₁ = 0
  e1f1 : herm σ e₁ f₁ = 1
  e1e2 : herm σ e₁ e₂ = 0
  e1f2 : herm σ e₁ f₂ = 0
  f1e1 : herm σ f₁ e₁ = 1
  f1f1 : herm σ f₁ f₁ = 0
  f1e2 : herm σ f₁ e₂ = 0
  f1f2 : herm σ f₁ f₂ = 0
  e2e1 : herm σ e₂ e₁ = 0
  e2f1 : herm σ e₂ f₁ = 0
  e2e2 : herm σ e₂ e₂ = 0
  e2f2 : herm σ e₂ f₂ = 1
  f2e1 : herm σ f₂ e₁ = 0
  f2f1 : herm σ f₂ f₁ = 0
  f2e2 : herm σ f₂ e₂ = 1
  f2f2 : herm σ f₂ f₂ = 0

@[expose] def vec4 (e₁ f₁ e₂ f₂ : Fin n → K) (ε₁ φ₁ ε₂ φ₂ : K) : Fin n → K :=
  ε₁ • e₁ + φ₁ • f₁ + ε₂ • e₂ + φ₂ • f₂

variable {e₁ f₁ e₂ f₂ : Fin n → K}

theorem herm_e1_vec4 (hF : FrameRel σ e₁ f₁ e₂ f₂) (ε₁ φ₁ ε₂ φ₂ : K) :
    herm σ e₁ (vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) = φ₁ := by
  simp only [vec4, herm_add_right, herm_smul_right, hF.e1e1, hF.e1f1, hF.e1e2, hF.e1f2]; ring

theorem herm_f1_vec4 (hF : FrameRel σ e₁ f₁ e₂ f₂) (ε₁ φ₁ ε₂ φ₂ : K) :
    herm σ f₁ (vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) = ε₁ := by
  simp only [vec4, herm_add_right, herm_smul_right, hF.f1e1, hF.f1f1, hF.f1e2, hF.f1f2]; ring

theorem herm_e2_vec4 (hF : FrameRel σ e₁ f₁ e₂ f₂) (ε₁ φ₁ ε₂ φ₂ : K) :
    herm σ e₂ (vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) = φ₂ := by
  simp only [vec4, herm_add_right, herm_smul_right, hF.e2e1, hF.e2f1, hF.e2e2, hF.e2f2]; ring

theorem herm_f2_vec4 (hF : FrameRel σ e₁ f₁ e₂ f₂) (ε₁ φ₁ ε₂ φ₂ : K) :
    herm σ f₂ (vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) = ε₂ := by
  simp only [vec4, herm_add_right, herm_smul_right, hF.f2e1, hF.f2f1, hF.f2e2, hF.f2f2]; ring


section Siegel

variable (hF : FrameRel σ e₁ f₁ e₂ f₂) {g : SUid σ n} {μ : K}

include hF

theorem siegel_e1f2_vec4
    (hS : ∀ x, g • x = x + (μ * herm σ e₁ x) • f₂ - (σ μ * herm σ f₂ x) • e₁)
    (ε₁ φ₁ ε₂ φ₂ : K) :
    g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ =
      vec4 e₁ f₁ e₂ f₂ (ε₁ - σ μ * ε₂) φ₁ ε₂ (φ₂ + μ * φ₁) := by
  rw [hS, herm_e1_vec4 hF, herm_f2_vec4 hF]
  simp only [vec4]
  module

theorem siegel_e2f1_vec4
    (hS : ∀ x, g • x = x + (μ * herm σ e₂ x) • f₁ - (σ μ * herm σ f₁ x) • e₂)
    (ε₁ φ₁ ε₂ φ₂ : K) :
    g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ =
      vec4 e₁ f₁ e₂ f₂ ε₁ (φ₁ + μ * φ₂) (ε₂ - σ μ * ε₁) φ₂ := by
  rw [hS, herm_e2_vec4 hF, herm_f1_vec4 hF]
  simp only [vec4]
  module

theorem siegel_e1e2_vec4
    (hS : ∀ x, g • x = x + (μ * herm σ e₁ x) • e₂ - (σ μ * herm σ e₂ x) • e₁)
    (ε₁ φ₁ ε₂ φ₂ : K) :
    g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ =
      vec4 e₁ f₁ e₂ f₂ (ε₁ - σ μ * φ₂) φ₁ (ε₂ + μ * φ₁) φ₂ := by
  rw [hS, herm_e1_vec4 hF, herm_e2_vec4 hF]
  simp only [vec4]
  module

theorem siegel_f1f2_vec4
    (hS : ∀ x, g • x = x + (μ * herm σ f₁ x) • f₂ - (σ μ * herm σ f₂ x) • f₁)
    (ε₁ φ₁ ε₂ φ₂ : K) :
    g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ =
      vec4 e₁ f₁ e₂ f₂ ε₁ (φ₁ - σ μ * ε₂) ε₂ (φ₂ + μ * ε₁) := by
  rw [hS, herm_f1_vec4 hF, herm_f2_vec4 hF]
  simp only [vec4]
  module

end Siegel

theorem tv_mem_of_smul_eq (hσ : ∀ c, σ (σ c) = c) {Ĥ : Subgroup (SUid σ n)} {g : SUid σ n}
    (hg : g ∈ Ĥ) {a a' : Fin n → K} (hga : g • a = a') (ha : herm σ a a = 0)
    (ha' : herm σ a' a' = 0) {c : K} (hc : c + σ c = 0) (h' : tv hσ ha' hc ∈ Ĥ) :
    tv hσ ha hc ∈ Ĥ := by
  have : tv hσ ha hc = g⁻¹ * tv hσ ha' hc * g⁻¹⁻¹ := by
    apply ext_smul
    intro v
    rw [conj_smul_of_tv g⁻¹ (tv hσ ha' hc) (tv_smul hσ ha' hc) v, ← hga, inv_smul_smul,
      tv_smul]
  rw [this]
  exact Ĥ.mul_mem (Ĥ.mul_mem (Ĥ.inv_mem hg) h') (Ĥ.inv_mem (Ĥ.inv_mem hg))


theorem vec4_congr {A A' B B' C C' D D' : K} (h1 : A = A') (h2 : B = B') (h3 : C = C')
    (h4 : D = D') :
    vec4 e₁ f₁ e₂ f₂ A B C D = vec4 e₁ f₁ e₂ f₂ A' B' C' D' := by
  subst h1 h2 h3 h4
  rfl

section Orbit

variable (hσ : IsUnitaryInvolution σ) (hF : FrameRel σ e₁ f₁ e₂ f₂) (Ĥ : Subgroup (SUid σ n))

include hσ hF

theorem reach_vec4
    (hS1 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₁ x) • f₂ - (σ μ * herm σ f₂ x) • e₁)
    (hS2 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₂ x) • f₁ - (σ μ * herm σ f₁ x) • e₂)
    (hS3 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₁ x) • e₂ - (σ μ * herm σ e₂ x) • e₁)
    (hS4 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ f₁ x) • f₂ - (σ μ * herm σ f₂ x) • f₁)
    (ε₁ φ₁ ε₂ φ₂ : K) :
    ∃ g ∈ Ĥ, (∃ c₁ c₂ : K, g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ = vec4 e₁ f₁ e₂ f₂ c₁ c₂ 0 0) ∨
      (∃ c₃ c₄ : K, g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ = vec4 e₁ f₁ e₂ f₂ 0 0 c₃ c₄) := by
  classical
  have hinv := hσ.invol
  by_cases hε₂ : ε₂ = 0
  · subst hε₂
    by_cases hφ₂ : φ₂ = 0
    · subst hφ₂
      exact ⟨1, Ĥ.one_mem, Or.inl ⟨ε₁, φ₁, by rw [one_smul]⟩⟩
    · by_cases hφ₁ : φ₁ = 0
      · subst hφ₁
        obtain ⟨μ, hμ⟩ : ∃ μ, σ μ * φ₂ = ε₁ := ⟨σ (ε₁ / φ₂), by rw [hinv]; field_simp⟩
        obtain ⟨g, hg, hS⟩ := hS3 μ
        refine ⟨g, hg, Or.inr ⟨0, φ₂, ?_⟩⟩
        rw [siegel_e1e2_vec4 hF hS]
        exact vec4_congr (by rw [hμ, sub_self]) rfl (by ring) rfl
      · obtain ⟨g, hg, hS⟩ := hS1 (-φ₂ / φ₁)
        refine ⟨g, hg, Or.inl ⟨ε₁, φ₁, ?_⟩⟩
        rw [siegel_e1f2_vec4 hF hS]
        exact vec4_congr (by ring) rfl rfl (by field_simp; ring)
  · obtain ⟨μ₁, hμ₁⟩ : ∃ μ, σ μ * ε₂ = ε₁ := ⟨σ (ε₁ / ε₂), by rw [hinv]; field_simp⟩
    obtain ⟨g₁, hg₁, hS₁⟩ := hS1 μ₁
    have e1 : g₁ • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ =
        vec4 e₁ f₁ e₂ f₂ 0 φ₁ ε₂ (φ₂ + μ₁ * φ₁) := by
      rw [siegel_e1f2_vec4 hF hS₁]
      exact vec4_congr (by rw [hμ₁, sub_self]) rfl rfl rfl
    by_cases hφ₂' : φ₂ + μ₁ * φ₁ = 0
    · obtain ⟨μ₃, hμ₃⟩ : ∃ μ, σ μ * ε₂ = φ₁ := ⟨σ (φ₁ / ε₂), by rw [hinv]; field_simp⟩
      obtain ⟨g₂, hg₂, hS₂⟩ := hS4 μ₃
      refine ⟨g₂ * g₁, Ĥ.mul_mem hg₂ hg₁, Or.inr ⟨ε₂, 0, ?_⟩⟩
      rw [mul_smul, e1, siegel_f1f2_vec4 hF hS₂]
      exact vec4_congr rfl (by rw [hμ₃, sub_self]) rfl (by rw [hφ₂']; ring)
    · obtain ⟨g₂, hg₂, hS₂⟩ := hS2 (-φ₁ / (φ₂ + μ₁ * φ₁))
      refine ⟨g₂ * g₁, Ĥ.mul_mem hg₂ hg₁, Or.inr ⟨ε₂, φ₂ + μ₁ * φ₁, ?_⟩⟩
      rw [mul_smul, e1, siegel_e2f1_vec4 hF hS₂]
      exact vec4_congr rfl (by rw [div_mul_cancel₀ _ hφ₂']; ring) (by ring) rfl

end Orbit


section Generation

variable (hσ : IsUnitaryInvolution σ) (hF : FrameRel σ e₁ f₁ e₂ f₂) (Ĥ : Subgroup (SUid σ n))

@[expose] def Sp4 (e₁ f₁ e₂ f₂ : Fin n → K) (a : Fin n → K) : Prop :=
  ∃ ε₁ φ₁ ε₂ φ₂ : K, a = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂

theorem Sp4.add {a b : Fin n → K} (ha : Sp4 e₁ f₁ e₂ f₂ a) (hb : Sp4 e₁ f₁ e₂ f₂ b) :
    Sp4 e₁ f₁ e₂ f₂ (a + b) := by
  obtain ⟨ε₁, φ₁, ε₂, φ₂, rfl⟩ := ha
  obtain ⟨ε₁', φ₁', ε₂', φ₂', rfl⟩ := hb
  exact ⟨ε₁ + ε₁', φ₁ + φ₁', ε₂ + ε₂', φ₂ + φ₂', by simp only [vec4]; module⟩

theorem Sp4.smul {a : Fin n → K} (t : K) (ha : Sp4 e₁ f₁ e₂ f₂ a) : Sp4 e₁ f₁ e₂ f₂ (t • a) := by
  obtain ⟨ε₁, φ₁, ε₂, φ₂, rfl⟩ := ha
  exact ⟨t * ε₁, t * φ₁, t * ε₂, t * φ₂, by simp only [vec4]; module⟩

theorem Sp4_e₁ : Sp4 e₁ f₁ e₂ f₂ e₁ := ⟨1, 0, 0, 0, by simp only [vec4]; module⟩
theorem Sp4_f₁ : Sp4 e₁ f₁ e₂ f₂ f₁ := ⟨0, 1, 0, 0, by simp only [vec4]; module⟩
theorem Sp4_e₂ : Sp4 e₁ f₁ e₂ f₂ e₂ := ⟨0, 0, 1, 0, by simp only [vec4]; module⟩
theorem Sp4_f₂ : Sp4 e₁ f₁ e₂ f₂ f₂ := ⟨0, 0, 0, 1, by simp only [vec4]; module⟩

include hσ hF

theorem tv_mem_of_vec4
    (hS1 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₁ x) • f₂ - (σ μ * herm σ f₂ x) • e₁)
    (hS2 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₂ x) • f₁ - (σ μ * herm σ f₁ x) • e₂)
    (hS3 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₁ x) • e₂ - (σ μ * herm σ e₂ x) • e₁)
    (hS4 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ f₁ x) • f₂ - (σ μ * herm σ f₂ x) • f₁)
    (hT : ∀ (a : Fin n → K) (ha : herm σ a a = 0) (c : K) (hc : c + σ c = 0),
      ((∃ c₁ c₂ : K, a = vec4 e₁ f₁ e₂ f₂ c₁ c₂ 0 0) ∨
        (∃ c₃ c₄ : K, a = vec4 e₁ f₁ e₂ f₂ 0 0 c₃ c₄)) → tv hσ.invol ha hc ∈ Ĥ)
    {a : Fin n → K} (hSp : Sp4 e₁ f₁ e₂ f₂ a) (ha : herm σ a a = 0) {c : K} (hc : c + σ c = 0) :
    tv hσ.invol ha hc ∈ Ĥ := by
  obtain ⟨ε₁, φ₁, ε₂, φ₂, rfl⟩ := hSp
  obtain ⟨g, hg, h | h⟩ := reach_vec4 hσ hF Ĥ hS1 hS2 hS3 hS4 ε₁ φ₁ ε₂ φ₂
  · obtain ⟨c₁, c₂, h⟩ := h
    have ha' : herm σ (g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) (g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) =
        0 := by rw [herm_smul_smul]; exact ha
    exact tv_mem_of_smul_eq hσ.invol hg rfl ha ha' hc
      (hT _ ha' c hc (Or.inl ⟨c₁, c₂, h⟩))
  · obtain ⟨c₃, c₄, h⟩ := h
    have ha' : herm σ (g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) (g • vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) =
        0 := by rw [herm_smul_smul]; exact ha
    exact tv_mem_of_smul_eq hσ.invol hg rfl ha ha' hc
      (hT _ ha' c hc (Or.inr ⟨c₃, c₄, h⟩))

end Generation


structure ZRel (σ : K ≃+* K) {n : ℕ} (e₁ f₁ e₂ f₂ z : Fin n → K) : Prop where
  e1z : herm σ e₁ z = 0
  f1z : herm σ f₁ z = 0
  e2z : herm σ e₂ z = 0
  f2z : herm σ f₂ z = 0
  ze1 : herm σ z e₁ = 0
  zf1 : herm σ z f₁ = 0
  ze2 : herm σ z e₂ = 0
  zf2 : herm σ z f₂ = 0

section Kill

variable (hσ : IsUnitaryInvolution σ) (hF : FrameRel σ e₁ f₁ e₂ f₂) (Ĥ : Subgroup (SUid σ n))
  {z : Fin n → K}

include hσ

theorem kill_with
    (hE : ∀ e : Fin n → K, (e = e₁ ∨ e = f₁ ∨ e = e₂ ∨ e = f₂) → ∀ (ν c : K)
      (hee : herm σ e e = 0) (hey : herm σ e (ν • z) = 0)
      (hc : c + σ c = -herm σ (ν • z) (ν • z)), eichler hσ.invol hee hey hc ∈ Ĥ)
    {e : Fin n → K} (he : e = e₁ ∨ e = f₁ ∨ e = e₂ ∨ e = f₂) (hee : herm σ e e = 0)
    (hez : herm σ e z = 0) (hSpe : Sp4 e₁ f₁ e₂ f₂ e) {a : Fin n → K} {c₅ : K} {V : Fin n → K}
    (hV : Sp4 e₁ f₁ e₂ f₂ V) (hα : a = V + c₅ • z) (hδ : herm σ e a ≠ 0) :
    ∃ g ∈ Ĥ, Sp4 e₁ f₁ e₂ f₂ (g • a) := by
  set δ := herm σ e a with hδdef
  set ν : K := -c₅ / δ with hν
  have hey : herm σ e (ν • z) = 0 := by rw [herm_smul_right, hez, mul_zero]
  have hfix : σ (-herm σ (ν • z) (ν • z)) = -herm σ (ν • z) (ν • z) := by
    rw [map_neg, herm_self_fixed σ hσ.invol]
  obtain ⟨c, hc⟩ := hσ.trace_surj _ hfix
  refine ⟨eichler hσ.invol hee hey hc, hE e he ν c hee hey hc, ?_⟩
  have key : ∀ (A V : Fin n → K) (δ μ' : K), A = V + c₅ • z →
      A + δ • (ν • z + c • e) - μ' • e = V + (δ * c - μ') • e + (c₅ + δ * ν) • z := by
    intro A V δ μ' hA
    rw [hA]
    module
  have hzero : c₅ + δ * ν = 0 := by rw [hν]; field_simp; ring
  rw [eichler_smul, key a V δ (herm σ (ν • z) a) hα, hzero, zero_smul, add_zero]
  exact hV.add (hSpe.smul _)

end Kill


section Final

variable (hσ : IsUnitaryInvolution σ) (hF : FrameRel σ e₁ f₁ e₂ f₂) (Ĥ : Subgroup (SUid σ n))
  {z : Fin n → K}

include hσ hF

theorem exists_smul_mem_sp4 (hZ : ZRel σ e₁ f₁ e₂ f₂ z) (hz0 : z ≠ 0 → herm σ z z ≠ 0)
    (hE : ∀ e : Fin n → K, (e = e₁ ∨ e = f₁ ∨ e = e₂ ∨ e = f₂) → ∀ (ν c : K)
      (hee : herm σ e e = 0) (hey : herm σ e (ν • z) = 0)
      (hc : c + σ c = -herm σ (ν • z) (ν • z)), eichler hσ.invol hee hey hc ∈ Ĥ)
    {a : Fin n → K} (ha : herm σ a a = 0) {ε₁ φ₁ ε₂ φ₂ c₅ : K}
    (hα : a = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ + c₅ • z) :
    ∃ g ∈ Ĥ, Sp4 e₁ f₁ e₂ f₂ (g • a) := by
  have hV : Sp4 e₁ f₁ e₂ f₂ (vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂) := ⟨ε₁, φ₁, ε₂, φ₂, rfl⟩
  by_cases h5 : c₅ • z = 0
  · exact ⟨1, Ĥ.one_mem, ⟨ε₁, φ₁, ε₂, φ₂, by rw [one_smul, hα, h5, add_zero]⟩⟩
  have hz : z ≠ 0 := fun h => h5 (by rw [h, smul_zero])
  have hc5 : c₅ ≠ 0 := fun h => h5 (by rw [h, zero_smul])
  have hε₀ := hz0 hz
  have hδ1 : herm σ e₁ a = φ₁ := by
    rw [hα, herm_add_right, herm_e1_vec4 hF, herm_smul_right, hZ.e1z, mul_zero, add_zero]
  have hδ2 : herm σ f₁ a = ε₁ := by
    rw [hα, herm_add_right, herm_f1_vec4 hF, herm_smul_right, hZ.f1z, mul_zero, add_zero]
  have hδ3 : herm σ e₂ a = φ₂ := by
    rw [hα, herm_add_right, herm_e2_vec4 hF, herm_smul_right, hZ.e2z, mul_zero, add_zero]
  have hδ4 : herm σ f₂ a = ε₂ := by
    rw [hα, herm_add_right, herm_f2_vec4 hF, herm_smul_right, hZ.f2z, mul_zero, add_zero]
  by_cases h1 : φ₁ = 0
  · by_cases h2 : ε₁ = 0
    · by_cases h3 : φ₂ = 0
      · by_cases h4 : ε₂ = 0
        · exfalso
          have : a = c₅ • z := by
            rw [hα, h1, h2, h3, h4]
            simp only [vec4]
            module
          rw [this, herm_smul_left, herm_smul_right] at ha
          exact mul_ne_zero ((map_ne_zero σ).2 hc5) (mul_ne_zero hc5 hε₀) ha
        · exact kill_with hσ Ĥ hE (Or.inr (Or.inr (Or.inr rfl))) hF.f2f2 hZ.f2z Sp4_f₂ hV hα
            (by rw [hδ4]; exact h4)
      · exact kill_with hσ Ĥ hE (Or.inr (Or.inr (Or.inl rfl))) hF.e2e2 hZ.e2z Sp4_e₂ hV hα
          (by rw [hδ3]; exact h3)
    · exact kill_with hσ Ĥ hE (Or.inr (Or.inl rfl)) hF.f1f1 hZ.f1z Sp4_f₁ hV hα
        (by rw [hδ2]; exact h2)
  · exact kill_with hσ Ĥ hE (Or.inl rfl) hF.e1e1 hZ.e1z Sp4_e₁ hV hα (by rw [hδ1]; exact h1)


theorem T_le_of_frame (hZ : ZRel σ e₁ f₁ e₂ f₂ z) (hz0 : z ≠ 0 → herm σ z z ≠ 0)
    (hspan : ∀ v : Fin n → K, ∃ ε₁ φ₁ ε₂ φ₂ c₅ : K,
      v = vec4 e₁ f₁ e₂ f₂ ε₁ φ₁ ε₂ φ₂ + c₅ • z)
    (hS1 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₁ x) • f₂ - (σ μ * herm σ f₂ x) • e₁)
    (hS2 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₂ x) • f₁ - (σ μ * herm σ f₁ x) • e₂)
    (hS3 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ e₁ x) • e₂ - (σ μ * herm σ e₂ x) • e₁)
    (hS4 : ∀ μ : K, ∃ g ∈ Ĥ, ∀ x, g • x = x + (μ * herm σ f₁ x) • f₂ - (σ μ * herm σ f₂ x) • f₁)
    (hT : ∀ (a : Fin n → K) (ha : herm σ a a = 0) (c : K) (hc : c + σ c = 0),
      ((∃ c₁ c₂ : K, a = vec4 e₁ f₁ e₂ f₂ c₁ c₂ 0 0) ∨
        (∃ c₃ c₄ : K, a = vec4 e₁ f₁ e₂ f₂ 0 0 c₃ c₄)) → tv hσ.invol ha hc ∈ Ĥ)
    (hE : ∀ e : Fin n → K, (e = e₁ ∨ e = f₁ ∨ e = e₂ ∨ e = f₂) → ∀ (ν c : K)
      (hee : herm σ e e = 0) (hey : herm σ e (ν • z) = 0)
      (hc : c + σ c = -herm σ (ν • z) (ν • z)), eichler hσ.invol hee hey hc ∈ Ĥ) :
    T σ n ≤ Ĥ := by
  show Subgroup.closure (tvSet σ n) ≤ Ĥ
  refine (Subgroup.closure_le Ĥ).2 ?_
  rintro t ⟨a, c, ha, hc, hta⟩
  have ht : t = tv hσ.invol ha hc := by
    apply ext_smul
    intro v
    rw [hta, tv_smul]
  rw [SetLike.mem_coe, ht]
  obtain ⟨ε₁, φ₁, ε₂, φ₂, c₅, hα⟩ := hspan a
  obtain ⟨g, hg, hSp⟩ := exists_smul_mem_sp4 hσ hF Ĥ hZ hz0 hE ha hα
  have ha' : herm σ (g • a) (g • a) = 0 := by rw [herm_smul_smul]; exact ha
  exact tv_mem_of_smul_eq hσ.invol hg rfl ha ha' hc
    (tv_mem_of_vec4 hσ hF Ĥ hS1 hS2 hS3 hS4 hT hSp ha' hc)

end Final

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Ub
