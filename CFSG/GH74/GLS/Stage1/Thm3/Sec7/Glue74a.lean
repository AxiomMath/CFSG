module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.TypeArg

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

omit [Finite G] in
theorem mem_normalizer_cj_iff {K : Subgroup G} {g w : G} :
    w ∈ normalizer ((M.cj K g : Subgroup G) : Set G) ↔ g * w * g⁻¹ ∈ normalizer (K : Set G) := by
  constructor
  · exact M.mem_normalizer_cj
  · intro hw
    rw [Subgroup.mem_normalizer_iff] at hw ⊢
    intro x
    have h1 := hw (g * x * g⁻¹)
    simp only [M.mem_cj]
    have e : g * (w * x * w⁻¹) * g⁻¹ = g * w * g⁻¹ * (g * x * g⁻¹) * (g * w * g⁻¹)⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem relIndex_cj (A B : Subgroup G) (g : G) :
    (M.cj A g).relIndex (M.cj B g) = A.relIndex B := by
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  unfold M.cj
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hsurj]

namespace Cfg7

theorem perm_pigeon (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∀ c ∈ centralizer ({z} : Set G), ∀ c' ∈ centralizer ({z} : Set G),
      c ∈ normalizer (K₁ : Set G) ∨ c' ∈ normalizer (K₁ : Set G) ∨
        c⁻¹ * c' ∈ normalizer (K₁ : Set G) := by
  intro c hc c' hc'
  have hM := h.m4 hII
  rcases hM.perm c hc with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Or.inl (M.cj_eq_iff_normalizer.1 h1)
  · rcases hM.perm c' hc' with ⟨h1', -⟩ | ⟨h1', h2'⟩
    · exact Or.inr (Or.inl (M.cj_eq_iff_normalizer.1 h1'))
    · right; right
      apply M.cj_eq_iff_normalizer.1
      have e1 : M.cj K₁ c⁻¹ = K₂ := by
        rw [← h2, M.cj_cj_inv]
      calc M.cj K₁ (c⁻¹ * c') = M.cj (M.cj K₁ c⁻¹) c' := (M.cj_cj c⁻¹ c' K₁).symm
        _ = M.cj K₂ c' := by rw [e1]
        _ = K₁ := h2'

theorem z_mem_normalizer (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : z ∈ normalizer (K : Set G) := by
  have hKC : K ≤ centralizer ({z} : Set G) := h.K_le_C hII hK
  have hcomm : ∀ x ∈ K, z * x = x * z := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKC hx)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : z * x * z⁻¹ = x := by rw [hcomm x hx]; group
    rwa [this]
  · intro hx
    have h2 : z * (z * x * z⁻¹) = (z * x * z⁻¹) * z := hcomm _ hx
    have : z * x * z⁻¹ = x := by
      have e : z * x * z⁻¹ = z⁻¹ * (z * (z * x * z⁻¹)) := by group
      rw [e, h2]; group
    rwa [this] at hx

theorem exists_E₂ (hII : II4_4_4_center) (h41 : Prop4_1) (h : Cfg7 G z S K₁ K₂ t u q) :
    ∃ E₂ : Subgroup G, E₂ ≤ S ⊓ centralizer ({t} : Set G) ∧
      (∀ e ∈ S ⊓ centralizer ({t} : Set G), ∀ e' ∈ S ⊓ centralizer ({t} : Set G),
        e ∈ E₂ ∨ e' ∈ E₂ ∨ e⁻¹ * e' ∈ E₂) ∧ z ∉ E₂ ∧ t ∈ E₂ := by
  obtain ⟨g, hg⟩ := M.exists_conj_inv h.ch.t_conj
  have hM := h.m4 hII
  have hzt : g * t * g⁻¹ = z := by rw [← hg]; group
  have htC : t ∈ centralizer ({z} : Set G) := hM.S_syl.1 h.ch.t_mem
  have hCe : ∀ e ∈ S ⊓ centralizer ({t} : Set G), g * e * g⁻¹ ∈ centralizer ({z} : Set G) := by
    intro e he
    have het : e * t = t * e := Subgroup.mem_centralizer_singleton_iff.1 he.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
    calc g * e * g⁻¹ * (g * t * g⁻¹) = g * (e * t) * g⁻¹ := by group
      _ = g * (t * e) * g⁻¹ := by rw [het]
      _ = g * t * g⁻¹ * (g * e * g⁻¹) := by group
  refine ⟨(S ⊓ centralizer ({t} : Set G)) ⊓ normalizer ((M.cj K₁ g : Subgroup G) : Set G),
    inf_le_left, ?_, ?_, ?_⟩
  · intro e he e' he'
    have hp := h.perm_pigeon hII _ (hCe e he) _ (hCe e' he')
    rcases hp with h1 | h1 | h1
    · exact Or.inl ⟨he, mem_normalizer_cj_iff.2 h1⟩
    · exact Or.inr (Or.inl ⟨he', mem_normalizer_cj_iff.2 h1⟩)
    · refine Or.inr (Or.inr ⟨(S ⊓ centralizer ({t} : Set G)).mul_mem
        ((S ⊓ centralizer ({t} : Set G)).inv_mem he) he', mem_normalizer_cj_iff.2 ?_⟩)
      have e2 : g * (e⁻¹ * e') * g⁻¹ = (g * e * g⁻¹)⁻¹ * (g * e' * g⁻¹) := by group
      rw [e2]; exact h1
  · intro hz
    have hint := (h41 G z S K₁ K₂ h.std.std).2.2 t htC h.ch.t_conj h.ch.t_swap g hg
    have hint' := (interchanges_iff z).1 hint
    simp only [← cj_eq_conjugate] at hint'
    have h1 : M.cj (M.cj K₁ g) z = M.cj K₁ g := M.cj_eq_iff_normalizer.2 hz.2
    have h2 : M.cj K₁ g = M.cj K₂ g := h1.symm.trans hint'.1
    have h3 := congrArg (fun H => M.cj H g⁻¹) h2
    simp only [M.cj_cj_inv] at h3
    exact h.std.std.ne h3
  · refine ⟨⟨h.ch.t_mem, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩, ?_⟩
    apply mem_normalizer_cj_iff.2
    rw [hzt]
    exact h.z_mem_normalizer hII (Or.inl rfl)

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
