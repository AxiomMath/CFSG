module

public import Mathlib

public section

namespace CFSG.LieType.BorelTits.Kempf

open scoped RealInnerProductSpace
open Metric

structure Data (G W E : Type*) [Group G] [Group W] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  act : W →* (E ≃ₗᵢ[ℝ] E)
  n : W → G
  B : Subgroup G
  D : Set E
  cover : ∀ x : E, ∃ w : W, ∃ y ∈ D, x = act w y
  bruhat : ∀ g : G, ∃ w : W, ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * n w * b₂

variable {G W E : Type*} [Group G] [Group W] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsScore (d : Data G W E) (f : G → E → ℝ) : Prop where
  usc : ∀ g, UpperSemicontinuous (f g)
  smul : ∀ g (t : ℝ) x, 0 ≤ t → f g (t • x) = t * f g x
  superadd : ∀ g x y, 0 < f g x → 0 < f g y → f g x + f g y ≤ f g (x + y)
  borel : ∀ g, ∀ b ∈ d.B, ∀ x ∈ d.D, 0 < f g x → f g x ≤ f (g * b) x
  weyl : ∀ g w x, f (g * d.n w) x = f g (d.act w x)

variable {d : Data G W E} {f : G → E → ℝ}

theorem IsScore.zero (hf : IsScore d f) (g : G) : f g 0 = 0 := by
  have := hf.smul g 0 0 le_rfl
  simpa using this

theorem exists_max [Finite G] [FiniteDimensional ℝ E] (hf : IsScore d f)
    (hpos : ∃ g x, 0 < f g x) :
    ∃ M : ℝ, 0 < M ∧ (∀ g x, ‖x‖ = 1 → f g x ≤ M) ∧
      ∃ g, ∃ x ∈ d.D, ‖x‖ = 1 ∧ f g x = M := by
  classical
  obtain ⟨g₀, x₀, hx₀⟩ := hpos
  have hx₀ne : x₀ ≠ 0 := by
    rintro rfl
    rw [hf.zero] at hx₀
    exact lt_irrefl _ hx₀
  have : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  have hnx₀ : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀ne
  have hunit : ‖‖x₀‖⁻¹ • x₀‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx₀.ne']
  have hne : (sphere (0 : E) 1).Nonempty := ⟨_, mem_sphere_zero_iff_norm.mpr hunit⟩
  have hmaxg : ∀ g, ∃ x ∈ sphere (0 : E) 1, IsMaxOn (f g) (sphere (0 : E) 1) x := fun g =>
    UpperSemicontinuousOn.exists_isMaxOn hne (isCompact_sphere (0 : E) 1)
      ((hf.usc g).upperSemicontinuousOn _)
  choose xg hxg hxgmax using hmaxg
  obtain ⟨g₁, hg₁⟩ := Finite.exists_max (fun g => f g (xg g))
  refine ⟨f g₁ (xg g₁), ?_, ?_, ?_⟩
  · have h1 : f g₀ (‖x₀‖⁻¹ • x₀) = ‖x₀‖⁻¹ * f g₀ x₀ := hf.smul _ _ _ (by positivity)
    have h2 : f g₀ (‖x₀‖⁻¹ • x₀) ≤ f g₀ (xg g₀) :=
      isMaxOn_iff.mp (hxgmax g₀) _ (mem_sphere_zero_iff_norm.mpr hunit)
    have h3 : 0 < ‖x₀‖⁻¹ * f g₀ x₀ := mul_pos (inv_pos.mpr hnx₀) hx₀
    linarith [hg₁ g₀]
  · intro g x hx
    have : f g x ≤ f g (xg g) :=
      isMaxOn_iff.mp (hxgmax g) _ (mem_sphere_zero_iff_norm.mpr hx)
    exact this.trans (hg₁ g)
  · obtain ⟨w, y, hyD, hy⟩ := d.cover (xg g₁)
    refine ⟨g₁ * d.n w, y, hyD, ?_, ?_⟩
    · have h := mem_sphere_zero_iff_norm.mp (hxg g₁)
      rw [hy, LinearIsometryEquiv.norm_map] at h
      exact h
    · rw [hf.weyl, ← hy]

theorem exists_better {g : G} (hf : IsScore d f) {M : ℝ} (hM : 0 < M) {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ y) (hfx : M ≤ f g x) (hfy : M ≤ f g y) :
    ∃ u : E, ‖u‖ = 1 ∧ M < f g u := by
  set z : E := (1 / 2 : ℝ) • (x + y) with hz
  have hfz : M ≤ f g z := by
    rw [hz, hf.smul g _ _ (by norm_num)]
    have := hf.superadd g x y (by linarith) (by linarith)
    linarith
  have hpar := parallelogram_law_with_norm ℝ x y
  have hdiff : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hsum : ‖x + y‖ < 2 := by
    rw [hx, hy] at hpar
    nlinarith [norm_nonneg (x + y), mul_pos hdiff hdiff]
  have hznorm : ‖z‖ < 1 := by
    rw [hz, norm_smul]
    have : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
    rw [this]
    linarith
  have hz0 : z ≠ 0 := by
    rintro h0
    rw [h0, hf.zero] at hfz
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzpos.ne']
  · rw [hf.smul g _ _ (by positivity)]
    have h1 : M < ‖z‖⁻¹ * M := by
      have : 1 < ‖z‖⁻¹ := (one_lt_inv₀ hzpos).mpr hznorm
      nlinarith
    have h2 : ‖z‖⁻¹ * M ≤ ‖z‖⁻¹ * f g z :=
      mul_le_mul_of_nonneg_left hfz (inv_nonneg.mpr (norm_nonneg _))
    linarith

theorem dominant_max_unique (hf : IsScore d f) {M : ℝ} (hM : 0 < M)
    (hmax : ∀ g x, ‖x‖ = 1 → f g x ≤ M)
    {g₁ g₂ : G} {x₁ x₂ : E} (hx₁ : x₁ ∈ d.D) (hx₂ : x₂ ∈ d.D)
    (hn₁ : ‖x₁‖ = 1) (hn₂ : ‖x₂‖ = 1) (hf₁ : f g₁ x₁ = M) (hf₂ : f g₂ x₂ = M)
    {w : W} {b₁ b₂ : G} (hb₁ : b₁ ∈ d.B) (hb₂ : b₂ ∈ d.B)
    (hg : g₁⁻¹ * g₂ = b₁ * d.n w * b₂) :
    x₁ = d.act w x₂ := by
  by_contra hne
  set k : G := g₁ * b₁ with hk
  have hk₁ : M ≤ f k x₁ := by
    have := hf.borel g₁ b₁ hb₁ x₁ hx₁ (by rw [hf₁]; exact hM)
    rw [hf₁] at this
    exact this
  have hk₂ : M ≤ f k (d.act w x₂) := by
    have hkn : k * d.n w = g₂ * b₂⁻¹ := by
      rw [hk]
      have : g₂ = g₁ * (b₁ * d.n w * b₂) := by rw [← hg]; group
      rw [this]
      group
    rw [← hf.weyl, hkn]
    have := hf.borel g₂ b₂⁻¹ (inv_mem hb₂) x₂ hx₂ (by rw [hf₂]; exact hM)
    rw [hf₂] at this
    exact this
  have hn₂' : ‖d.act w x₂‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact hn₂
  obtain ⟨u, hu, hfu⟩ := exists_better hf hM hn₁ hn₂' hne hk₁ hk₂
  exact absurd (hmax k u hu) (not_le.mpr hfu)

theorem conj_mem_of_invariant (hf : IsScore d f) {M : ℝ} (hM : 0 < M)
    (hmax : ∀ g x, ‖x‖ = 1 → f g x ≤ M) {g : G} {x : E} (hxD : x ∈ d.D) (hxn : ‖x‖ = 1)
    (hfx : f g x = M) {h : G} (hh : ∀ g' x', f (h * g') x' = f g' x') :
    ∃ w : W, d.act w x = x ∧ ∃ b₁ ∈ d.B, ∃ b₂ ∈ d.B, g⁻¹ * h * g = b₁ * d.n w * b₂ := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hbr⟩ := d.bruhat (g⁻¹ * h * g)
  refine ⟨w, ?_, b₁, hb₁, b₂, hb₂, hbr⟩
  have hf₂ : f (h * g) x = M := by rw [hh]; exact hfx
  have hg : g⁻¹ * (h * g) = b₁ * d.n w * b₂ := by rw [← hbr]; group
  exact (dominant_max_unique hf hM hmax hxD hxD hxn hxn hfx hf₂ hb₁ hb₂ hg).symm

end CFSG.LieType.BorelTits.Kempf
