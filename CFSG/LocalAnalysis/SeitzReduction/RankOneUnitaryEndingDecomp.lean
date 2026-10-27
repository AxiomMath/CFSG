module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoSetup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_normalizer_szA₁_of_mem_normalizer {G : Type*} [Group G] {T₁ : Subgroup G} {d : G}
    (hd : d ∈ normalizer (T₁ : Set G)) : d ∈ normalizer (szA₁ T₁ : Set G) := by
  have key : ∀ c ∈ normalizer (T₁ : Set G), ∀ x ∈ szA₁ T₁, c * x * c⁻¹ ∈ szA₁ T₁ := by
    intro c hc x hx
    obtain ⟨hxT, hxC⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hc x).mp hxT, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : c⁻¹ * y * c⁻¹⁻¹ ∈ T₁ := (mem_normalizer_iff.mp (inv_mem hc) y).mp hy
    have e := mem_centralizer_iff.mp hxC _ hy'
    calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c⁻¹⁻¹) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * y * c⁻¹⁻¹)) * c⁻¹ := by rw [e]
      _ = c * x * c⁻¹ * y := by group
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => key d hd x hx, fun hx => ?_⟩
  have := key d⁻¹ (inv_mem hd) _ hx
  rwa [show d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x by group] at this

namespace U3RTorus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T₁ R₁ R₂ : Subgroup G}
  {d k : G}

omit [Finite G] in
theorem eq_bot_or_le_of_le (hT : U3RTorus T₁ R₁ t d k) {X : Subgroup G} (hX : X ≤ szA₁ T₁)
    (hdX : d ∈ normalizer (X : Set G)) : X = ⊥ ∨ szA₁ T₁ ≤ X := by
  rcases X.bot_or_exists_ne_one with h | ⟨b, hbX, hb1⟩
  · exact Or.inl h
  · refine Or.inr fun b' hb' => ?_
    by_cases hb'1 : b' = 1
    · rw [hb'1]
      exact one_mem _
    · obtain ⟨n, hn⟩ := hT.trans b (hX hbX) b' hb' hb1 hb'1
      have hm : (d ^ n)⁻¹ ∈ normalizer (X : Set G) := inv_mem (pow_mem hdX n)
      have := (mem_normalizer_iff.mp hm b).mp hbX
      rwa [inv_inv, hn] at this

theorem le_or_le_of_le (hT : U3RTorus T₁ R₁ t d k) (hR : U3R2 G L T₁ R₂ t f)
    (hdR : d ∈ normalizer (R₂ : Set G)) {X : Subgroup G} (hAX : szA₁ T₁ ≤ X) (hXR : X ≤ R₂)
    (hdX : d ∈ normalizer (X : Set G)) : X ≤ szA₁ T₁ ∨ R₂ ≤ X := by
  by_cases hle : X ≤ szA₁ T₁
  · exact Or.inl hle
  · refine Or.inr fun r hr => ?_
    obtain ⟨r₀, hr₀X, hr₀A⟩ := Set.not_subset.mp hle
    by_cases hrA : r ∈ szA₁ T₁
    · exact hAX hrA
    obtain ⟨n, -, hn⟩ := hR.sq_eq_conj_of_not_mem hT.comm_t hdR hT.trans (hXR hr₀X) hr₀A hr hrA
    have hDt : d ^ n * t = t * d ^ n := (Commute.pow_left hT.comm_t n).eq
    have hDt' : (d ^ n)⁻¹ * t = t * (d ^ n)⁻¹ := by
      calc (d ^ n)⁻¹ * t = (d ^ n)⁻¹ * (t * d ^ n) * (d ^ n)⁻¹ := by group
        _ = (d ^ n)⁻¹ * (d ^ n * t) * (d ^ n)⁻¹ := by rw [hDt]
        _ = t * (d ^ n)⁻¹ := by group
    set r₁ := (d ^ n)⁻¹ * r₀ * d ^ n with hr₁
    have hm : (d ^ n)⁻¹ ∈ normalizer (X : Set G) := inv_mem (pow_mem hdX n)
    have hr₁X : r₁ ∈ X := by
      have := (mem_normalizer_iff.mp hm r₀).mp hr₀X
      rwa [inv_inv] at this
    have hρ : r₁ * t * r₁⁻¹ * t = r * t * r⁻¹ * t := by
      rw [hn, hr₁]
      exact U3R2.rho_conj (D := d ^ n) hDt
    have h1 : r₁ * t * r₁⁻¹ = r * t * r⁻¹ := by
      rw [hR.conj_t_eq r₁, hR.conj_t_eq r, hρ]
    have hcomm : r₁⁻¹ * r * t = t * (r₁⁻¹ * r) := by
      calc r₁⁻¹ * r * t = r₁⁻¹ * (r * t * r⁻¹) * r := by group
        _ = r₁⁻¹ * (r₁ * t * r₁⁻¹) * r := by rw [h1]
        _ = t * (r₁⁻¹ * r) := by group
    have hA : r₁⁻¹ * r ∈ szA₁ T₁ := hR.rho_ker _ (mul_mem (inv_mem (hXR hr₁X)) hr) hcomm
    have := mul_mem hr₁X (hAX hA)
    rwa [mul_inv_cancel_left] at this

end U3RTorus

end CFSG.SeitzReduction.RankOne
