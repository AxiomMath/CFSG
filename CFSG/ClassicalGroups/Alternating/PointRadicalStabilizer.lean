module

public import CFSG.ClassicalGroups.Alternating.PointRadicalChar
public import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
public import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open CFSG.Open CFSG.ClassicalGroups.PCoreSection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

@[expose] def pointStabilizer (B : BilinForm K V) (u : V) : Subgroup (Gsp B) where
  carrier := {g | ∃ c : K, g.app u = c • u}
  one_mem' := ⟨1, by rw [Gsp.app_one, one_smul]⟩
  mul_mem' := by
    rintro g h ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨d * c, by rw [Gsp.app_mul, hd, Gsp.map_smul, hc, smul_smul]⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    by_cases hc0 : c = 0
    · have hu : u = 0 := by
        rw [← Gsp.app_inv_app g u, hc, hc0, zero_smul, Gsp.map_zero']
      exact ⟨1, by rw [hu, Gsp.map_zero', smul_zero]⟩
    · refine ⟨c⁻¹, ?_⟩
      conv_lhs => rw [← inv_smul_smul₀ hc0 u]
      rw [← hc, Gsp.map_smul, Gsp.app_inv_app]

theorem mem_pointStabilizer {u : V} {g : Gsp B} :
    g ∈ pointStabilizer B u ↔ ∃ c : K, g.app u = c • u := Iff.rfl

theorem isLinearAction_Gsp (B : BilinForm K V) :
    IsLinearAction K (fun (g : Gsp B) (x : V) => g.app x) :=
  ⟨Gsp.app_one, Gsp.app_mul, Gsp.map_add, Gsp.map_smul⟩

theorem Gsp.ne_zero_of_app_eq_smul {u : V} (hu : u ≠ 0) {g : Gsp B} {c : K}
    (hc : g.app u = c • u) : c ≠ 0 := by
  rintro rfl
  apply hu
  rw [← Gsp.app_inv_app g u, hc, zero_smul, Gsp.map_zero']

private theorem mem_orth_span_iff (hB : B.IsAlt) {u x : V} :
    x ∈ B.orthogonal (Submodule.span K {u}) ↔ B x u = 0 := by
  have hflip : B x u = 0 ↔ B u x = 0 := by
    rw [← hB.neg_eq u x, neg_eq_zero]
  rw [hflip, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact h u (Submodule.mem_span_singleton_self u)
  · intro h n hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
    show B (a • u) x = 0
    rw [map_smul, LinearMap.smul_apply, h, smul_zero]

theorem app_mem_perp_of_mem_pointStabilizer (hB : B.IsAlt) {u : V} (hu : u ≠ 0) {s : Gsp B}
    (hs : s ∈ pointStabilizer B u) {x : V} (hx : B x u = 0) : B (s.app x) u = 0 := by
  obtain ⟨c, hc⟩ := hs
  have hc0 := Gsp.ne_zero_of_app_eq_smul hu hc
  have h1 : B (s.app x) (s.app u) = 0 := by rw [Gsp.form_app, hx]
  rw [hc, map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.mp h1).resolve_left hc0

theorem eq_span_or_eq_perp [FiniteDimensional K V] (hB : B.IsAlt) (hBn : B.Nondegenerate)
    {u : V} (X : Submodule K V) (hLX : Submodule.span K {u} ≤ X)
    (hXP : X ≤ B.orthogonal (Submodule.span K {u}))
    (hXinv : ∀ s ∈ pointStabilizer B u, ∀ x ∈ X, s.app x ∈ X) :
    X = Submodule.span K {u} ∨ X = B.orthogonal (Submodule.span K {u}) := by
  by_cases hXL : X = Submodule.span K {u}
  · exact Or.inl hXL
  refine Or.inr (le_antisymm hXP ?_)
  obtain ⟨y, hyX, hyL⟩ : ∃ y ∈ X, y ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    exact hXL (le_antisymm hcon hLX)
  obtain ⟨z₀, hz₀P, hz₀⟩ : ∃ z ∈ B.orthogonal (Submodule.span K {u}), B y z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hyL
    rw [← LinearMap.BilinForm.orthogonal_orthogonal hBn hB.isRefl (Submodule.span K {u})]
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    show B n y = 0
    rw [← hB.neg_eq y n, hcon n hn, neg_zero]
  have key : ∀ z ∈ B.orthogonal (Submodule.span K {u}), B y z ≠ 0 → z ∈ X := by
    intro z hzP hyz
    have hzu : B z u = 0 := (mem_orth_span_iff hB).mp hzP
    have huz : B u z = 0 := by rw [← hB.neg_eq z u, hzu, neg_zero]
    have hT : Tsp hB z 1 ∈ pointStabilizer B u := ⟨1, by rw [Tsp_app, huz]; simp⟩
    have h1 := hXinv _ hT y hyX
    rw [Tsp_app] at h1
    have h2 : B y z • z ∈ X := by
      have := X.sub_mem h1 hyX
      simpa using this
    have h3 := X.smul_mem (B y z)⁻¹ h2
    rwa [smul_smul, inv_mul_cancel₀ hyz, one_smul] at h3
  intro a haP
  by_cases hya : B y a = 0
  · have hz₁ : a + z₀ ∈ X :=
      key _ ((B.orthogonal (Submodule.span K {u})).add_mem haP hz₀P)
        (by rw [map_add, hya, zero_add]; exact hz₀)
    have := X.sub_mem hz₁ (key z₀ hz₀P hz₀)
    simpa using this
  · exact key a haP hya

theorem Lsp_eq_pCoreOf_pointStabilizer [FiniteDimensional K V] [Finite K] [CharP K 2]
    (hB : B.IsAlt) (hBn : B.Nondegenerate) {u : V} (hu : u ≠ 0) :
    Lsp B hB u = pCoreOf 2 (pointStabilizer B u) := by
  haveI : Finite V := Module.finite_of_finite K
  have hfix : ∀ g ∈ Lsp B hB u, g.app u = u := fun g hg =>
    apply_self_of_mem_pointRadical hB (mem_Lsp.mp hg)
  refine eq_pCoreOf_of_section (isLinearAction_Gsp B) (L := Submodule.span K {u})
    (P := B.orthogonal (Submodule.span K {u})) hu (fun s hs => hs) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun g hg => ⟨1, by rw [hfix g hg, one_smul]⟩
  · intro s hs n hn
    obtain ⟨c, hc⟩ := hs
    have := conj_mem_Lsp hB s hn
    rwa [hc, Lsp_smul hB (Gsp.ne_zero_of_app_eq_smul hu hc)] at this
  · intro x
    obtain ⟨w, c, hw, hx⟩ := mem_Lsp.mp x.2
    have hsq : x.1 * x.1 = 1 := by
      have : x.1 = Ssp hB u w c := Subtype.ext hx.symm
      rw [this]
      exact Ssp_mul_self hB hw c
    exact ⟨1, Subtype.ext (by simpa [pow_two] using hsq)⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [mem_orth_span_iff hB, map_smul, LinearMap.smul_apply, hB.self_eq_zero, smul_zero]
  · intro s hs x hx
    exact (mem_orth_span_iff hB).mpr
      (app_mem_perp_of_mem_pointStabilizer hB hu hs ((mem_orth_span_iff hB).mp hx))
  · intro s hs x hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨c, hc⟩ := hs
    rw [Gsp.map_smul, hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  · exact fun X hLX hXP hXinv => eq_span_or_eq_perp hB hBn X hLX hXP hXinv
  · intro g _ hgu hgx
    rw [mem_Lsp, mem_pointRadical_iff hB hBn hu]
    refine ⟨g.2, hgu, fun x hx => ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hgx x ((mem_orth_span_iff hB).mpr hx))
    exact ⟨c, hc.symm⟩

end CFSG.ClassicalGroups.Alternating
