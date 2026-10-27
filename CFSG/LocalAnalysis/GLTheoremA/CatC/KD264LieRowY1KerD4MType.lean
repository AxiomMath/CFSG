module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerD4MPlane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

open QuadraticMap Module CFSG.GroupTheory.WeirSylow

noncomputable section

section TypeCalc

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

structure OIdem (Q : QuadraticForm K V) (e : Module.End K V) : Prop where
  idem : e * e = e
  adj : ∀ u v, polar Q (e u) v = polar Q u (e v)

@[expose] def IsCubePlane (Q : QuadraticForm K V) (W : Submodule K V) : Prop :=
  finrank K W = 2 ∧ ∃ T : V →ₗ[K] V, (∀ x ∈ W, T x ∈ W) ∧ (∀ x ∈ W, T (T x) + T x + x = 0) ∧
    ∀ x, Q (T x) = Q x

variable {Q : QuadraticForm K V}

theorem OIdem.add {e f : Module.End K V} (he : OIdem Q e) (hf : OIdem Q f) (hef : e * f = 0)
    (hfe : f * e = 0) : OIdem Q (e + f) :=
  ⟨add_idem he.idem hf.idem hef hfe, fun u v => by
    simp only [LinearMap.add_apply, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      he.adj, hf.adj]⟩

theorem OIdem.nondeg_comp {e : Module.End K V} (he : OIdem Q e)
    (hnd : (polarBilin Q).Nondegenerate) :
    (polarBilin (Q.comp (LinearMap.range e).subtype)).Nondegenerate :=
  nondeg_comp_subtype' (nondeg_range hnd he.idem he.adj)

variable [Finite K] [FiniteDimensional K V]

theorem plus_of_two_planes (h3 : (3 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    {e f : Module.End K V} (he : OIdem Q e) (hf : OIdem Q f) (hef : e * f = 0) (hfe : f * e = 0)
    (pe : IsCubePlane Q (LinearMap.range e)) (pf : IsCubePlane Q (LinearMap.range f)) :
    IsPlusType (Q.comp (LinearMap.range (e + f)).subtype) := by
  rw [isPlusType_congr_eq (range_add_eq_sup he.idem hf.idem hef hfe),
    isPlusType_sup_iff' (disjoint_range_of_orth he.idem hef) (polar_range_orth he.adj hef)
      (he.nondeg_comp hnd) (hf.nondeg_comp hnd) (d₁ := 1) (d₂ := 1) le_rfl le_rfl
      (by rw [pe.1]) (by rw [pf.1])]
  obtain ⟨hpe, T, hTW, hT, hTQ⟩ := pe
  obtain ⟨hpf, T', hTW', hT', hTQ'⟩ := pf
  rw [plane_plus_iff h3 hpe hTW hT hTQ (nondeg_range hnd he.idem he.adj),
    plane_plus_iff h3 hpf hTW' hT' hTQ' (nondeg_range hnd hf.idem hf.adj)]

theorem plus_split (hnd : (polarBilin Q).Nondegenerate) {u w : Module.End K V} (hu : OIdem Q u)
    (hw : OIdem Q w) (huw : u * w = 0) (hwu : w * u = 0) (hsum : u + w = 1) {d₁ d₂ : ℕ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (h₁ : finrank K (LinearMap.range u) = 2 * d₁)
    (h₂ : finrank K (LinearMap.range w) = 2 * d₂) :
    IsPlusType Q ↔ (IsPlusType (Q.comp (LinearMap.range u).subtype) ↔
      IsPlusType (Q.comp (LinearMap.range w).subtype)) := by
  have htop : LinearMap.range u ⊔ LinearMap.range w = ⊤ := by
    rw [← range_add_eq_sup hu.idem hw.idem huw hwu, hsum]
    exact LinearMap.range_eq_top.2 (fun v => ⟨v, rfl⟩)
  let iso : Q.IsometryEquiv (Q.comp (⊤ : Submodule K V).subtype) :=
    { toLinearEquiv := Submodule.topEquiv.symm
      map_app' := fun x => by simp [QuadraticMap.comp_apply] }
  rw [isPlusType_congr iso, isPlusType_congr_eq htop.symm,
    isPlusType_sup_iff' (disjoint_range_of_orth hu.idem huw) (polar_range_orth hu.adj huw)
      (hu.nondeg_comp hnd) (hw.nondeg_comp hnd) hd₁ hd₂ h₁ h₂]

theorem not_plus_of_split (h3 : (3 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hnp : ¬ IsPlusType Q) {u w₁ w₂ : Module.End K V} (hu : OIdem Q u) (h₁ : OIdem Q w₁)
    (h₂ : OIdem Q w₂) (hu₁ : u * w₁ = 0) (h₁u : w₁ * u = 0) (hu₂ : u * w₂ = 0)
    (h₂u : w₂ * u = 0) (h₁₂ : w₁ * w₂ = 0) (h₂₁ : w₂ * w₁ = 0) (hsum : u + (w₁ + w₂) = 1)
    {d : ℕ} (hd : 1 ≤ d) (hdu : finrank K (LinearMap.range u) = 2 * d)
    (p₁ : IsCubePlane Q (LinearMap.range w₁)) (p₂ : IsCubePlane Q (LinearMap.range w₂)) :
    ¬ IsPlusType (Q.comp (LinearMap.range u).subtype) := by
  have hw : OIdem Q (w₁ + w₂) := h₁.add h₂ h₁₂ h₂₁
  have huw : u * (w₁ + w₂) = 0 := by rw [mul_add, hu₁, hu₂, add_zero]
  have hwu : (w₁ + w₂) * u = 0 := by rw [add_mul, h₁u, h₂u, add_zero]
  have hdw : finrank K (LinearMap.range (w₁ + w₂)) = 2 * 2 := by
    rw [finrank_range_add h₁.idem h₂.idem h₁₂ h₂₁, p₁.1, p₂.1]
  have hplus := plus_of_two_planes h3 hnd h₁ h₂ h₁₂ h₂₁ p₁ p₂
  have hsplit := plus_split hnd hu hw huw hwu hsum hd (le_refl _ |>.trans (by norm_num : 1 ≤ 2))
    hdu hdw
  intro hU
  exact hnp (hsplit.2 ⟨fun _ => hplus, fun _ => hU⟩)

theorem false_of_four_planes (h3 : (3 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hnp : ¬ IsPlusType Q) {w₁ w₂ w₃ w₄ : Module.End K V} (h₁ : OIdem Q w₁) (h₂ : OIdem Q w₂)
    (h₃ : OIdem Q w₃) (h₄ : OIdem Q w₄) (h₁₂ : w₁ * w₂ = 0) (h₂₁ : w₂ * w₁ = 0)
    (h₁₃ : w₁ * w₃ = 0) (h₃₁ : w₃ * w₁ = 0) (h₁₄ : w₁ * w₄ = 0) (h₄₁ : w₄ * w₁ = 0)
    (h₂₃ : w₂ * w₃ = 0) (h₃₂ : w₃ * w₂ = 0) (h₂₄ : w₂ * w₄ = 0) (h₄₂ : w₄ * w₂ = 0)
    (h₃₄ : w₃ * w₄ = 0) (h₄₃ : w₄ * w₃ = 0) (hsum : (w₁ + w₂) + (w₃ + w₄) = 1)
    (p₁ : IsCubePlane Q (LinearMap.range w₁)) (p₂ : IsCubePlane Q (LinearMap.range w₂))
    (p₃ : IsCubePlane Q (LinearMap.range w₃)) (p₄ : IsCubePlane Q (LinearMap.range w₄)) :
    False := by
  have hA : OIdem Q (w₁ + w₂) := h₁.add h₂ h₁₂ h₂₁
  have hB : OIdem Q (w₃ + w₄) := h₃.add h₄ h₃₄ h₄₃
  have hAB : (w₁ + w₂) * (w₃ + w₄) = 0 := by
    rw [add_mul, mul_add, mul_add, h₁₃, h₁₄, h₂₃, h₂₄]
    simp
  have hBA : (w₃ + w₄) * (w₁ + w₂) = 0 := by
    rw [add_mul, mul_add, mul_add, h₃₁, h₃₂, h₄₁, h₄₂]
    simp
  have hdA : finrank K (LinearMap.range (w₁ + w₂)) = 2 * 2 := by
    rw [finrank_range_add h₁.idem h₂.idem h₁₂ h₂₁, p₁.1, p₂.1]
  have hdB : finrank K (LinearMap.range (w₃ + w₄)) = 2 * 2 := by
    rw [finrank_range_add h₃.idem h₄.idem h₃₄ h₄₃, p₃.1, p₄.1]
  have hplA := plus_of_two_planes h3 hnd h₁ h₂ h₁₂ h₂₁ p₁ p₂
  have hplB := plus_of_two_planes h3 hnd h₃ h₄ h₃₄ h₄₃ p₃ p₄
  have hsplit := plus_split hnd hA hB hAB hBA hsum (by norm_num : 1 ≤ 2) (by norm_num : 1 ≤ 2)
    hdA hdB
  exact hnp (hsplit.2 ⟨fun _ => hplB, fun _ => hplA⟩)

end TypeCalc

end

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KD4

end
