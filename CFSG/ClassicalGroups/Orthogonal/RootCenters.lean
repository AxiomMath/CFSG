module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def IsRootCenter (H : Subgroup (V ≃ₗ[K] V)) (u : V) : Prop :=
  u ≠ 0 ∧ Q u = 0 ∧ ∀ w, polar Q u w = 0 → eichler Q u w ∈ H

theorem IsRootCenter.smul {H : Subgroup (V ≃ₗ[K] V)} {u : V} (h : IsRootCenter Q H u) {c : K}
    (hc : c ≠ 0) : IsRootCenter Q H (c • u) := by
  obtain ⟨hu0, hQ, hE⟩ := h
  refine ⟨smul_ne_zero hc hu0, by rw [map_smul_eq_sq, hQ, mul_zero], fun w hw => ?_⟩
  rw [eichler_smul_left]
  apply hE
  rw [polar_smul_right_eq]
  rw [polar_smul_left_eq] at hw
  rcases mul_eq_zero.mp hw with h0 | h0
  · exact absurd h0 hc
  · rw [h0, mul_zero]

theorem IsRootCenter.map {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {u : V} (h : IsRootCenter Q H u)
    {g : V ≃ₗ[K] V} (hg : g ∈ H) : IsRootCenter Q H (g u) := by
  obtain ⟨hu0, hQ, hE⟩ := h
  have hgO := hH hg
  refine ⟨fun h0 => hu0 (g.injective (by rw [h0, map_zero])), by rw [map_of_mem hgO, hQ],
    fun w hw => ?_⟩
  have hw' : polar Q u (g⁻¹ w) = 0 := by
    rw [← polar_map_of_mem hgO, LinearEquiv.apply_inv_apply']
    exact hw
  have h1 := eichler_conj hgO u (g⁻¹ w)
  rw [LinearEquiv.apply_inv_apply'] at h1
  rw [← h1]
  exact H.mul_mem (H.mul_mem hg (hE _ hw')) (H.inv_mem hg)

theorem IsRootCenter.of_opposite {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {a b c : V} (ha : IsRootCenter Q H a)
    (hb : IsRootCenter Q H b) (hab : polar Q a b ≠ 0) (hcQ : Q c = 0)
    (hca : polar Q a c ≠ 0) : IsRootCenter Q H c := by
  have hlam : polar Q a b / polar Q a c ≠ 0 := div_ne_zero hab hca
  set c' := (polar Q a b / polar Q a c) • c with hc'
  have hc'Q : Q c' = 0 := by rw [hc', map_smul_eq_sq, hcQ, mul_zero]
  have hac' : polar Q a c' = polar Q a b := by
    rw [hc', polar_smul_right_eq]
    field_simp
  have hw : polar Q a ((polar Q a b)⁻¹ • (c' - b)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hac', sub_self, mul_zero]
  have hg : eichler Q a ((polar Q a b)⁻¹ • (c' - b)) ∈ H := ha.2.2 _ hw
  have hmap : eichler Q a ((polar Q a b)⁻¹ • (c' - b)) b = c' :=
    eichler_apply_eq_of_polar_eq ha.2.1 (by rw [hb.2.1, hc'Q]) rfl hac' hab
  have hc'root : IsRootCenter Q H c' := by
    rw [← hmap]
    exact hb.map hH hg
  have hcc : c = (polar Q a b / polar Q a c)⁻¹ • c' := by
    rw [hc', smul_smul, inv_mul_cancel₀ hlam, one_smul]
  rw [hcc]
  exact hc'root.smul (inv_ne_zero hlam)

theorem eichler_mem_of_conj {H : Subgroup (V ≃ₗ[K] V)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[K] V} (hg : g ∈ H) {u w : V}
    (h : eichler Q u w ∈ H) : eichler Q (g u) (g w) ∈ H := by
  rw [← eichler_conj (hH hg) u w]
  exact H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)

theorem IsRootCenter.of_span {H : Subgroup (V ≃ₗ[K] V)} {e : V} (he0 : e ≠ 0) (heQ : Q e = 0)
    (S : Set V) (hS : ∀ w ∈ S, polar Q e w = 0 ∧ eichler Q e w ∈ H)
    (hspan : ∀ w, polar Q e w = 0 → w ∈ AddSubgroup.closure (S ∪ {e})) :
    IsRootCenter Q H e := by
  refine ⟨he0, heQ, fun w hw => ?_⟩
  have key : ∀ w ∈ AddSubgroup.closure (S ∪ {e}), polar Q e w = 0 ∧ eichler Q e w ∈ H := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hS x hx
      · rw [Set.mem_singleton_iff.mp hx]
        refine ⟨polar_self_eq_zero heQ, ?_⟩
        have := eichler_add_smul_self heQ 0 1
        rw [zero_add, one_smul, eichler_zero_right] at this
        rw [this]
        exact H.one_mem
    | zero => exact ⟨polar_zero_right Q e, by rw [eichler_zero_right]; exact H.one_mem⟩
    | add x y _ _ hx hy =>
      refine ⟨by rw [polar_add_right, hx.1, hy.1, add_zero], ?_⟩
      rw [← eichler_mul hx.1 hy.1]
      exact H.mul_mem hx.2 hy.2
    | neg x _ hx =>
      refine ⟨by rw [polar_neg_right, hx.1, neg_zero], ?_⟩
      rw [← eichler_inv hx.1]
      exact H.inv_mem hx.2
  exact (key w (hspan w hw)).2

theorem elementaryGroup_le_of_hypPair (hQ : (polarBilin Q).Nondegenerate)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (P : HypPair Q) (he : IsRootCenter Q H P.e) (hf : IsRootCenter Q H P.f) :
    elementaryGroup Q ≤ H := by
  have hpef : polar Q P.e P.f ≠ 0 := by rw [P.polar_ef]; exact one_ne_zero
  have hpfe : polar Q P.f P.e ≠ 0 := by rw [P.polar_fe]; exact one_ne_zero
  have key : ∀ c : V, c ≠ 0 → Q c = 0 → IsRootCenter Q H c := by
    intro c hc0 hcQ
    by_cases h1 : polar Q P.f c ≠ 0
    · exact IsRootCenter.of_opposite hH hf he hpfe hcQ h1
    by_cases h2 : polar Q P.e c ≠ 0
    · exact IsRootCenter.of_opposite hH he hf hpef hcQ h2
    push Not at h1 h2
    have hcperp : c ∈ P.perp := HypPair.mem_perp.2 ⟨h2, h1⟩
    obtain ⟨h, hh, hch⟩ :=
      (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hcperp hc0
    set h' := (polar Q c h)⁻¹ • h with hh'def
    have hh' : h' ∈ P.perp := P.perp.smul_mem _ hh
    have hch' : polar Q c h' = 1 := by rw [hh'def, polar_smul_right_eq, inv_mul_cancel₀ hch]
    set P' := HypPair.ofPolarEqOne hcQ hch' with hP'
    have hf'perp : P'.f ∈ P.perp := by
      rw [hP', HypPair.ofPolarEqOne_f]
      exact P.perp.sub_mem hh' (P.perp.smul_mem _ hcperp)
    have hperp := HypPair.mem_perp.1 hf'perp
    have he''Q : Q (P.e + P'.f) = 0 := by
      rw [QuadraticMap.map_add Q, P.Q_e, P'.Q_f, hperp.1]
      simp
    have he''f : polar Q P.f (P.e + P'.f) = 1 := by
      rw [polar_add_right, P.polar_fe, hperp.2]
      simp
    have he''root : IsRootCenter Q H (P.e + P'.f) :=
      IsRootCenter.of_opposite hH hf he hpfe he''Q (by rw [he''f]; exact one_ne_zero)
    have hcf' : polar Q c P'.f = 1 := P'.polar_ef
    have hpol : polar Q (P.e + P'.f) c ≠ 0 := by
      rw [polar_add_left, h2, zero_add, polar_comm, hcf']
      exact one_ne_zero
    have hpf : polar Q (P.e + P'.f) P.f ≠ 0 := by
      rw [polar_comm, he''f]
      exact one_ne_zero
    exact IsRootCenter.of_opposite hH he''root hf hpf hcQ hpol
  refine (Subgroup.closure_le H).2 ?_
  rintro _ ⟨u, w, hu, hw, rfl⟩
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact H.one_mem
  · exact (key u hu0 hu).2.2 w hw

end CFSG.ClassicalGroups.Orthogonal
