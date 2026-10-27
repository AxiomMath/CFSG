module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NMCase2

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.LieType.BorelTits

section Fixed

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

@[expose] def NM_theta (x : V) : V := x + T x + T (T x) + T (T (T x)) + T (T (T (T x)))

omit [CharP K 2] in
theorem NM_T5 (hT5 : T ^ 5 = 1) (x : V) : T (T (T (T (T x)))) = x := by
  have : (T ^ 5) x = T (T (T (T (T x)))) := by simp [pow_succ]
  rw [← this, hT5]
  rfl

omit [CharP K 2] in
theorem NM_T_theta (hT5 : T ^ 5 = 1) (x : V) : T (NM_theta T x) = NM_theta T x := by
  simp only [NM_theta, map_add, NM_T5 T hT5]
  abel

omit [CharP K 2] in
theorem NM_B_T_left_fix (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {y : V} (hy : T y = y) (x : V) :
    Φ.polar.β (T x) y = Φ.polar.β x y := by
  have := Φ.polar_map_of_Q (g := T) hTQ x y
  rwa [hy] at this

theorem NM_B_theta_left (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {y : V} (hy : T y = y) (g : V) :
    Φ.polar.β (NM_theta T g) y = Φ.polar.β g y := by
  have h1 := NM_B_T_left_fix Φ T hTQ hy
  have h2 : (2 : K) = 0 := NM_two_eq_zero
  simp only [NM_theta, Φ.polar.add_left, h1]
  linear_combination (2 * Φ.polar.β g y) * h2

theorem NM_B_theta_right (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {y : V} (hy : T y = y) (g : V) :
    Φ.polar.β y (NM_theta T g) = Φ.polar.β y g := by
  rw [Φ.polar_symm, NM_B_theta_left Φ T hTQ hy, Φ.polar_symm]

omit [CharP K 2] in
theorem NM_eichler_comm_fix (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {u w : V} (hu : T u = u) (hw : T w = w)
    (v : V) : Φ.eichler u w (T v) = T (Φ.eichler u w v) := by
  have h1 : Φ.polar.β u (T v) = Φ.polar.β u v := by
    have := Φ.polar_map_of_Q (g := T) hTQ u v
    rwa [hu] at this
  have h2 : Φ.polar.β w (T v) = Φ.polar.β w v := by
    have := Φ.polar_map_of_Q (g := T) hTQ w v
    rwa [hw] at this
  simp only [QuadForm.eichler_apply, map_add, map_sub, map_smul, hu, hw, h1, h2]

omit [CharP K 2] in
theorem NM_exists_dual [FiniteDimensional K V] {x y : V} (hxy : ∀ c : K, x ≠ c • y) :
    ∃ g, Φ.polar.β g x = 1 ∧ Φ.polar.β g y = 0 := by
  have h : ∃ g, Φ.polar.β g y = 0 ∧ Φ.polar.β g x ≠ 0 := by
    by_contra! hc
    have hmem : x ∈ Φ.polar.perp (Φ.polar.perp (K ∙ y)) := fun g hg => by
      exact hc g (by rw [Φ.polar_symm]; exact Φ.polar.mem_perp_span_singleton.mp hg)
    rw [Φ.polar.perp_perp] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact hxy c hc.symm
  obtain ⟨g, hg1, hg2⟩ := h
  refine ⟨(Φ.polar.β g x)⁻¹ • g, ?_, ?_⟩
  · rw [Φ.polar_smul_left, inv_mul_cancel₀ hg2]
  · rw [Φ.polar_smul_left, hg1, mul_zero]

theorem NM_false_of_fixed [FiniteDimensional K V] (hT5 : T ^ 5 = 1)
    (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) (W : Submodule K V) (hWQ : ∀ w ∈ W, Φ.Q w = 0)
    (hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ W, Φ.eichler x y w ∈ W)
    (hfix : ∀ w ∈ W, T w = w) (hdim : 2 ≤ Module.finrank K W) : False := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  obtain ⟨f1, hf1W, hf10⟩ : ∃ f1 ∈ W, f1 ≠ 0 := by
    by_contra! h
    have : W = ⊥ := (Submodule.eq_bot_iff W).mpr h
    rw [this] at hdim
    simp at hdim
  obtain ⟨f2, hf2W, hf2⟩ : ∃ f2 ∈ W, f2 ∉ K ∙ f1 := by
    by_contra! h
    have h1 : W ≤ K ∙ f1 := h
    have := Submodule.finrank_mono h1
    rw [finrank_span_singleton hf10] at this
    omega
  obtain ⟨v', hv'⟩ : ∃ v', Φ.polar.β f1 v' ≠ 0 := by
    by_contra! h
    exact hf10 (Φ.polar.nondeg _ h)
  set v : V := (Φ.polar.β f1 v')⁻¹ • v' with hv
  have hBv : Φ.polar.β f1 v = 1 := by
    rw [hv, Φ.polar.smul_right, inv_mul_cancel₀ hv']
  set u' : V := NM_theta T v with hu'
  set c : K := Φ.Q u' with hc
  set u : V := u' + c • f1 with hu
  have hTf1 := hfix f1 hf1W
  have hTu' : T u' = u' := NM_T_theta T hT5 v
  have hTu : T u = u := by simp only [hu, map_add, map_smul, hTu', hTf1]
  have hf1u' : Φ.polar.β f1 u' = 1 := by
    rw [hu', NM_B_theta_right Φ T hTQ hTf1]
    exact hBv
  have hBf1f1 : Φ.polar.β f1 f1 = 0 := NM_B_eq_zero_of_mem Φ hWQ hf1W hf1W
  have hQf1 := hWQ f1 hf1W
  have hQu : Φ.Q u = 0 := by
    rw [hu, Φ.Q_add, Φ.Q_smul, hQf1, Φ.polar.smul_right, Φ.polar_symm u' f1, hf1u']
    linear_combination c * h2K
  have hf1u : Φ.polar.β f1 u = 1 := by
    rw [hu, Φ.polar.add_right, Φ.polar.smul_right, hBf1f1, hf1u']
    ring
  set f2' : V := f2 - Φ.polar.β f2 u • f1 with hf2'
  have hf2'W : f2' ∈ W := W.sub_mem hf2W (W.smul_mem _ hf1W)
  have hf2'u : Φ.polar.β f2' u = 0 := by
    rw [hf2', Φ.polar.β_sub_left, Φ.polar_smul_left, hf1u]
    ring
  have hf2'0 : ∀ c0 : K, f2' ≠ c0 • u := by
    intro c0 h
    have h0 := NM_B_eq_zero_of_mem Φ hWQ hf1W hf2'W
    rw [h, Φ.polar.smul_right, hf1u, mul_one] at h0
    rw [h0, zero_smul] at h
    apply hf2
    have : f2 = Φ.polar.β f2 u • f1 := by
      rw [hf2'] at h
      exact sub_eq_zero.mp h
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f1)
  obtain ⟨g0, hg0x, hg0y⟩ := NM_exists_dual Φ hf2'0
  set w : V := NM_theta T g0 with hw
  have hTw : T w = w := NM_T_theta T hT5 g0
  have hBwf2' : Φ.polar.β w f2' = 1 := by
    rw [hw, NM_B_theta_left Φ T hTQ (hfix f2' hf2'W) g0]
    exact hg0x
  have hBwu : Φ.polar.β w u = 0 := by
    rw [hw, NM_B_theta_left Φ T hTQ hTu g0]
    exact hg0y
  have hBuw : Φ.polar.β u w = 0 := by rw [Φ.polar_symm]; exact hBwu
  have hEf1 := hE u w hQu hBuw (NM_eichler_comm_fix Φ T hTQ hTu hTw) f1 hf1W
  have hBuf1 : Φ.polar.β u f1 = 1 := by rw [Φ.polar_symm]; exact hf1u
  have hz : w - (Φ.Q w + Φ.polar.β w f1) • u ∈ W := by
    have : Φ.eichler u w f1 - f1 = w - (Φ.Q w + Φ.polar.β w f1) • u := by
      rw [QuadForm.eichler_apply, hBuf1]
      module
    rw [← this]
    exact W.sub_mem hEf1 hf1W
  have hB0 := NM_B_eq_zero_of_mem Φ hWQ hz hf2'W
  rw [Φ.polar.β_sub_left, Φ.polar_smul_left, hBwf2', Φ.polar_symm u f2', hf2'u] at hB0
  simp at hB0

end Fixed

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
