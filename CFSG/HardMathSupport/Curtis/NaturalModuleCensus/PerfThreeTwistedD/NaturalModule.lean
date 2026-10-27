module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltPlusD.NMFixed

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.LieType.BorelTits

section Three

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

@[expose] def NM3_theta (x : V) : V := x + T x + T (T x)

omit [CharP K 2] in
theorem NM3_T3 (hT3 : T ^ 3 = 1) (x : V) : T (T (T x)) = x := by
  have : (T ^ 3) x = T (T (T x)) := by simp [pow_succ]
  rw [← this, hT3]
  rfl

omit [CharP K 2] in
theorem NM3_T_theta (hT3 : T ^ 3 = 1) (x : V) : T (NM3_theta T x) = NM3_theta T x := by
  simp only [NM3_theta, map_add, NM3_T3 T hT3]
  abel

theorem NM3_B_theta_left (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {y : V} (hy : T y = y) (g : V) :
    Φ.polar.β (NM3_theta T g) y = Φ.polar.β g y := by
  have h1 := NM_B_T_left_fix Φ T hTQ hy
  have h2 : (2 : K) = 0 := NM_two_eq_zero
  simp only [NM3_theta, Φ.polar.add_left, h1]
  linear_combination (Φ.polar.β g y) * h2

theorem NM3_B_theta_right (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {y : V} (hy : T y = y) (g : V) :
    Φ.polar.β y (NM3_theta T g) = Φ.polar.β y g := by
  rw [Φ.polar_symm, NM3_B_theta_left Φ T hTQ hy, Φ.polar_symm]

theorem NM3_false_of_fixed [FiniteDimensional K V] (hT3 : T ^ 3 = 1)
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
  set u' : V := NM3_theta T v with hu'
  set c : K := Φ.Q u' with hc
  set u : V := u' + c • f1 with hu
  have hTf1 := hfix f1 hf1W
  have hTu' : T u' = u' := NM3_T_theta T hT3 v
  have hTu : T u = u := by simp only [hu, map_add, map_smul, hTu', hTf1]
  have hf1u' : Φ.polar.β f1 u' = 1 := by
    rw [hu', NM3_B_theta_right Φ T hTQ hTf1]
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
  set w : V := NM3_theta T g0 with hw
  have hTw : T w = w := NM3_T_theta T hT3 g0
  have hBwf2' : Φ.polar.β w f2' = 1 := by
    rw [hw, NM3_B_theta_left Φ T hTQ (hfix f2' hf2'W) g0]
    exact hg0x
  have hBwu : Φ.polar.β w u = 0 := by
    rw [hw, NM3_B_theta_left Φ T hTQ hTu g0]
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

end Three

section Quadratic

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (Φ : QuadForm K V) (T : V →ₗ[K] V)

omit [CharP K 2] in
theorem NM3_B_right_two (hT3 : T ^ 3 = 1) (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) (x y : V) :
    Φ.polar.β x (T y) = Φ.polar.β (T (T x)) y := by
  have h := Φ.polar_map_of_Q (g := T) hTQ (T (T x)) y
  rwa [NM3_T3 T hT3] at h

theorem NM3_exists_u' (hT3 : T ^ 3 = 1) (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {f : V} (hf0 : f ≠ 0)
    (hf : T (T f) = T f + f) :
    ∃ u' : V, T (T u') = T u' + u' ∧ Φ.polar.β f u' = 1 := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  have hTf0 : T f ≠ 0 := fun h => hf0 (by rw [← NM3_T3 T hT3 f, h]; simp)
  obtain ⟨v', hv'⟩ : ∃ v', Φ.polar.β (T f) v' ≠ 0 := by
    by_contra! h
    exact hTf0 (Φ.polar.nondeg _ h)
  set v : V := (Φ.polar.β (T f) v')⁻¹ • v' with hv
  have hBv : Φ.polar.β (T f) v = 1 := by
    rw [hv, Φ.polar.smul_right, inv_mul_cancel₀ hv']
  refine ⟨v + T v, ?_, ?_⟩
  · simp only [map_add, NM3_T3 T hT3]
    linear_combination (norm := module) (-1 : K) • NM_two_smul_zero (K := K) (T v)
  · rw [Φ.polar.add_right, NM3_B_right_two Φ T hT3 hTQ f v, hf, Φ.polar.add_left, hBv]
    linear_combination (Φ.polar.β f v) * h2K

theorem NM3_fix_u (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) {f u' : V}
    (hQf : Φ.Q f = 0) (hBff : Φ.polar.β f (T f) = 0) (hf : T (T f) = T f + f)
    (hu : T (T u') = T u' + u') (hfu : Φ.polar.β f u' = 1) :
    ∃ u : V, Φ.Q u = 0 ∧ T (T u) = T u + u ∧ Φ.polar.β f u = 1 ∧
      Φ.polar.β u (T u) = 0 := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  have hBf0 : Φ.polar.β f f = 0 := by rw [Φ.polar_self, hQf, mul_zero]
  have hBsymm : Φ.polar.β u' f = 1 := by rw [Φ.polar_symm]; exact hfu
  set c : K := Φ.Q u' with hc
  have key1 : Φ.polar.β u' (T u') = c := by
    have hQ2 : Φ.Q (T u' + u') = Φ.Q u' := by rw [← hu, hTQ, hTQ]
    rw [Φ.Q_add, hTQ, Φ.polar_symm (T u') u'] at hQ2
    linear_combination hQ2 - c * h2K
  have key2 : Φ.polar.β f (T u') = 1 + Φ.polar.β u' (T f) := by
    have h1 := Φ.polar_map_of_Q (g := T) hTQ f (T u')
    have h2 := Φ.polar_map_of_Q (g := T) hTQ f u'
    rw [hu, Φ.polar.add_right, h2, hfu, Φ.polar_symm (T f) u'] at h1
    linear_combination -h1
  refine ⟨u' + c • f, ?_, ?_, ?_, ?_⟩
  · rw [Φ.Q_add, Φ.Q_smul, hQf, Φ.polar.smul_right, hBsymm]
    linear_combination c * h2K
  · simp only [map_add, map_smul]
    linear_combination (norm := module) hu + c • hf
  · rw [Φ.polar.add_right, Φ.polar.smul_right, hBf0, hfu]
    ring
  · simp only [map_add, map_smul, Φ.polar.add_left, Φ.polar.add_right, Φ.polar_smul_left,
      Φ.polar.smul_right, key1, key2, hBff]
    linear_combination (c + c * Φ.polar.β u' (T f)) * h2K

theorem NM3_false_of_quadratic [Finite K] (hK : Nat.card K = 2) (hT3 : T ^ 3 = 1)
    (hTQ : ∀ v, Φ.Q (T v) = Φ.Q v) (W : Submodule K V) (hWQ : ∀ w ∈ W, Φ.Q w = 0)
    (hW : ∀ w ∈ W, T w ∈ W)
    (hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ W, Φ.eichler x y w ∈ W)
    {f : V} (hfW : f ∈ W) (hf0 : f ≠ 0) (hf : T (T f) = T f + f) : False := by
  have h2K : (2 : K) = 0 := NM_two_eq_zero
  obtain ⟨u', hu', hfu'⟩ := NM3_exists_u' Φ T hT3 hTQ hf0 hf
  have hQf := hWQ f hfW
  have hBff : Φ.polar.β f (T f) = 0 := NM_B_eq_zero_of_mem Φ hWQ hfW (hW f hfW)
  obtain ⟨u, hQu, hu, hfu, hBu⟩ := NM3_fix_u Φ T hTQ hQf hBff hf hu' hfu'
  have hQTu : Φ.Q (T u) = 0 := by rw [hTQ, hQu]
  have hu1 : T (T u) = (1 : K) • T u + u := by rw [one_smul]; exact hu
  have hEf := hE u (T u) hQu hBu (NM_eichler_comm Φ T hTQ hQu hu1) f hfW
  set β : K := Φ.polar.β (T u) f with hβ
  have hBuf : Φ.polar.β u f = 1 := by rw [Φ.polar_symm]; exact hfu
  have hz : T u - β • u ∈ W := by
    have : Φ.eichler u (T u) f - f = T u - β • u := by
      rw [QuadForm.eichler_apply, hQTu, hBuf]
      module
    rw [← this]
    exact W.sub_mem hEf hfW
  have hB0 := NM_B_eq_zero_of_mem Φ hWQ hfW (hW _ hz)
  have hBfTu : Φ.polar.β f (T u) = β := Φ.polar_symm _ _
  rw [map_sub, map_smul, hu, Φ.polar.β_sub_right, Φ.polar.add_right, Φ.polar.smul_right,
    hBfTu, hfu] at hB0
  have e : β ^ 2 = β + 1 := by linear_combination -hB0
  have := Fintype.ofFinite K
  have h2 : β ^ 2 = β := by
    simpa [show Fintype.card K = 2 by rw [← Nat.card_eq_fintype_card, hK]] using
      FiniteField.pow_card β
  have : (1 : K) = 0 := by linear_combination h2 - e
  exact one_ne_zero this

end Quadratic

open CFSG.Assembly.LowTwoRank Matrix in
theorem false_of_invariant_totSingular_two {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2) (Φ : QuadForm K (ι → K))
    (hι : 5 ≤ Fintype.card ι) (W : Submodule K (ι → K)) (hWQ : ∀ w ∈ W, Φ.Q w = 0)
    (hW : 2 ≤ Module.finrank K W) (M : GL ι K)
    (hMQ : ∀ v, Φ.Q ((M : Matrix ι ι K) *ᵥ v) = Φ.Q v) (hM3 : M ^ 3 = 1)
    (hMW : ∀ w ∈ W, (M : Matrix ι ι K) *ᵥ w ∈ W)
    (hC : ∀ g ∈ StatedOmega Φ.Q, g * M = M * g → ∀ w ∈ W, (g : Matrix ι ι K) *ᵥ w ∈ W) :
    False := by
  set T : (ι → K) →ₗ[K] (ι → K) := Matrix.toLin' (M : Matrix ι ι K) with hTdef
  have hT : ∀ v, T v = (M : Matrix ι ι K) *ᵥ v := fun v => Matrix.toLin'_apply _ _
  have hT3 : T ^ 3 = 1 := by
    have h1 : T ^ 3 = Matrix.toLinAlgEquiv' ((M : Matrix ι ι K) ^ 3) := by
      rw [map_pow]
      rfl
    rw [h1, ← Units.val_pow_eq_pow_val, hM3]
    simp
  have hTQ : ∀ v, Φ.Q (T v) = Φ.Q v := fun v => by rw [hT]; exact hMQ v
  have hTW : ∀ w ∈ W, T w ∈ W := fun w hw => by rw [hT]; exact hMW w hw
  have hE : ∀ x y, Φ.Q x = 0 → Φ.polar.β x y = 0 →
      (∀ v, Φ.eichler x y (T v) = T (Φ.eichler x y v)) → ∀ w ∈ W, Φ.eichler x y w ∈ W := by
    intro x y hx hxy hcomm w hw
    obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι hx hxy
    have hAM : A * M = M * A := by
      apply Units.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAv, ← hT, hAv, hcomm, hT]
    have := hC A hA hAM w hw
    rwa [hAv] at this
  by_cases hfix : ∀ w ∈ W, T w = w
  · exact NM3_false_of_fixed Φ T hT3 hTQ W hWQ hE hfix hW
  · push Not at hfix
    obtain ⟨f, hfW, hf⟩ := hfix
    have h2K : (2 : K) = 0 := NM_two_eq_zero
    have hf2W : f + T f ∈ W := add_mem hfW (hTW f hfW)
    have hf20 : f + T f ≠ 0 := fun h => hf (NM_eq_of_add_eq_zero K h).symm
    have hrel : T (T (f + T f)) = T (f + T f) + (f + T f) := by
      simp only [map_add, NM3_T3 T hT3]
      linear_combination (norm := module) (-1 : K) • NM_two_smul_zero (K := K) (T f)
    exact NM3_false_of_quadratic Φ T hK hT3 hTQ W hWQ hTW hE hf2W hf20 hrel

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
