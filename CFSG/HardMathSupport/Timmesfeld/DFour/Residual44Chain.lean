module

public import CFSG.HardMathSupport.Timmesfeld.DFour.Residual44Jordan

public section

namespace CFSG.HardMathSupport.Timmesfeld.DFour

open QuadraticMap Module LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def chainMap (e₀ e₁ e₂ e₃ : V) : Module.End K V where
  toFun x := polar Q x e₀ • e₃ - polar Q x e₁ • e₂ + polar Q x e₂ • e₁ - polar Q x e₃ • e₀
  map_add' x y := by
    simp only [polar_add_left, add_smul]
    abel
  map_smul' c x := by
    simp only [polar_smul_left, smul_eq_mul, RingHom.id_apply, mul_smul, smul_add, smul_sub]

theorem chainMap_apply (e₀ e₁ e₂ e₃ x : V) :
    chainMap Q e₀ e₁ e₂ e₃ x =
      polar Q x e₀ • e₃ - polar Q x e₁ • e₂ + polar Q x e₂ • e₁ - polar Q x e₃ • e₀ := rfl

theorem chainMap_skew (e₀ e₁ e₂ e₃ x y : V) :
    polar Q (chainMap Q e₀ e₁ e₂ e₃ x) y = -polar Q x (chainMap Q e₀ e₁ e₂ e₃ y) := by
  simp only [chainMap_apply, polar_add_left, polar_sub_left, polar_smul_left, polar_add_right,
    polar_sub_right, polar_smul_right, smul_eq_mul]
  rw [polar_comm Q e₃ y, polar_comm Q e₂ y, polar_comm Q e₁ y, polar_comm Q e₀ y]
  ring

variable {z : Module.End K V}

theorem chainMap_comm (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y)) {e₀ e₁ e₂ e₃ : V}
    (h1 : z e₀ = e₁) (h2 : z e₁ = e₂) (h3 : z e₂ = e₃) (h4 : z e₃ = 0) (x : V) :
    chainMap Q e₀ e₁ e₂ e₃ (z x) = z (chainMap Q e₀ e₁ e₂ e₃ x) := by
  simp only [chainMap_apply, map_add, map_sub, map_smul, h1, h2, h3, h4, hz x, polar_zero_right,
    neg_smul, zero_smul, smul_zero]
  abel

theorem chainMap_chainMap {e₀ e₁ e₂ e₃ : V}
    (h : ∀ u ∈ ({e₀, e₁, e₂, e₃} : Set V), ∀ v ∈ ({e₀, e₁, e₂, e₃} : Set V), polar Q u v = 0)
    (x : V) : chainMap Q e₀ e₁ e₂ e₃ (chainMap Q e₀ e₁ e₂ e₃ x) = 0 := by
  have hk : ∀ v ∈ ({e₀, e₁, e₂, e₃} : Set V), polar Q (chainMap Q e₀ e₁ e₂ e₃ x) v = 0 := by
    intro v hv
    simp only [chainMap_apply, polar_add_left, polar_sub_left, polar_smul_left, smul_eq_mul,
      h e₀ (by simp) v hv, h e₁ (by simp) v hv, h e₂ (by simp) v hv, h e₃ (by simp) v hv]
    ring
  rw [chainMap_apply, hk e₀ (by simp), hk e₁ (by simp), hk e₂ (by simp), hk e₃ (by simp)]
  simp

theorem chainMap_of_ker (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y)) {x : V} (hx : z x = 0)
    (e : V) :
    chainMap Q e (z e) (z (z e)) (z (z (z e))) x = polar Q x e • z (z (z e)) := by
  have h0 : ∀ y, polar Q x (z y) = 0 := fun y => by
    have := hz x y
    rw [hx, polar_zero_left] at this
    linear_combination this
  rw [chainMap_apply, h0, h0, h0]
  simp

theorem polar_chain (h2 : (2 : K) ≠ 0) (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y))
    (h4 : z ^ 4 = 0) {e : V} (hQ : Q e = 0) (hB : polar Q e ((z ^ 2) e) = 0) (i j : ℕ) :
    polar Q ((z ^ i) e) ((z ^ j) e) = 0 := by
  rw [polar_pow_left hz, ← Module.End.mul_apply, ← pow_add]
  rcases Nat.even_or_odd (i + j) with ⟨m, hm⟩ | hodd
  · rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [hm, pow_zero, Module.End.one_apply, polar_self, hQ, smul_zero, mul_zero]
      · rw [hm, hB, mul_zero]
    · have : z ^ (i + j) = 0 := by
        rw [show i + j = 4 + (i + j - 4) by omega, pow_add, h4, zero_mul]
      rw [this, LinearMap.zero_apply, polar_zero_right, mul_zero]
  · rw [polar_pow_self_odd h2 hz hodd, mul_zero]

theorem pow_four_eq_zero (h4 : ∀ x, z (z (z (z x))) = 0) : z ^ 4 = 0 :=
  LinearMap.ext fun x => by simpa [pow_succ, Module.End.mul_apply] using h4 x

theorem polar_isotropic_chain (h2 : (2 : K) ≠ 0) (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y))
    (h4 : ∀ x, z (z (z (z x))) = 0) {e : V} (hQ : Q e = 0) (hB : polar Q e (z (z e)) = 0) :
    ∀ u ∈ ({e, z e, z (z e), z (z (z e))} : Set V),
      ∀ v ∈ ({e, z e, z (z e), z (z (z e))} : Set V), polar Q u v = 0 := by
  have hpow : ∀ u ∈ ({e, z e, z (z e), z (z (z e))} : Set V), ∃ i : ℕ, u = (z ^ i) e := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨2, by simp [pow_succ, Module.End.mul_apply]⟩
    · exact ⟨3, by simp [pow_succ, Module.End.mul_apply]⟩
  have hB' : polar Q e ((z ^ 2) e) = 0 := by
    rw [pow_two, Module.End.mul_apply, hB]
  intro u hu v hv
  obtain ⟨i, rfl⟩ := hpow u hu
  obtain ⟨j, rfl⟩ := hpow v hv
  exact polar_chain h2 hz (pow_four_eq_zero h4) hQ hB' i j

theorem exists_polar_eq_one (hnd : (polarBilin Q).Nondegenerate) {a : V} (ha : a ≠ 0) :
    ∃ w, polar Q a w = 1 := by
  by_contra! h
  apply ha
  refine hnd.1 a fun y => ?_
  change polar Q a y = 0
  by_contra hy
  apply h ((polar Q a y)⁻¹ • y)
  rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]

theorem exists_isotropic_chain (h2 : (2 : K) ≠ 0) (hnd : (polarBilin Q).Nondegenerate)
    (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y)) (h4 : ∀ x, z (z (z (z x))) = 0) {u : V}
    (hu : z (z (z u)) ≠ 0) :
    ∃ e, z (z (z e)) = z (z (z u)) ∧ Q e = 0 ∧ polar Q e (z (z e)) = 0 := by
  obtain ⟨w₀, hw₀⟩ := exists_polar_eq_one hnd hu
  obtain ⟨c, hc2⟩ : ∃ c : K, 2 * c = polar Q u (z (z u)) :=
    ⟨polar Q u (z (z u)) / 2, by field_simp⟩
  have f1 : polar Q (z (z (z u))) (c • w₀) = c := by
    rw [polar_smul_right, hw₀, smul_eq_mul, mul_one]
  have f2 : polar Q (c • w₀) (z (z (z u))) = c := by rw [polar_comm, f1]
  have h3e₁ : z (z (z (u + z (c • w₀)))) = z (z (z u)) := by
    simp only [map_add, h4, add_zero]
  have hBe₁ : polar Q (u + z (c • w₀)) (z (z (u + z (c • w₀)))) = 0 := by
    have a1 := hz (z (z u)) (c • w₀)
    have a2 := hz (z u) (z (c • w₀))
    have a3 := hz u (z (z (c • w₀)))
    have a4 := hz (c • w₀) (z (z u))
    have a5 := hz (c • w₀) (z (z (z (c • w₀))))
    rw [h4, polar_zero_right, neg_zero] at a5
    simp only [map_add, polar_add_left, polar_add_right]
    linear_combination a1 - a2 + a3 - f1 + a4 - f2 + a5 - hc2
  set e₁ := u + z (c • w₀) with he₁
  have hz2 : z (z e₁) ≠ 0 := by
    intro h0
    apply hu
    rw [← h3e₁, h0, map_zero]
  obtain ⟨w₁, hw₁⟩ := exists_polar_eq_one hnd hz2
  set d := -Q e₁ with hd
  have hq : Q (z (z (d • w₁))) = 0 := by
    have b1 := hz (z (d • w₁)) (z (z (d • w₁)))
    have b2 := hz (d • w₁) (z (z (z (d • w₁))))
    rw [h4, polar_zero_right, neg_zero] at b2
    have hs := polar_self Q (z (z (d • w₁)))
    rw [two_smul] at hs
    have : (2 : K) * Q (z (z (d • w₁))) = 0 := by linear_combination -hs + b1 - b2
    exact (mul_eq_zero.1 this).resolve_left h2
  have e6 : polar Q e₁ (z (z (d • w₁))) = d := by
    have b5 : polar Q (z (z e₁)) (d • w₁) = d := by
      rw [polar_smul_right, hw₁, smul_eq_mul, mul_one]
    have b6 := hz (z e₁) (d • w₁)
    have b7 := hz e₁ (z (d • w₁))
    linear_combination b7 - b6 + b5
  refine ⟨e₁ + z (z (d • w₁)), ?_, ?_, ?_⟩
  · simp only [map_add, h4, add_zero, h3e₁]
  · rw [QuadraticMap.map_add Q, hq, e6, hd]
    ring
  · simp only [map_add, h4, add_zero, polar_add_left, hBe₁]
    have c1 := hz (z (d • w₁)) (z (z e₁))
    have c2 := hz (d • w₁) (z (z (z e₁)))
    have c5 : polar Q (d • w₁) (z (z (z (z e₁)))) = 0 := by rw [h4, polar_zero_right]
    linear_combination c1 - c2 + c5

theorem not_eigen_both (hnd : (polarBilin Q).Nondegenerate)
    (hz : ∀ x y, polar Q (z x) y = -polar Q x (z y)) (h4 : ∀ x, z (z (z (z x))) = 0)
    {e₁ e₂ : V} (hc₁ : polar Q (z (z (z e₁))) e₁ = 0) (hc₂ : polar Q (z (z (z e₂))) e₂ = 0)
    (hli : LinearIndependent K ![z (z (z e₁)), z (z (z e₂))])
    (hspan : ∀ x, z x = 0 → x ∈ Submodule.span K {z (z (z e₁)), z (z (z e₂))})
    {x : V} (hx : z x = 0) (hx0 : x ≠ 0) {μ₁ μ₂ : K}
    (h₁ : x + polar Q x e₁ • z (z (z e₁)) = μ₁ • x)
    (h₂ : x + polar Q x e₂ • z (z (z e₂)) = μ₂ • x) : False := by
  set b₁ := z (z (z e₁)) with hb₁
  set b₂ := z (z (z e₂)) with hb₂
  have hpair := LinearIndependent.pair_iff.1 hli
  have h3 : ∀ y e, polar Q (z (z (z y))) e = -polar Q y (z (z (z e))) := by
    intro y e
    have g1 := hz (z (z y)) e
    have g2 := hz (z y) (z e)
    have g3 := hz y (z (z e))
    linear_combination g1 - g2 + g3
  have hcoef : ∀ y, z y = 0 → ∃ c₁ c₂ : K, c₁ • b₁ + c₂ • b₂ = y := fun y hy =>
    Submodule.mem_span_pair.1 (hspan y hy)
  have hb₁0 : b₁ ≠ 0 := by
    intro h
    have := hpair 1 0 (by rw [h]; simp)
    exact one_ne_zero this.1
  have hb₂0 : b₂ ≠ 0 := by
    intro h
    have := hpair 0 1 (by rw [h]; simp)
    exact one_ne_zero this.2
  have hβ₁ : polar Q b₂ e₁ ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_polar_eq_one hnd hb₁0
    obtain ⟨c₁, c₂, hc⟩ := hcoef (z (z (z y))) (h4 y)
    have k1 := h3 y e₁
    rw [← hc, polar_add_left, polar_smul_left, polar_smul_left, hc₁, polar_comm Q y, hy] at k1
    intro h0
    rw [h0] at k1
    simp at k1
  have hβ₂ : polar Q b₁ e₂ ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_polar_eq_one hnd hb₂0
    obtain ⟨c₁, c₂, hc⟩ := hcoef (z (z (z y))) (h4 y)
    have k1 := h3 y e₂
    rw [← hc, polar_add_left, polar_smul_left, polar_smul_left, hc₂, polar_comm Q y, hy] at k1
    intro h0
    rw [h0] at k1
    simp at k1
  obtain ⟨c₁, c₂, hc⟩ := hcoef x hx
  have hx₁ : polar Q x e₁ = c₂ * polar Q b₂ e₁ := by
    rw [← hc, polar_add_left, polar_smul_left, polar_smul_left, hc₁, smul_eq_mul, smul_eq_mul,
      mul_zero, zero_add]
  have hx₂ : polar Q x e₂ = c₁ * polar Q b₁ e₂ := by
    rw [← hc, polar_add_left, polar_smul_left, polar_smul_left, hc₂, smul_eq_mul, smul_eq_mul,
      mul_zero, add_zero]
  rw [hx₁, ← hc] at h₁
  rw [hx₂, ← hc] at h₂
  have k₁ := hpair (c₁ + c₂ * polar Q b₂ e₁ - μ₁ * c₁) (c₂ - μ₁ * c₂)
    (by linear_combination (norm := module) h₁)
  have k₂ := hpair (c₁ - μ₂ * c₁) (c₂ + c₁ * polar Q b₁ e₂ - μ₂ * c₂)
    (by linear_combination (norm := module) h₂)
  have hc₂0 : c₂ * c₂ * polar Q b₂ e₁ = 0 := by linear_combination c₂ * k₁.1 - c₁ * k₁.2
  have hc₁0 : c₁ * c₁ * polar Q b₁ e₂ = 0 := by linear_combination c₁ * k₂.2 - c₂ * k₂.1
  have hc₂' : c₂ = 0 := by
    rcases mul_eq_zero.1 hc₂0 with h | h
    · exact mul_self_eq_zero.1 h
    · exact absurd h hβ₁
  have hc₁' : c₁ = 0 := by
    rcases mul_eq_zero.1 hc₁0 with h | h
    · exact mul_self_eq_zero.1 h
    · exact absurd h hβ₂
  apply hx0
  rw [← hc, hc₁', hc₂', zero_smul, zero_smul, add_zero]

end CFSG.HardMathSupport.Timmesfeld.DFour
