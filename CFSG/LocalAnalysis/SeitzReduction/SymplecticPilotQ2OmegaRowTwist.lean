module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowO2

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module
open scoped commutatorElement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Reflect

variable [CharP K 2]

theorem reflect_apply_of_map_eq_one_two {w : V} (hw : Q w = 1) (u : V) :
    reflect Q w u = u + polar Q w u • w := by
  rw [reflect_apply (by rw [hw]; exact one_ne_zero), hw, div_one, omegaInv_sub_eq_add K]

theorem reflect_mul_reflect_apply_two {x z : V} (hx : Q x = 1) (hz : Q z = 1)
    (hxz : polar Q x z = 1) (w : V) :
    (reflect Q x * reflect Q z) w = w + (polar Q x w + polar Q z w) • x + polar Q z w • z := by
  rw [LinearEquiv.mul_apply, reflect_apply_of_map_eq_one_two hz,
    reflect_apply_of_map_eq_one_two hx, polar_add_right, polar_smul_right_eq, hxz, mul_one]
  module

theorem reflect_mul_reflect_pow_three_two {x z : V} (hx : Q x = 1) (hz : Q z = 1)
    (hxz : polar Q x z = 1) : (reflect Q x * reflect Q z) ^ 3 = 1 := by
  have hzx : polar Q z x = 1 := by rw [polar_comm, hxz]
  have h1 : reflect Q x * reflect Q z * reflect Q x = reflect Q (x + z) := by
    have e := reflect_conj (reflect_mem_orthogonalGroup Q x) z
    rw [reflect_inv, reflect_apply_of_map_eq_one_two hx, hxz, one_smul, add_comm] at e
    exact e
  have h2 : reflect Q z * reflect Q x * reflect Q z = reflect Q (x + z) := by
    have e := reflect_conj (reflect_mem_orthogonalGroup Q z) x
    rw [reflect_inv, reflect_apply_of_map_eq_one_two hz, hzx, one_smul] at e
    exact e
  calc (reflect Q x * reflect Q z) ^ 3
      = (reflect Q x * reflect Q z * reflect Q x) * (reflect Q z * reflect Q x * reflect Q z) := by
        rw [pow_succ, pow_succ, pow_one]
        group
    _ = 1 := by rw [h1, h2, reflect_mul_self]

theorem reflect_mul_reflect_mem_omega {x z : V} (hx : Q x = 1) (hz : Q z = 1)
    (hxz : polar Q x z = 1) :
    reflect Q x * reflect Q z ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have h3 := reflect_mul_reflect_pow_three_two hx hz hxz
  have hsq : (reflect Q x * reflect Q z) ^ 2 = ⁅reflect Q x, reflect Q z⁆ := by
    rw [commutatorElement_def, reflect_inv, reflect_inv, _root_.sq]
    group
  have e : reflect Q x * reflect Q z = ((reflect Q x * reflect Q z) ^ 2) ^ 2 := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h3, one_mul]
  rw [e, hsq]
  exact pow_mem (Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q x)
    (reflect_mem_orthogonalGroup Q z)) 2

end Reflect

theorem exists_apply_eq_of_commute_reflect_mul [CharP K 2] [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) {x z : V} (hx : Q x = 1) (hz : Q z = 1)
    (hxz : polar Q x z = 1) {A : V ≃ₗ[K] V}
    (hA : A * (reflect Q x * reflect Q z) = (reflect Q x * reflect Q z) * A) :
    ∃ c₁ c₂ : K, A x = c₁ • x + c₂ • z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, polar_zero_right] at hxz
    exact zero_ne_one hxz
  have hxz' : ∀ c : K, x ≠ c • z := by
    intro c h
    rw [h, polar_smul_left_eq, polar_self_eq_two_mul, omegaInv_two_eq_zero, zero_mul,
      mul_zero] at hxz
    exact zero_ne_one hxz
  obtain ⟨y, hyz, hyx⟩ := omegaInv_exists_polar_eq_zero_polar_eq_one hQ hz0 hxz'
  have hTy : (reflect Q x * reflect Q z) y = y + x := by
    rw [reflect_mul_reflect_apply_two hx hz hxz, polar_comm Q x y, hyx, polar_comm Q z y, hyz,
      add_zero, one_smul, zero_smul, add_zero]
  have hAx : A x = (reflect Q x * reflect Q z) (A y) - A y := by
    rw [← LinearEquiv.mul_apply, ← hA, LinearEquiv.mul_apply, hTy, map_add, add_sub_cancel_left]
  refine ⟨polar Q x (A y) + polar Q z (A y), polar Q z (A y), ?_⟩
  rw [hAx, reflect_mul_reflect_apply_two hx hz hxz]
  abel

theorem exists_perp_three_not_mem_span [FiniteDimensional K V] (a b c d d' : V)
    (hdim : 6 ≤ finrank K V) : ∃ u, polar Q a u = 0 ∧ polar Q b u = 0 ∧ polar Q c u = 0 ∧
      u ∉ Submodule.span K ({d, d'} : Set V) := by
  classical
  set φ : V →ₗ[K] K × K × K :=
    (polarBilin Q a).prod ((polarBilin Q b).prod (polarBilin Q c)) with hφ
  by_contra hc
  push Not at hc
  have hle : LinearMap.ker φ ≤ Submodule.span K ({d, d'} : Set V) := by
    intro u hu
    have h0 : φ u = 0 := LinearMap.mem_ker.1 hu
    have e1 : polar Q a u = 0 := by simpa [hφ] using congrArg Prod.fst h0
    have e2 : polar Q b u = 0 := by simpa [hφ] using congrArg (fun p => p.2.1) h0
    have e3 : polar Q c u = 0 := by simpa [hφ] using congrArg (fun p => p.2.2) h0
    exact hc u e1 e2 e3
  have h1 := Submodule.finrank_mono hle
  have h2 : finrank K (Submodule.span K ({d, d'} : Set V)) ≤ 2 := by
    have e : ({d, d'} : Set V) = (({d, d'} : Finset V) : Set V) := by simp
    rw [e]
    refine (finrank_span_finset_le_card _).trans ?_
    exact (Finset.card_insert_le _ _).trans (by simp)
  have h3 := LinearMap.finrank_range_add_finrank_ker φ
  have h4 : finrank K (LinearMap.range φ) ≤ 3 := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self]
  omega

section Centralizer

variable [CharP K 2] [FiniteDimensional K V]

theorem apply_eq_self_of_nonsingular (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1) {A : V ≃ₗ[K] V}
    (hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g v = v → A * g = g * A)
    {x : V} (hxv : polar Q v x = 0) (hx : Q x = 1) (hxne : x ≠ v) : A x = x := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hx
    exact zero_ne_one hx
  have hxv' : ∀ c : K, x ≠ c • v := by
    intro c h
    rcases omegaTwo_eq_zero_or_eq_one hK c with rfl | rfl
    · rw [zero_smul] at h
      exact hx0 h
    · rw [one_smul] at h
      exact hxne h
  have hvx : polar Q x v = 0 := by rw [polar_comm, hxv]
  have hvv : polar Q v v = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  obtain ⟨z₀, hz₀v, hz₀x⟩ := omegaInv_exists_polar_eq_zero_polar_eq_one hQ hv0 hxv'
  obtain ⟨z₁, hz₁v, hz₁x, hQz₁⟩ : ∃ z₁, polar Q v z₁ = 0 ∧ polar Q x z₁ = 1 ∧ Q z₁ = 1 := by
    have hvz₀ : polar Q v z₀ = 0 := by rw [polar_comm, hz₀v]
    have hxz₀ : polar Q x z₀ = 1 := by rw [polar_comm, hz₀x]
    rcases omegaTwo_eq_zero_or_eq_one hK (Q z₀) with h0 | h1
    · refine ⟨z₀ + v, ?_, ?_, ?_⟩
      · rw [polar_add_right, hvz₀, hvv, add_zero]
      · rw [polar_add_right, hxz₀, hvx, add_zero]
      · rw [QuadraticMap.map_add Q, h0, hv, hz₀v, zero_add, add_zero]
    · exact ⟨z₀, hvz₀, hxz₀, h1⟩
  have hz₁v' : polar Q z₁ v = 0 := by rw [polar_comm, hz₁v]
  obtain ⟨u, huv, hux, huz, huspan⟩ := exists_perp_three_not_mem_span (Q := Q) v x z₁ v v hdim
  have hvspan : v ∈ Submodule.span K ({v, v} : Set V) := Submodule.subset_span (by simp)
  obtain ⟨w, hwv, hwx, hwz, hw0, hQw⟩ : ∃ w, polar Q v w = 0 ∧ polar Q x w = 0 ∧
      polar Q z₁ w = 0 ∧ w ≠ 0 ∧ Q w = 0 := by
    have hu0 : u ≠ 0 := fun h => huspan (h ▸ Submodule.zero_mem _)
    rcases omegaTwo_eq_zero_or_eq_one hK (Q u) with h0 | h1
    · exact ⟨u, huv, hux, huz, hu0, h0⟩
    · refine ⟨u + v, by rw [polar_add_right, huv, hvv, add_zero],
        by rw [polar_add_right, hux, hvx, add_zero], by rw [polar_add_right, huz, hz₁v', add_zero],
        fun h => huspan ?_, ?_⟩
      · rw [eq_neg_of_add_eq_zero_left h]
        exact Submodule.neg_mem _ hvspan
      · rw [QuadraticMap.map_add Q, h1, hv, polar_comm, huv, add_zero, CharTwo.add_self_eq_zero]
  set z₂ := z₁ + w with hz₂
  have hz₂v : polar Q v z₂ = 0 := by rw [hz₂, polar_add_right, hz₁v, hwv, add_zero]
  have hz₂x : polar Q x z₂ = 1 := by rw [hz₂, polar_add_right, hz₁x, hwx, add_zero]
  have hQz₂ : Q z₂ = 1 := by
    rw [hz₂, QuadraticMap.map_add Q, hQz₁, hQw, hwz, add_zero, add_zero]
  have hfix : ∀ {z : V}, polar Q v z = 0 → (reflect Q x * reflect Q z) v = v := fun {z} hzv => by
    have hzv' : polar Q z v = 0 := by rw [polar_comm]; exact hzv
    rw [LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hzv',
      reflect_apply_of_polar_eq_zero hvx]
  obtain ⟨c₁, c₂, h1⟩ := exists_apply_eq_of_commute_reflect_mul hQ hx hQz₁ hz₁x
    (hcomm _ (reflect_mul_reflect_mem_omega hx hQz₁ hz₁x) (hfix hz₁v))
  obtain ⟨d₁, d₂, h2'⟩ := exists_apply_eq_of_commute_reflect_mul hQ hx hQz₂ hz₂x
    (hcomm _ (reflect_mul_reflect_mem_omega hx hQz₂ hz₂x) (hfix hz₂v))
  have e : c₁ • x + c₂ • z₁ = d₁ • x + d₂ • z₁ + d₂ • w := by
    rw [← h1, h2', hz₂, smul_add, add_assoc]
  have hxx : polar Q x x = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hz₁z₁ : polar Q z₁ z₁ = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hz₁x' : polar Q z₁ x = 1 := by rw [polar_comm, hz₁x]
  have ex := congrArg (polar Q x) e
  have ez := congrArg (polar Q z₁) e
  simp only [polar_add_right, polar_smul_right_eq, hxx, hz₁x, hwx, hz₁z₁, hz₁x', hwz, mul_zero,
    mul_one, zero_add, add_zero] at ex ez
  rw [ex, ez] at e
  have hw' : d₂ • w = 0 := by
    calc d₂ • w = (d₁ • x + d₂ • z₁ + d₂ • w) - (d₁ • x + d₂ • z₁) := by abel
      _ = 0 := by rw [← e, sub_self]
  have hd₂ : d₂ = 0 := (smul_eq_zero.1 hw').resolve_right hw0
  rw [ex, hd₂, zero_smul, add_zero] at h1
  have hc₁ : c₁ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h1
    exact hx0 (A.injective (h1.trans (map_zero A).symm))
  rw [h1, omegaTwo_eq_one_of_ne_zero hK hc₁, one_smul]

theorem apply_eq_self_of_mem_perp (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1) {A : V ≃ₗ[K] V}
    (hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g v = v → A * g = g * A)
    {x : V} (hxv : polar Q v x = 0) : A x = x := by
  have h2 : (2 : K) = 0 := omegaInv_two_eq_zero
  have hvv : polar Q v v = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  have hnons : ∀ y, polar Q v y = 0 → Q y = 1 → y ≠ v → A y = y := fun y hy hQy hyv =>
    apply_eq_self_of_nonsingular hK hQ hdim hv hcomm hy hQy hyv
  have hsing : ∀ y, polar Q v y = 0 → Q y = 0 → A y = y := by
    intro y hyv hQy
    by_cases hy0 : y = 0
    · rw [hy0, map_zero]
    have hyv' : polar Q y v = 0 := by rw [polar_comm, hyv]
    obtain ⟨u, huv, huy, -, huspan⟩ := exists_perp_three_not_mem_span (Q := Q) v y y y v hdim
    have hyS : y ∈ Submodule.span K ({y, v} : Set V) := Submodule.subset_span (by simp)
    have hvS : v ∈ Submodule.span K ({y, v} : Set V) := Submodule.subset_span (by simp)
    obtain ⟨n₁, hn₁v, hn₁y, hQn₁, hn₁ne, hn₁ne'⟩ : ∃ n₁, polar Q v n₁ = 0 ∧ polar Q y n₁ = 0 ∧
        Q n₁ = 1 ∧ n₁ ≠ v ∧ n₁ ≠ y + v := by
      rcases omegaTwo_eq_zero_or_eq_one hK (Q u) with h0 | h1
      · refine ⟨u + v, by rw [polar_add_right, huv, hvv, add_zero],
          by rw [polar_add_right, huy, hyv', add_zero], ?_, fun h => huspan ?_, fun h => huspan ?_⟩
        · rw [QuadraticMap.map_add Q, h0, hv, polar_comm, huv, zero_add, add_zero]
        · rw [add_eq_right.1 h]
          exact Submodule.zero_mem _
        · rw [add_right_cancel h]
          exact hyS
      · refine ⟨u, huv, huy, h1, fun h => huspan (h ▸ hvS), fun h => huspan ?_⟩
        rw [h]
        exact Submodule.add_mem _ hyS hvS
    have hyn : polar Q v (y + n₁) = 0 := by rw [polar_add_right, hyv, hn₁v, add_zero]
    have hQyn : Q (y + n₁) = 1 := by
      rw [QuadraticMap.map_add Q, hQy, hQn₁, hn₁y, zero_add, add_zero]
    have hynv : y + n₁ ≠ v := by
      intro h
      apply hn₁ne'
      rw [← h, ← add_assoc, omegaInv_add_self K, zero_add]
    calc A y = A (y + n₁) - A n₁ := by rw [map_add, add_sub_cancel_right]
      _ = y := by rw [hnons _ hyn hQyn hynv, hnons _ hn₁v hQn₁ hn₁ne, add_sub_cancel_right]
  have hvfix : A v = v := by
    obtain ⟨u, huv, -, -, huspan⟩ := exists_perp_three_not_mem_span (Q := Q) v v v v v hdim
    have hvS : v ∈ Submodule.span K ({v, v} : Set V) := Submodule.subset_span (by simp)
    obtain ⟨s, hsv, hQs, hs0⟩ : ∃ s, polar Q v s = 0 ∧ Q s = 0 ∧ s ≠ 0 := by
      rcases omegaTwo_eq_zero_or_eq_one hK (Q u) with h0 | h1
      · exact ⟨u, huv, h0, fun h => huspan (h ▸ Submodule.zero_mem _)⟩
      · refine ⟨u + v, by rw [polar_add_right, huv, hvv, add_zero], ?_, fun h => huspan ?_⟩
        · rw [QuadraticMap.map_add Q, h1, hv, polar_comm, huv, add_zero, CharTwo.add_self_eq_zero]
        · rw [eq_neg_of_add_eq_zero_left h]
          exact Submodule.neg_mem _ hvS
    have hvs : polar Q v (v + s) = 0 := by rw [polar_add_right, hvv, hsv, add_zero]
    have hQvs : Q (v + s) = 1 := by
      rw [QuadraticMap.map_add Q, hv, hQs, hsv, add_zero, add_zero]
    have hvsne : v + s ≠ v := fun h => hs0 (add_eq_left.1 h)
    calc A v = A (v + s) - A s := by rw [map_add, add_sub_cancel_right]
      _ = v := by rw [hnons _ hvs hQvs hvsne, hsing s hsv hQs, add_sub_cancel_right]
  rcases omegaTwo_eq_zero_or_eq_one hK (Q x) with h0 | h1
  · exact hsing x hxv h0
  · by_cases hxv' : x = v
    · rw [hxv']
      exact hvfix
    · exact hnons x hxv h1 hxv'

omit [FiniteDimensional K V] in
theorem eq_one_or_eq_reflect_of_perp (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    {v : V} (hv : Q v = 1) {A : V ≃ₗ[K] V} (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ x, polar Q v x = 0 → A x = x) : A = 1 ∨ A = reflect Q v := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨y, hyv⟩ := omegaInv_exists_polar_eq_one hQ hv0
  have hvy : polar Q v y = 1 := by rw [polar_comm, hyv]
  have hperp' : ∀ w, polar Q v (w - polar Q v w • y) = 0 := fun w => by
    rw [polar_sub_right, polar_smul_right_eq, hvy, mul_one, sub_self]
  have hdecomp : ∀ w, w = (w - polar Q v w • y) + polar Q v w • y := fun w => by abel
  have hdperp : ∀ x, polar Q v x = 0 → polar Q (A y - y) x = 0 := by
    intro x hx
    have e := polar_map_of_mem hA y x
    rw [hfix x hx] at e
    rw [polar_sub_left, e, sub_self]
  have hd : A y - y = polar Q (A y - y) y • v := by
    apply eq_of_sub_eq_zero
    apply eq_zero_of_polar_eq_zero hQ
    intro x
    have h0 := hdperp _ (hperp' x)
    rw [polar_sub_right, polar_smul_right_eq] at h0
    rw [polar_sub_left, polar_smul_left_eq]
    linear_combination h0
  rcases omegaTwo_eq_zero_or_eq_one hK (polar Q (A y - y) y) with h0 | h1
  · left
    have hAy : A y = y := by
      rw [h0, zero_smul] at hd
      exact sub_eq_zero.1 hd
    refine LinearEquiv.ext fun w => ?_
    show A w = w
    calc A w = A ((w - polar Q v w • y) + polar Q v w • y) := congrArg A (hdecomp w)
      _ = (w - polar Q v w • y) + polar Q v w • y := by
        rw [map_add, map_smul, hfix _ (hperp' w), hAy]
      _ = w := (hdecomp w).symm
  · right
    have hAy : A y = y + v := by
      rw [h1, one_smul] at hd
      rw [← hd]
      abel
    refine LinearEquiv.ext fun w => ?_
    calc A w = A ((w - polar Q v w • y) + polar Q v w • y) := congrArg A (hdecomp w)
      _ = (w - polar Q v w • y) + polar Q v w • (y + v) := by
        rw [map_add, map_smul, hfix _ (hperp' w), hAy]
      _ = reflect Q v w := by
        rw [reflect_apply_of_map_eq_one_two hv w, smul_add]
        abel

theorem eq_one_or_eq_reflect_of_commute (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 6 ≤ finrank K V) {v : V} (hv : Q v = 1) {A : V ≃ₗ[K] V}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hcomm : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g v = v → A * g = g * A) :
    A = 1 ∨ A = reflect Q v :=
  eq_one_or_eq_reflect_of_perp hK hQ hv hA fun _ hx =>
    apply_eq_self_of_mem_perp hK hQ hdim hv hcomm hx

end Centralizer

end CFSG.SeitzReduction.SymplecticPilot
