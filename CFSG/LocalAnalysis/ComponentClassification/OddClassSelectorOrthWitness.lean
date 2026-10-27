module

public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupOrthogonalAbelianization
public import CFSG.LocalAnalysis.ComponentInitial.LinearOrthogonalBasis
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.OddClassSelector

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem reflect_comm_of_polar_eq_zero {u v : V} (huv : polar Q u v = 0) :
    reflect Q u * reflect Q v = reflect Q v * reflect Q u := by
  have h := reflect_conj (reflect_mem_orthogonalGroup Q u) v
  rw [reflect_apply_of_polar_eq_zero huv, reflect_inv] at h
  calc reflect Q u * reflect Q v = reflect Q u * reflect Q v * reflect Q u * reflect Q u := by
        rw [mul_assoc _ (reflect Q u), reflect_mul_self, mul_one]
    _ = reflect Q v * reflect Q u := by rw [h]

theorem reflect_mul_reflect_mem (h2 : (2 : K) ≠ 0) {u v : V} (hu : Q u ≠ 0) (hv : Q v ≠ 0)
    (hsq : IsSquare (Q u * Q v)) :
    reflect Q u * reflect Q v ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hu hv (by rw [hc, mul_zero])
  have hv' : Q u = Q ((c / Q v) • v) := by
    rw [QuadraticMap.map_smul, smul_eq_mul]
    field_simp
    linear_combination hc
  obtain ⟨g, hg, hgu⟩ :=
    LocalAnalysis.ComponentInitial.exists_mem_orthogonalGroup_apply_eq h2 hv' (by rwa [← hv'])
  have hconj : g * reflect Q u * g⁻¹ = reflect Q v := by
    rw [reflect_conj hg, hgu,
      LocalAnalysis.ComponentInitial.reflect_smul_of_ne_zero (div_ne_zero hc0 hv)]
  have hcomm : reflect Q u * reflect Q v = ⁅reflect Q u, g⁆ := by
    rw [commutatorElement_def, ← hconj, reflect_inv]
    group
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q u) hg

theorem polar_self_eq (x : V) : polar Q x x = 2 * Q x := by
  rw [polar_self, two_smul, two_mul]

theorem map_sub_of_polar_eq_zero {u y : V} (h : polar Q u y = 0) : Q (u - y) = Q u + Q y := by
  have h1 : polar Q u (-y) = 0 := by rw [polar_neg_right, h, neg_zero]
  have h2 : polar Q u (-y) = Q (u - y) - Q u - Q y := by
    rw [polar, QuadraticMap.map_neg, ← sub_eq_add_neg u y]
  linear_combination h2.symm.trans h1

theorem reflect_sub_apply (h2 : (2 : K) ≠ 0) {u y : V} (h : polar Q u y = 0) (hQ : Q u = Q y)
    (hy : Q y ≠ 0) : reflect Q (u - y) y = u := by
  have hQs : Q (u - y) = 2 * Q y := by rw [map_sub_of_polar_eq_zero h, hQ, two_mul]
  have hQs0 : Q (u - y) ≠ 0 := by rw [hQs]; exact mul_ne_zero h2 hy
  rw [reflect_apply hQs0, polar_sub_left, h, polar_self_eq, hQs]
  have : (0 - 2 * Q y) / (2 * Q y) = -1 := by
    field_simp
    ring
  rw [this, neg_one_smul, sub_neg_eq_add, add_sub_cancel]

section Main

variable [Finite K] [FiniteDimensional K V]

theorem mem_span_norm (hK : ringChar K ≠ 2) {M : Submodule K V}
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate) (hM3 : 3 ≤ finrank K M)
    {c : K} (hc : c ≠ 0) :
    ∀ m ∈ M, m ∈ Submodule.span K {u : V | u ∈ M ∧ Q u = c} := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  have hsymm : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨hval, hbas⟩ :=
    LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
      hodd rfl (by omega : 2 ≤ finrank K M) hMnd (hsymm.restrict M)
  have h2c : 2 * c ≠ 0 := mul_ne_zero h2 hc
  obtain ⟨m0, hm0⟩ := hval (2 * c) h2c
  obtain ⟨eb, heo, -, hea, hel⟩ := hbas (2 * c) m0 h2c hm0
  set S := Submodule.span K {u : V | u ∈ M ∧ Q u = c}
  set j0 : Fin (finrank K M) := ⟨0, by omega⟩
  set j1 : Fin (finrank K M) := ⟨1, by omega⟩
  set jl : Fin (finrank K M) := ⟨finrank K M - 1, by omega⟩
  have hQa : ∀ j : Fin (finrank K M), (j : ℕ) < finrank K M - 1 → Q (eb j : V) = c := by
    intro j hj
    have h := hea j hj
    change polar Q (eb j : V) (eb j : V) = 2 * c at h
    rw [polar_self_eq] at h
    exact mul_left_cancel₀ h2 h
  have hmemS : ∀ j : Fin (finrank K M), (j : ℕ) < finrank K M - 1 → (eb j : V) ∈ S := fun j hj =>
    Submodule.subset_span ⟨(eb j).2, hQa j hj⟩
  have hQl : Q (eb jl : V) ≠ 0 := by
    intro h0
    apply hel jl rfl
    change polar Q (eb jl : V) (eb jl : V) = 0
    rw [polar_self_eq, h0, mul_zero]
  have hQ0 : Q (eb j0 : V) = c := hQa j0 (by simp [j0]; omega)
  have hQ1 : Q (eb j1 : V) = c := hQa j1 (by simp [j1]; omega)
  obtain ⟨x, y, hxy⟩ := LocalAnalysis.ComponentInitial.exists_mul_sq_add_mul_sq_eq
    (by rw [← Nat.card_eq_fintype_card]; exact Nat.odd_iff.mp hodd) hc hc (c - Q (eb jl : V))
  set w : V := x • (eb j0 : V) + y • (eb j1 : V) + (eb jl : V)
  have h01 : polar Q (eb j0 : V) (eb j1 : V) = 0 := heo (show j0 ≠ j1 by simp [j0, j1, Fin.ext_iff])
  have h0l : polar Q (eb j0 : V) (eb jl : V) = 0 :=
    heo (show j0 ≠ jl by simp [j0, jl, Fin.ext_iff]; omega)
  have h1l : polar Q (eb j1 : V) (eb jl : V) = 0 :=
    heo (show j1 ≠ jl by simp [j1, jl, Fin.ext_iff]; omega)
  have hw : Q w = c := by
    have e1 : Q w = Q (x • (eb j0 : V) + y • (eb j1 : V)) + Q (eb jl : V) +
        polar Q (x • (eb j0 : V) + y • (eb j1 : V)) (eb jl : V) := by rw [polar]; ring
    have e2 : Q (x • (eb j0 : V) + y • (eb j1 : V)) = Q (x • (eb j0 : V)) + Q (y • (eb j1 : V)) +
        polar Q (x • (eb j0 : V)) (y • (eb j1 : V)) := by rw [polar]; ring
    rw [e1, e2, polar_add_left, polar_smul_left, polar_smul_left, polar_smul_left,
      polar_smul_right, h0l, h1l, h01, QuadraticMap.map_smul, QuadraticMap.map_smul, hQ0, hQ1]
    simp only [smul_eq_mul, mul_zero, add_zero]
    linear_combination hxy
  have hwM : w ∈ M := add_mem (add_mem (M.smul_mem x (eb j0).2) (M.smul_mem y (eb j1).2)) (eb jl).2
  have hlS : (eb jl : V) ∈ S := by
    have hwS : w ∈ S := Submodule.subset_span ⟨hwM, hw⟩
    have h3 : (eb jl : V) = w - x • (eb j0 : V) - y • (eb j1 : V) := by
      simp only [w]
      abel
    rw [h3]
    exact sub_mem (sub_mem hwS (S.smul_mem x (hmemS j0 (by simp [j0]; omega))))
      (S.smul_mem y (hmemS j1 (by simp [j1]; omega)))
  have hall : ∀ j : Fin (finrank K M), (eb j : V) ∈ S := by
    intro j
    rcases Nat.lt_or_ge (j : ℕ) (finrank K M - 1) with h | h
    · exact hmemS j h
    · rw [show j = jl from Fin.ext (by have := j.isLt; simp [jl]; omega)]
      exact hlS
  intro m hm
  have hsum := eb.sum_repr ⟨m, hm⟩
  have hm' : m = ∑ j, (eb.repr ⟨m, hm⟩ j) • (eb j : V) := by
    have := congrArg Subtype.val hsum
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this.symm
  rw [hm']
  exact Submodule.sum_mem _ fun j _ => S.smul_mem _ (hall j)

theorem eq_one_of_normalizer (hK : ringChar K ≠ 2) {M F : Submodule K V} (hMF : IsCompl M F)
    (horth : ∀ m ∈ M, ∀ f ∈ F, polar Q m f = 0)
    (hMnd : (LinearMap.BilinForm.restrict Q.polarBilin M).Nondegenerate)
    (hFnd : (LinearMap.BilinForm.restrict Q.polarBilin F).Nondegenerate)
    (hM3 : 3 ≤ finrank K M) (hF3 : 3 ≤ finrank K F)
    {Y : Subgroup (V ≃ₗ[K] V)} (hYO : Y ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hYF : ∀ y ∈ Y, ∀ f ∈ F, y f = f)
    (hN : ∀ t s : V ≃ₗ[K] V,
      t ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      t * t = 1 → (∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id) → (∀ y ∈ Y, y * t = t * y) →
      s * t = t * s → s ∈ normalizer (Y : Set (V ≃ₗ[K] V))) :
    ∀ g ∈ Y, g = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card, Nat.odd_iff]
    exact FiniteField.odd_card_of_char_ne_two hK
  have hsymm : LinearMap.BilinForm.IsSymm Q.polarBilin :=
    ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  obtain ⟨hvalF, hbasF⟩ :=
    LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
      hodd rfl (by omega : 2 ≤ finrank K F) hFnd (hsymm.restrict F)
  obtain ⟨f0, hf0⟩ := hvalF 2 h2
  obtain ⟨eF, heFo, -, heFa, heFl⟩ := hbasF 2 f0 h2 hf0
  set i0 : Fin (finrank K F) := ⟨0, by omega⟩
  set i1 : Fin (finrank K F) := ⟨1, by omega⟩
  set i2 : Fin (finrank K F) := ⟨2, by omega⟩
  set e₁ : V := (eF i0 : V)
  set e₂ : V := (eF i1 : V)
  set y : V := (eF i2 : V)
  have hpolF : ∀ i j : Fin (finrank K F), i ≠ j → polar Q (eF i : V) (eF j : V) = 0 :=
    fun i j hij => heFo hij
  have hBF : ∀ i : Fin (finrank K F), polar Q (eF i : V) (eF i : V) ≠ 0 := by
    intro i
    rcases Nat.lt_or_ge (i : ℕ) (finrank K F - 1) with h | h
    · have := heFa i h
      change polar Q (eF i : V) (eF i : V) = 2 at this
      rw [this]
      exact h2
    · exact heFl i (by have := i.isLt; omega)
  have hQe₁ : Q e₁ = 1 := by
    have := heFa i0 (by simp [i0]; omega)
    change polar Q e₁ e₁ = 2 at this
    rw [polar_self_eq] at this
    exact (mul_eq_left₀ h2).mp (by rw [mul_comm]; linear_combination this)
  have hQe₂ : Q e₂ = 1 := by
    have := heFa i1 (by simp [i1]; omega)
    change polar Q e₂ e₂ = 2 at this
    rw [polar_self_eq] at this
    exact (mul_eq_left₀ h2).mp (by rw [mul_comm]; linear_combination this)
  have hQy : Q y ≠ 0 := by
    intro h0
    apply hBF i2
    change polar Q y y = 0
    rw [polar_self_eq, h0, mul_zero]
  have h01 : polar Q e₁ e₂ = 0 := hpolF i0 i1 (by simp [i0, i1, Fin.ext_iff])
  have h02 : polar Q e₁ y = 0 := hpolF i0 i2 (by simp [i0, i2, Fin.ext_iff])
  have h12 : polar Q e₂ y = 0 := hpolF i1 i2 (by simp [i1, i2, Fin.ext_iff])
  have hyF : y ∈ F := (eF i2).2
  have he₁F : e₁ ∈ F := (eF i0).2
  have he₂F : e₂ ∈ F := (eF i1).2
  have hQe₁0 : Q e₁ ≠ 0 := by rw [hQe₁]; exact one_ne_zero
  have hQe₂0 : Q e₂ ≠ 0 := by rw [hQe₂]; exact one_ne_zero
  set t : V ≃ₗ[K] V := reflect Q e₁ * reflect Q e₂
  have hc12 : reflect Q e₁ * reflect Q e₂ = reflect Q e₂ * reflect Q e₁ :=
    reflect_comm_of_polar_eq_zero h01
  have htΩ := reflect_mul_reflect_mem h2 hQe₁0 hQe₂0 ⟨1, by simp [hQe₁, hQe₂]⟩
  have htt : t * t = 1 := by
    change reflect Q e₁ * reflect Q e₂ * (reflect Q e₁ * reflect Q e₂) = 1
    calc reflect Q e₁ * reflect Q e₂ * (reflect Q e₁ * reflect Q e₂) =
        reflect Q e₁ * (reflect Q e₂ * reflect Q e₁) * reflect Q e₂ := by group
      _ = reflect Q e₁ * reflect Q e₁ * (reflect Q e₂ * reflect Q e₂) := by rw [← hc12]; group
      _ = 1 := by rw [reflect_mul_self, reflect_mul_self, one_mul]
  have ht1 : t e₁ = -e₁ := by
    change reflect Q e₁ (reflect Q e₂ e₁) = -e₁
    rw [reflect_apply_of_polar_eq_zero (v := e₂) (x := e₁) (by rw [polar_comm]; exact h01),
      reflect_apply hQe₁0, polar_self_eq, mul_div_assoc, div_self hQe₁0, mul_one, two_smul]
    abel
  have hty : t y = y := by
    change reflect Q e₁ (reflect Q e₂ y) = y
    rw [reflect_apply_of_polar_eq_zero (v := e₂) (x := y) h12,
      reflect_apply_of_polar_eq_zero (v := e₁) (x := y) h02]
  have htn : ∀ c : K, (t : V →ₗ[K] V) ≠ c • LinearMap.id := by
    intro c hc
    have hce : c • e₁ = -e₁ := by
      have := LinearMap.congr_fun hc e₁
      rw [LinearMap.smul_apply, LinearMap.id_apply] at this
      rw [← this]
      exact ht1
    have hcy : c • y = y := by
      have := LinearMap.congr_fun hc y
      rw [LinearMap.smul_apply, LinearMap.id_apply] at this
      rw [← this]
      exact hty
    have hy0 : y ≠ 0 := fun h0 => hQy (by rw [h0, QuadraticMap.map_zero])
    have hc1 : c = 1 := by
      have h3 : (c - 1) • y = 0 := by rw [sub_smul, hcy, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hy0)
    rw [hc1, one_smul] at hce
    have he0 : e₁ = 0 := by
      have h3 : (2 : K) • e₁ = 0 := by rw [two_smul]; nth_rewrite 1 [hce]; exact neg_add_cancel e₁
      exact (smul_eq_zero.mp h3).resolve_left h2
    exact hQe₁0 (by rw [he0, QuadraticMap.map_zero])
  have htY : ∀ g ∈ Y, g * t = t * g := by
    intro g hg
    have hgO := hYO hg
    have hfix₁ : g * reflect Q e₁ = reflect Q e₁ * g := by
      have h := reflect_conj hgO e₁
      rw [hYF g hg e₁ he₁F] at h
      calc g * reflect Q e₁ = g * reflect Q e₁ * g⁻¹ * g := by group
        _ = reflect Q e₁ * g := by rw [h]
    have hfix₂ : g * reflect Q e₂ = reflect Q e₂ * g := by
      have h := reflect_conj hgO e₂
      rw [hYF g hg e₂ he₂F] at h
      calc g * reflect Q e₂ = g * reflect Q e₂ * g⁻¹ * g := by group
        _ = reflect Q e₂ * g := by rw [h]
    change g * (reflect Q e₁ * reflect Q e₂) = reflect Q e₁ * reflect Q e₂ * g
    rw [← mul_assoc, hfix₁, mul_assoc, hfix₂, mul_assoc]
  obtain ⟨hvalM, -⟩ :=
    LocalAnalysis.ComponentInitial.finite_odd_symmetric_equal_value_orthogonal_basis
      hodd rfl (by omega : 2 ≤ finrank K M) hMnd (hsymm.restrict M)
  have hfixM : ∀ u : V, u ∈ M ∧ Q u = Q y → ∀ g ∈ Y, g u = u := by
    rintro u ⟨huM, hQu⟩ g hg
    have hQu0 : Q u ≠ 0 := by rw [hQu]; exact hQy
    have h4ne : (4 : K) ≠ 0 := by
      have h4 : (4 : K) = 2 * 2 := by norm_num
      rw [h4]
      exact mul_ne_zero h2 h2
    obtain ⟨z0, hz0⟩ := hvalM (4 * Q u) (mul_ne_zero h4ne hQu0)
    set z : V := (z0 : V)
    have hzM : z ∈ M := z0.2
    have hQz : Q z = 2 * Q u := by
      have h := hz0
      change polar Q z z = 4 * Q u at h
      rw [polar_self_eq] at h
      have h4 : (4 : K) = 2 * 2 := by norm_num
      rw [h4, mul_assoc] at h
      exact mul_left_cancel₀ h2 h
    have huy : polar Q u y = 0 := horth u huM y hyF
    have hu₁ : polar Q u e₁ = 0 := horth u huM e₁ he₁F
    have hu₂ : polar Q u e₂ = 0 := horth u huM e₂ he₂F
    have hz₁ : polar Q z e₁ = 0 := horth z hzM e₁ he₁F
    have hz₂ : polar Q z e₂ = 0 := horth z hzM e₂ he₂F
    have hzy : polar Q z y = 0 := horth z hzM y hyF
    have hQuy : Q (u - y) = 2 * Q u := by
      rw [map_sub_of_polar_eq_zero huy, ← hQu, two_mul]
    have hQuy0 : Q (u - y) ≠ 0 := by rw [hQuy]; exact mul_ne_zero h2 hQu0
    set s : V ≃ₗ[K] V := reflect Q (u - y) * reflect Q z
    have hsΩ : s ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
      reflect_mul_reflect_mem h2 hQuy0 (by rw [hQz]; exact mul_ne_zero h2 hQu0)
        ⟨2 * Q u, by rw [hQuy, hQz]⟩
    have hp1 : polar Q (u - y) e₁ = 0 := by
      rw [polar_sub_left, hu₁, polar_comm, h02, sub_zero]
    have hp2 : polar Q (u - y) e₂ = 0 := by
      rw [polar_sub_left, hu₂, polar_comm, h12, sub_zero]
    have hst : s * t = t * s := by
      have ha1 := reflect_comm_of_polar_eq_zero hp1
      have ha2 := reflect_comm_of_polar_eq_zero hp2
      have hb1 := reflect_comm_of_polar_eq_zero hz₁
      have hb2 := reflect_comm_of_polar_eq_zero hz₂
      change reflect Q (u - y) * reflect Q z * (reflect Q e₁ * reflect Q e₂) =
        reflect Q e₁ * reflect Q e₂ * (reflect Q (u - y) * reflect Q z)
      calc reflect Q (u - y) * reflect Q z * (reflect Q e₁ * reflect Q e₂) =
          reflect Q (u - y) * (reflect Q z * reflect Q e₁) * reflect Q e₂ := by group
        _ = reflect Q (u - y) * reflect Q e₁ * (reflect Q z * reflect Q e₂) := by
          rw [hb1]; group
        _ = reflect Q e₁ * reflect Q (u - y) * (reflect Q e₂ * reflect Q z) := by
          rw [ha1, hb2]
        _ = reflect Q e₁ * (reflect Q (u - y) * reflect Q e₂) * reflect Q z := by group
        _ = reflect Q e₁ * reflect Q e₂ * (reflect Q (u - y) * reflect Q z) := by
          rw [ha2]; group
    have hsN := hN t s htΩ hsΩ htt htn htY hst
    have hsy : s y = u := by
      change reflect Q (u - y) (reflect Q z y) = u
      rw [reflect_apply_of_polar_eq_zero (v := z) (x := y) hzy,
        reflect_sub_apply h2 huy hQu hQy]
    have hg' : s⁻¹ * g * s ∈ Y := by
      have := (mem_normalizer_iff.mp hsN (s⁻¹ * g * s)).mpr
      have e : s * (s⁻¹ * g * s) * s⁻¹ = g := by group
      rw [e] at this
      exact this hg
    have h3 := hYF _ hg' y hyF
    have h4 : s (s⁻¹ (g (s y))) = s y := by
      change s ((s⁻¹ * g * s) y) = s y
      rw [h3]
    rwa [LinearEquiv.apply_inv_apply', hsy] at h4
  intro g hg
  have hfixMall : ∀ m ∈ M, g m = m := by
    intro m hm
    have hspan := mem_span_norm hK hMnd hM3 hQy m hm
    have hle : Submodule.span K {u : V | u ∈ M ∧ Q u = Q y} ≤
        LinearMap.ker ((g : V →ₗ[K] V) - LinearMap.id) := by
      rw [Submodule.span_le]
      intro u hu
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        LinearEquiv.coe_coe, hfixM u hu g hg, sub_self]
    have := hle hspan
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      sub_eq_zero] at this
    exact this
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨m, hm, f, hf, rfl⟩ := Submodule.mem_sup.mp (hMF.sup_eq_top ▸ Submodule.mem_top :
    v ∈ M ⊔ F)
  rw [map_add, hfixMall m hm, hYF g hg f hf]
  rfl

end Main

end CFSG.ComponentClassification.OddClassSelector
