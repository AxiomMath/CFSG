module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.UnitEichler

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {p f : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  (h : UnitaryFieldData p f K) (G : Matrix ι ι K)

theorem Psi_smul (α β : K) (x y : ι → K) :
    Psi h G (α • x) (β • y) = h.bar β * α * hf h G y x - h.bar α * β * hf h G x y := by
  simp only [Psi, hf_smul_left, hf_smul_right]
  ring

theorem Psi_smul_left (α : K) (x y : ι → K) :
    Psi h G (α • x) y = α * hf h G y x - h.bar α * hf h G x y := by
  simp only [Psi, hf_smul_left, hf_smul_right]

theorem Psi_smul_right (β : K) (x y : ι → K) :
    Psi h G x (β • y) = h.bar β * hf h G y x - β * hf h G x y := by
  simp only [Psi, hf_smul_left, hf_smul_right]

theorem Psi_self (x : ι → K) : Psi h G x x = 0 := by simp [Psi]

private theorem bar_two_inv : h.bar (2⁻¹ : K) = 2⁻¹ := by
  rw [map_inv₀, map_ofNat]

theorem exists_hf_ne_zero (hdet : G.det ≠ 0) {v : ι → K} (hv0 : v ≠ 0) : ∃ w, hf h G v w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact hv0 (eq_zero_of_hf_eq_zero h G hdet hcon)

theorem exists_perp_hf_ne_zero (hdet : G.det ≠ 0) (hG : (G.map h.bar)ᵀ = G) {v u : ι → K}
    (hv0 : v ≠ 0) (huv : ∀ k : K, u ≠ k • v) : ∃ w, hf h G v w = 0 ∧ hf h G u w ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w₁, hw₁⟩ := exists_hf_ne_zero h G hdet hv0
  set k : K := hf h G u w₁ / hf h G v w₁ with hk
  have key : ∀ x, hf h G (u - h.bar k • v) x = 0 := by
    intro x
    set x' : ι → K := x - (hf h G v x / hf h G v w₁) • w₁ with hx'
    have h1 : hf h G v x' = 0 := by
      rw [hx', hf_sub_right, hf_smul_right]
      field_simp
      ring
    have h2 := hcon x' h1
    rw [hx', hf_sub_right, hf_smul_right] at h2
    rw [hf_sub_left, hf_smul_left, UnitaryFieldData.bar_bar, hk]
    field_simp
    field_simp at h2
    linear_combination h2
  have := eq_zero_of_hf_eq_zero h G hdet key
  exact huv (h.bar k) (sub_eq_zero.1 this)

theorem exists_partner_isotropic (h2 : (2 : K) ≠ 0) (hdet : G.det ≠ 0) (hG : (G.map h.bar)ᵀ = G)
    {v u : ι → K} (hv0 : v ≠ 0) (hu : hf h G v u = 0) (huu : hf h G u u = 0)
    (huv : ∀ k : K, u ≠ k • v) :
    ∃ w, hf h G v w = 0 ∧ hf h G u w = 1 ∧ hf h G w w = 0 := by
  obtain ⟨w₀, hv₀, hu₀⟩ := exists_perp_hf_ne_zero h G hdet hG hv0 huv
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : ι → K, w₁ = (hf h G u w₀)⁻¹ • w₀ := ⟨_, rfl⟩
  have h1 : hf h G u w₁ = 1 := by
    rw [hw₁, hf_smul_right, inv_mul_cancel₀ hu₀]
  have h3 : hf h G v w₁ = 0 := by rw [hw₁, hf_smul_right, hv₀, mul_zero]
  have h4 : hf h G w₁ u = 1 := by
    rw [← map_hf h G hG u w₁, h1, map_one]
  obtain ⟨c, hc⟩ : ∃ c : K, c = 2⁻¹ * hf h G w₁ w₁ := ⟨_, rfl⟩
  have hbc : h.bar c = c := by
    rw [hc, map_mul, bar_two_inv, hf_self_bar h G hG]
  refine ⟨w₁ - c • u, ?_, ?_, ?_⟩
  · rw [hf_sub_right, hf_smul_right, h3, hu]; ring
  · rw [hf_sub_right, hf_smul_right, h1, huu]; ring
  · simp only [hf_sub_right, hf_sub_left, hf_smul_left, hf_smul_right, h4, h1, huu, hbc]
    have := mul_inv_cancel₀ h2
    rw [hc] at *
    linear_combination (-hf h G w₁ w₁) * this

structure SympSys (v : ι → K) (a b : Fin 2 → ι → K) (ι₀ : K) : Prop where
  ha : ∀ i, hf h G v (a i) = 0
  hb : ∀ i, hf h G v (b i) = 0
  hι : ι₀ + h.bar ι₀ = 0
  hι0 : ι₀ ≠ 0
  haa : ∀ i j, Psi h G (a i) (a j) = 0
  hbb : ∀ i j, i ≠ j → Psi h G (b i) (b j) = 0
  hab : ∀ i j, i ≠ j → Psi h G (a i) (b j) = 0
  hii : ∀ i, Psi h G (a i) (b i) = ι₀

theorem exists_symp_system_isotropic (h2 : (2 : K) ≠ 0) (hdet : G.det ≠ 0)
    (hG : (G.map h.bar)ᵀ = G) {v u : ι → K} (hv0 : v ≠ 0) (hv : hf h G v v = 0)
    (hu : hf h G v u = 0) (huu : hf h G u u = 0) (huv : ∀ k : K, u ≠ k • v) :
    ∃ (a b : Fin 2 → ι → K) (ι₀ : K), a 0 = u ∧ SympSys h G v a b ι₀ := by
  obtain ⟨w, hvw, huw, hww⟩ := exists_partner_isotropic h G h2 hdet hG hv0 hu huu huv
  obtain ⟨ι₀, hι, hι0⟩ := h.exists_mem_traceZero_ne_zero
  rw [UnitaryFieldData.mem_traceZero] at hι
  have hbι : h.bar ι₀ = -ι₀ := by
    have : ι₀ + h.bar ι₀ = 0 := hι
    linear_combination this
  have hwu : hf h G w u = 1 := by rw [← map_hf h G hG u w, huw, map_one]
  have hb2 : h.bar (2⁻¹ * ι₀) = -(2⁻¹ * ι₀) := by
    rw [map_mul, bar_two_inv, hbι]; ring
  have hi2 : (2⁻¹ : K) * 2 = 1 := inv_mul_cancel₀ h2
  obtain ⟨α, hα⟩ : ∃ α : K, α = 2⁻¹ * ι₀ := ⟨_, rfl⟩
  rw [← hα] at hb2
  have hα2 : α + α = ι₀ := by rw [hα]; linear_combination ι₀ * hi2
  have hbα : h.bar α = -α := hb2
  have f1 : Psi h G u (α • u) = 0 := by rw [Psi_smul_right, huu]; ring
  have f2 : Psi h G (α • u) u = 0 := by rw [Psi_smul_left, huu]; ring
  have g1 : Psi h G ((-α) • w) w = 0 := by rw [Psi_smul_left, hww]; ring
  have g2 : Psi h G w ((-α) • w) = 0 := by rw [Psi_smul_right, hww]; ring
  have c1 : Psi h G u w = 0 := by rw [Psi, hwu, huw]; ring
  have c2 : Psi h G (α • u) ((-α) • w) = 0 := by
    rw [Psi_smul, hwu, huw, map_neg, hbα]; ring
  have d1 : Psi h G u ((-α) • w) = ι₀ := by
    have := Psi_smul h G 1 (-α) u w
    rw [one_smul] at this
    rw [this, hwu, huw, map_neg, hbα, map_one]
    linear_combination hα2
  have d2 : Psi h G (α • u) w = ι₀ := by
    have := Psi_smul h G α 1 u w
    rw [one_smul] at this
    rw [this, hwu, huw, map_one, hbα]
    linear_combination hα2
  refine ⟨![u, α • u], ![(-α) • w, w], ι₀, rfl, ?_⟩
  refine ⟨?_, ?_, hι, hι0, ?_, ?_, ?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact hu
    · show hf h G v (α • u) = 0
      rw [hf_smul_right, hu, mul_zero]
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show hf h G v ((-α) • w) = 0
      rw [hf_smul_right, hvw, mul_zero]
    · exact hvw
  · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · exact Psi_self h G u
    · exact f1
    · exact f2
    · exact Psi_self h G _
  · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · intro h0; exact absurd rfl h0
    · intro _; exact g1
    · intro _; exact g2
    · intro h0; exact absurd rfl h0
  · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · intro h0; exact absurd rfl h0
    · intro _; exact c1
    · intro _; exact c2
    · intro h0; exact absurd rfl h0
  · refine Fin.forall_fin_two.2 ⟨d1, d2⟩

open CFSG.LinearGroups in
theorem exists_symp_system_aniso (h2 : (2 : K) ≠ 0) (hdet : G.det ≠ 0)
    (hG : (G.map h.bar)ᵀ = G) (hcard : Fintype.card ι = 4) {v u : ι → K} (hv0 : v ≠ 0)
    (hv : hf h G v v = 0) (hu : hf h G v u = 0) (huu : hf h G u u ≠ 0) :
    ∃ (a b : Fin 2 → ι → K) (ι₀ : K), a 0 = u ∧ SympSys h G v a b ι₀ := by
  have hB : (gramForm h G).IsSymm := gramForm_isSymm h hG
  have hBl : (gramForm h G).SeparatingLeft := gramForm_separatingLeft h hdet
  obtain ⟨⟨v', hvv', hv'v'⟩, hsplit⟩ := hermitian_hyperbolic_splitting h hB hBl hv0 hv
  obtain ⟨-, -, hcompl, hWsep, hWdim⟩ := hsplit v' hvv' hv'v'
  have hvv'' : hf h G v v' = 1 := hvv'
  have hv'v'' : hf h G v' v' = 0 := hv'v'
  set S : Submodule K (ι → K) := Submodule.span K {v, v'} with hS
  set W : Submodule K (ι → K) := S.orthogonalBilin (gramForm h G) with hW
  have hfin : Module.finrank K (ι → K) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  have hdimW : Module.finrank K W = 2 := by rw [hWdim, hfin]
  obtain ⟨e, he⟩ := h.exists_orthonormal_basis (hB.domRestrict _) hWsep
  generalize hn : Module.finrank K W = n at e he
  have hn2 : n = 2 := hn.symm.trans hdimW
  subst hn2
  have hWperp : ∀ x ∈ W, hf h G v x = 0 ∧ hf h G v' x = 0 := by
    intro x hx
    rw [hW, Submodule.mem_orthogonalBilin] at hx
    exact ⟨hx v (Submodule.subset_span (by simp)), hx v' (Submodule.subset_span (by simp))⟩
  have hornt : ∀ i j : Fin 2, hf h G (e i : ι → K) (e j : ι → K) = if i = j then 1 else 0 := by
    intro i j
    have := he i j
    rwa [LinearMap.domRestrict₁₂_apply] at this
  have hu_mem : u ∈ S ⊔ W := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨s₀, hs₀, w', hw', hsw⟩ := Submodule.mem_sup.1 hu_mem
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.1 hs₀
  have hβ : β = 0 := by
    have h1 : hf h G v u = β * hf h G v v' + hf h G v w' := by
      rw [← hsw, ← hαβ, hf_add_right, hf_add_right, hf_smul_right, hf_smul_right, hv]
      ring
    rw [hu, hvv'', (hWperp w' hw').1] at h1
    linear_combination -h1
  rw [hβ, zero_smul, add_zero] at hαβ
  set x : Fin 2 → K := fun i => e.repr ⟨w', hw'⟩ i with hx
  have hw'e : w' = x 0 • (e 0 : ι → K) + x 1 • (e 1 : ι → K) := by
    have := e.sum_repr ⟨w', hw'⟩
    rw [Fin.sum_univ_two] at this
    have h3 := congrArg (fun z : W => (z : ι → K)) this
    simpa [hx] using h3.symm
  have hve : ∀ i, hf h G v (e i : ι → K) = 0 := fun i => (hWperp _ (e i).2).1
  have hev : ∀ i, hf h G (e i : ι → K) v = 0 := fun i => by
    have := map_hf h G hG v (e i : ι → K)
    rw [hve i, map_zero] at this
    exact this.symm
  have hvw' : hf h G v w' = 0 := (hWperp w' hw').1
  have hw'v : hf h G w' v = 0 := by
    have := map_hf h G hG v w'
    rw [hvw', map_zero] at this
    exact this.symm
  have hu_eq : u = α • v + w' := by rw [← hsw, ← hαβ]
  have hww' : hf h G w' w' = h.bar (x 0) * x 0 + h.bar (x 1) * x 1 := by
    conv_lhs => rw [hw'e]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hornt]
    simp
    ring
  have huu' : hf h G u u = h.bar (x 0) * x 0 + h.bar (x 1) * x 1 := by
    rw [hu_eq, hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right,
      hf_smul_right, hv, hvw', hw'v, hww']
    ring
  obtain ⟨w, hw⟩ : ∃ w : ι → K, w = h.bar (x 1) • (e 0 : ι → K) - h.bar (x 0) • (e 1 : ι → K) :=
    ⟨_, rfl⟩
  have hvw : hf h G v w = 0 := by
    rw [hw, hf_sub_right, hf_smul_right, hf_smul_right, hve, hve]; ring
  have hwv : hf h G w v = 0 := by
    have := map_hf h G hG v w
    rw [hvw, map_zero] at this
    exact this.symm
  have huw : hf h G u w = 0 := by
    rw [hu_eq, hw, hf_add_left, hf_smul_left, hf_sub_right, hf_smul_right, hf_smul_right, hve,
      hve]
    rw [hw'e]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hf_sub_right, hornt]
    try simp only [map_neg, UnitaryFieldData.bar_bar]
    simp
    ring
  have hwu : hf h G w u = 0 := by
    have := map_hf h G hG u w
    rw [huw, map_zero] at this
    exact this.symm
  have hww : hf h G w w = hf h G u u := by
    rw [huu', hw]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hf_sub_left, hf_sub_right,
      hornt]
    try simp only [map_neg, map_sub, UnitaryFieldData.bar_bar]
    simp
    ring
  obtain ⟨ι₀, hι, hι0⟩ := h.exists_mem_traceZero_ne_zero
  rw [UnitaryFieldData.mem_traceZero] at hι
  have hι' : ι₀ + h.bar ι₀ = 0 := hι
  have hbι : h.bar ι₀ = -ι₀ := by linear_combination hι'
  set N : K := hf h G u u with hN
  have hbN : h.bar N = N := hf_self_bar h G hG u
  have hN2 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hNN : N * N⁻¹ = 1 := mul_inv_cancel₀ huu
  obtain ⟨γ, hγ⟩ : ∃ γ : K, γ = -(2⁻¹ * N⁻¹ * ι₀) := ⟨_, rfl⟩
  have hbγ : h.bar γ = -γ := by
    rw [hγ, map_neg, map_mul, map_mul, bar_two_inv, map_inv₀, hbN, hbι]; ring
  have hΨ : h.bar γ * N - γ * N = ι₀ := by
    rw [hbγ, hγ]
    linear_combination (ι₀ * N * N⁻¹) * hN2 + ι₀ * hNN
  have e1 : Psi h G u (γ • u) = ι₀ := by rw [Psi_smul_right]; exact hΨ
  have e2 : Psi h G w (γ • w) = ι₀ := by rw [Psi_smul_right, hww]; exact hΨ
  have c1 : Psi h G u w = 0 := by rw [Psi, hwu, huw]; ring
  have c2 : Psi h G w u = 0 := by rw [Psi, hwu, huw]; ring
  have c3 : Psi h G u (γ • w) = 0 := by rw [Psi_smul_right, hwu, huw]; ring
  have c4 : Psi h G w (γ • u) = 0 := by rw [Psi_smul_right, hwu, huw]; ring
  have c5 : Psi h G (γ • u) (γ • w) = 0 := by rw [Psi_smul, hwu, huw]; ring
  have c6 : Psi h G (γ • w) (γ • u) = 0 := by rw [Psi_smul, hwu, huw]; ring
  refine ⟨![u, w], ![γ • u, γ • w], ι₀, rfl, ?_⟩
  refine ⟨?_, ?_, hι', hι0, ?_, ?_, ?_, ?_⟩
  · refine Fin.forall_fin_two.2 ⟨hu, hvw⟩
  · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show hf h G v (γ • u) = 0
      rw [hf_smul_right, hu, mul_zero]
    · show hf h G v (γ • w) = 0
      rw [hf_smul_right, hvw, mul_zero]
  · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · exact Psi_self h G u
    · exact c1
    · exact c2
    · exact Psi_self h G w
  · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · intro h0; exact absurd rfl h0
    · intro _; exact c5
    · intro _; exact c6
    · intro h0; exact absurd rfl h0
  · refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · intro h0; exact absurd rfl h0
    · intro _; exact c3
    · intro _; exact c4
    · intro h0; exact absurd rfl h0
  · exact Fin.forall_fin_two.2 ⟨e1, e2⟩

theorem exists_symp_system (h2 : (2 : K) ≠ 0) (hdet : G.det ≠ 0) (hG : (G.map h.bar)ᵀ = G)
    (hcard : Fintype.card ι = 4) {v u : ι → K} (hv0 : v ≠ 0) (hv : hf h G v v = 0)
    (hu : hf h G v u = 0) (huv : ∀ k : K, u ≠ k • v) :
    ∃ (a b : Fin 2 → ι → K) (ι₀ : K), a 0 = u ∧ SympSys h G v a b ι₀ := by
  by_cases huu : hf h G u u = 0
  · exact exists_symp_system_isotropic h G h2 hdet hG hv0 hv hu huu huv
  · exact exists_symp_system_aniso h G h2 hdet hG hcard hv0 hv hu huu

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
