module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Lemma610
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt
public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open scoped commutatorElement

section Group

theorem commute_of_perfect_of_map_commute {S X : Type} [Group S] [Group X] (ψ : S →* X)
    (hker : ψ.ker ≤ Subgroup.center S) {R : Subgroup S} (hR : ⁅R, R⁆ = R) {a : S}
    (h : ∀ r ∈ R, Commute (ψ a) (ψ r)) : ∀ r ∈ R, Commute a r := by
  have hk : ∀ r ∈ R, ⁅a, r⁆ ∈ Subgroup.center S := fun r hr => hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (h r hr).eq)
  have hconj : ∀ r ∈ R, a * r * a⁻¹ = r * ⁅a, r⁆ := fun r hr => by
    have := Subgroup.mem_center_iff.mp (hk r hr) r
    rw [commutatorElement_def] at this ⊢
    calc a * r * a⁻¹ = (a * r * a⁻¹ * r⁻¹) * r := by group
      _ = r * (a * r * a⁻¹ * r⁻¹) := this.symm
  have key : ⁅R, R⁆ ≤ Subgroup.centralizer ({a} : Set S) := by
    refine Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅a * g₁ * a⁻¹, a * g₂ * a⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : ⁅a * g₁ * a⁻¹, a * g₂ * a⁻¹⁆ = ⁅g₁, g₂⁆ := by
      rw [hconj g₁ hg₁, hconj g₂ hg₂]
      exact RouteD.Gaps.commutator_mul_central g₁ g₂ _ _ (hk g₁ hg₁) (hk g₂ hg₂)
    have : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅g₁, g₂⁆ := e.trans e2
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  intro r hr
  have := Subgroup.mem_centralizer_singleton_iff.mp (key (hR ▸ hr))
  exact (this.symm : Commute a r)

end Group

end CFSG.ClassicalInvolution.RouteD.TwinSmall

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.ModelFacts.OrthAut

section Mixed

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem Frame.mem_span_iff_comb (F : Frame Q) {x : V} :
    x ∈ F.span ↔ ∃ a b c d : K, x = a • F.e₁ + b • F.f₁ + c • F.e₂ + d • F.f₂ := by
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨X 0 0, X 1 1, -X 0 1, X 1 0, rfl⟩
  · rintro ⟨a, b, c, d, rfl⟩
    refine ⟨!![a, -c; d, b], ?_⟩
    simp [Frame.incl_apply]

theorem Frame.polar_span_of_vecs (F : Frame Q) {y : V} (h1 : polar Q F.e₁ y = 0)
    (h2 : polar Q F.f₁ y = 0) (h3 : polar Q F.e₂ y = 0) (h4 : polar Q F.f₂ y = 0) :
    ∀ x ∈ F.span, polar Q x y = 0 := by
  intro x hx
  obtain ⟨a, b, c, d, rfl⟩ := (Frame.mem_span_iff_comb F).mp hx
  simp only [polar_add_left, polar_smul_left, h1, h2, h3, h4, smul_zero, add_zero]

theorem orth_symm' {A B : Submodule K V} (h : ∀ x ∈ A, ∀ y ∈ B, polar Q x y = 0) :
    ∀ x ∈ B, ∀ y ∈ A, polar Q x y = 0 := fun x hx y hy => by
  rw [polar_comm]
  exact h y hy x hx

theorem polarNondegOn_three (F₀ F₁ F₂ : Frame Q)
    (h01 : ∀ x ∈ F₀.span, ∀ y ∈ F₁.span, polar Q x y = 0)
    (h02 : ∀ x ∈ F₀.span, ∀ y ∈ F₂.span, polar Q x y = 0)
    (h12 : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar Q x y = 0) :
    PolarNondegOn Q (F₀.span ⊔ F₁.span ⊔ F₂.span) := by
  have h10 := orth_symm' h01
  have h20 := orth_symm' h02
  have h21 := orth_symm' h12
  intro x hx hxo
  obtain ⟨w, hw, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Submodule.mem_sup.mp hw
  have o0 : ∀ y ∈ F₀.span, polar Q u₀ y = 0 := fun y hy => by
    have := hxo y (Submodule.mem_sup_left (Submodule.mem_sup_left hy))
    rw [polar_add_left, polar_add_left, h10 u₁ hu₁ y hy, h20 u₂ hu₂ y hy] at this
    simpa using this
  have o1 : ∀ y ∈ F₁.span, polar Q u₁ y = 0 := fun y hy => by
    have := hxo y (Submodule.mem_sup_left (Submodule.mem_sup_right hy))
    rw [polar_add_left, polar_add_left, h01 u₀ hu₀ y hy, h21 u₂ hu₂ y hy] at this
    simpa using this
  have o2 : ∀ y ∈ F₂.span, polar Q u₂ y = 0 := fun y hy => by
    have := hxo y (Submodule.mem_sup_right hy)
    rw [polar_add_left, polar_add_left, h02 u₀ hu₀ y hy, h12 u₁ hu₁ y hy] at this
    simpa using this
  rw [F₀.polarNondegOn_span u₀ hu₀ o0, F₁.polarNondegOn_span u₁ hu₁ o1,
    F₂.polarNondegOn_span u₂ hu₂ o2]
  simp

variable [FiniteDimensional K V]

theorem exists_perp_vec (hQ : (polarBilin Q).Nondegenerate) (F₀ F₁ F₂ : Frame Q)
    (h01 : ∀ x ∈ F₀.span, ∀ y ∈ F₁.span, polar Q x y = 0)
    (h02 : ∀ x ∈ F₀.span, ∀ y ∈ F₂.span, polar Q x y = 0)
    (h12 : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar Q x y = 0)
    (hdim : 13 ≤ Module.finrank K V) :
    ∃ a : V, a ≠ 0 ∧ Q a ≠ 0 ∧ (∀ y ∈ F₀.span, polar Q a y = 0) ∧
      (∀ y ∈ F₁.span, polar Q a y = 0) ∧ ∀ y ∈ F₂.span, polar Q a y = 0 := by
  classical
  have h10 := orth_symm' h01
  have h20 := orth_symm' h02
  have h21 := orth_symm' h12
  set S : Submodule K V := F₀.span ⊔ F₁.span ⊔ F₂.span with hS
  have hnd : PolarNondegOn Q S := polarNondegOn_three F₀ F₁ F₂ h01 h02 h12
  have d01 : Disjoint F₀.span F₁.span := by
    rw [Submodule.disjoint_def]
    intro x hx0 hx1
    exact F₀.polarNondegOn_span x hx0 fun y hy => by rw [polar_comm]; exact h01 y hy x hx1
  have d012 : Disjoint (F₀.span ⊔ F₁.span) F₂.span := by
    rw [Submodule.disjoint_def]
    intro x hx hx2
    refine F₂.polarNondegOn_span x hx2 fun y hy => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    rw [polar_add_left, h02 u hu y hy, h12 v hv y hy, add_zero]
  have hS12 : Module.finrank K S = 12 := by
    rw [hS, Frame.finrank_sup_of_disjoint d012, Frame.finrank_sup_of_disjoint d01,
      Frame.finrank_span, Frame.finrank_span, Frame.finrank_span]
  set T := LinearMap.BilinForm.orthogonal (polarBilin Q) S with hT
  have hT1 : Module.finrank K T = Module.finrank K V - Module.finrank K S :=
    LinearMap.BilinForm.finrank_orthogonal hQ S
  have hSle : Module.finrank K S ≤ Module.finrank K V := Submodule.finrank_le S
  have hTmem : ∀ x, x ∈ T ↔ ∀ y ∈ S, polar Q y x = 0 := fun x => by
    rw [hT, LinearMap.BilinForm.mem_orthogonal_iff]
    rfl
  have hST : S ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxT⟩
    exact hnd x hxS fun y hy => by rw [polar_comm]; exact (hTmem x).mp hxT y hy
  have hsup : S ⊔ T = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have := Submodule.finrank_sup_add_finrank_inf_eq S T
    rw [hST, finrank_bot] at this
    omega
  obtain ⟨a₀, ha₀, ha₀0⟩ : ∃ a₀ ∈ T, a₀ ≠ 0 := by
    have : 0 < Module.finrank K T := by omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot (fun h => by rw [h, finrank_bot] at this; omega)
  obtain ⟨v, hv⟩ : ∃ v, polar Q a₀ v ≠ 0 := by
    by_contra h
    push Not at h
    exact ha₀0 (eq_zero_of_polar_eq_zero hQ h)
  have hv' : v ∈ S ⊔ T := hsup ▸ Submodule.mem_top
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hv'
  have hst : polar Q a₀ t ≠ 0 := by
    rw [polar_add_right, polar_comm Q a₀ s, (hTmem a₀).mp ha₀ s hs, zero_add] at hv
    exact hv
  have key : ∀ a ∈ T, (∀ y ∈ F₀.span, polar Q a y = 0) ∧ (∀ y ∈ F₁.span, polar Q a y = 0) ∧
      ∀ y ∈ F₂.span, polar Q a y = 0 := fun a ha =>
    ⟨fun y hy => by rw [polar_comm]; exact (hTmem a).mp ha y (Submodule.mem_sup_left
        (Submodule.mem_sup_left hy)),
     fun y hy => by rw [polar_comm]; exact (hTmem a).mp ha y (Submodule.mem_sup_left
        (Submodule.mem_sup_right hy)),
     fun y hy => by rw [polar_comm]; exact (hTmem a).mp ha y (Submodule.mem_sup_right hy)⟩
  have hpol : polar Q a₀ t = Q (a₀ + t) - Q a₀ - Q t := rfl
  by_cases h1 : Q a₀ = 0
  · by_cases h2' : Q t = 0
    · have h3 : Q (a₀ + t) ≠ 0 := by
        intro h3
        rw [h3, h1, h2'] at hpol
        simp at hpol
        exact hst hpol
      have hat : a₀ + t ∈ T := T.add_mem ha₀ ht
      refine ⟨a₀ + t, ?_, h3, (key _ hat).1, (key _ hat).2.1, (key _ hat).2.2⟩
      intro h0
      exact h3 (by rw [h0]; simp)
    · refine ⟨t, ?_, h2', (key t ht).1, (key t ht).2.1, (key t ht).2.2⟩
      intro h0
      exact h2' (by rw [h0]; simp)
  · exact ⟨a₀, ha₀0, h1, (key a₀ ha₀).1, (key a₀ ha₀).2.1, (key a₀ ha₀).2.2⟩

variable (h2 : (2 : K) ≠ 0)

include h2 in
theorem exists_mixed_frame (hQ : (polarBilin Q).Nondegenerate) (F₀ F₁ F₂ : Frame Q)
    (h01 : ∀ x ∈ F₀.span, ∀ y ∈ F₁.span, polar Q x y = 0)
    (h02 : ∀ x ∈ F₀.span, ∀ y ∈ F₂.span, polar Q x y = 0)
    (h12 : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar Q x y = 0)
    (hdim : 13 ≤ Module.finrank K V) :
    ∃ F : Frame Q, (∀ x ∈ F.span, ∀ y ∈ F₀.span, polar Q x y = 0) ∧
      (∃ e ∈ F.span, e ≠ 0 ∧ e ∈ F₁.span ∧ ∀ y ∈ F₂.span, polar Q e y = 0) ∧
      (∃ a ∈ F.span, a ≠ 0 ∧ (∀ y ∈ F₁.span, polar Q a y = 0) ∧
        ∀ y ∈ F₂.span, polar Q a y = 0) ∧
      ∃ e' ∈ F.span, ∃ f' ∈ F₁.span, polar Q e' f' = 1 := by
  classical
  obtain ⟨a, ha0, hQa, ha₀, ha₁, ha₂⟩ := exists_perp_vec hQ F₀ F₁ F₂ h01 h02 h12 hdim
  obtain ⟨lam, hlam⟩ : ∃ lam : K, lam * Q a = -1 :=
    ⟨-(Q a)⁻¹, by rw [neg_mul, inv_mul_cancel₀ hQa]⟩
  set b : V := F₁.e₂ + lam • F₁.f₂ with hb
  have hbspan : b ∈ F₁.span := F₁.span.add_mem F₁.e₂_mem_span (F₁.span.smul_mem _ F₁.f₂_mem_span)
  have hab : polar Q a b = 0 := ha₁ b hbspan
  have hba : polar Q b a = 0 := by rw [polar_comm]; exact hab
  have hQb : Q b = lam := by
    rw [hb, QuadraticMap.map_add Q, QuadraticMap.map_smul, F₁.Q_e₂, polar_smul_right]
    simp [F₁.Q_f₂, F₁.polar_e₂_f₂]
  have hqa4 : (4 * Q a : K) ≠ 0 := by
    have : (4 : K) ≠ 0 := by
      have h22 : (4 : K) = 2 * 2 := by norm_num
      rw [h22]
      exact mul_ne_zero h2 h2
    exact mul_ne_zero this hQa
  have hQe : Q (a + (Q a) • b) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hab, hQb]
    simp only [smul_eq_mul, mul_zero, add_zero]
    linear_combination (Q a) * hlam
  have hQf : Q (a + (-Q a) • b) = 0 := by
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, polar_smul_right, hab, hQb]
    simp only [smul_eq_mul, mul_zero, add_zero]
    linear_combination (Q a) * hlam
  have hpol : polar Q (a + (Q a) • b) ((4 * Q a)⁻¹ • (a + (-Q a) • b)) = 1 := by
    simp only [polar_smul_right, polar_add_left, polar_add_right, polar_smul_left, hab, hba,
      polar_self, hQb, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero,
      zero_add, Nat.cast_ofNat]
    rw [inv_mul_eq_iff_eq_mul₀ hqa4, mul_one]
    linear_combination (-2 * Q a) * hlam
  have hea : polar Q F₁.e₁ a = 0 := by rw [polar_comm]; exact ha₁ _ F₁.e₁_mem_span
  have hfa : polar Q F₁.f₁ a = 0 := by rw [polar_comm]; exact ha₁ _ F₁.f₁_mem_span
  have heb : polar Q F₁.e₁ b = 0 := by
    rw [hb, polar_add_right, polar_smul_right, F₁.polar_e₁_e₂, F₁.polar_e₁_f₂]; simp
  have hfb : polar Q F₁.f₁ b = 0 := by
    rw [hb, polar_add_right, polar_smul_right, F₁.polar_f₁_e₂, F₁.polar_f₁_f₂]; simp
  let P' : HypPair Q :=
    ⟨a + (Q a) • b, (4 * Q a)⁻¹ • (a + (-Q a) • b), hQe,
      by rw [QuadraticMap.map_smul, hQf, smul_zero], hpol⟩
  have horth : F₁.P.Orth P' :=
    ⟨by show polar Q F₁.e₁ (a + (Q a) • b) = 0
        rw [polar_add_right, polar_smul_right, hea, heb]; simp,
     by show polar Q F₁.e₁ ((4 * Q a)⁻¹ • (a + (-Q a) • b)) = 0
        rw [polar_smul_right, polar_add_right, polar_smul_right, hea, heb]; simp,
     by show polar Q F₁.f₁ (a + (Q a) • b) = 0
        rw [polar_add_right, polar_smul_right, hfa, hfb]; simp,
     by show polar Q F₁.f₁ ((4 * Q a)⁻¹ • (a + (-Q a) • b)) = 0
        rw [polar_smul_right, polar_add_right, polar_smul_right, hfa, hfb]; simp⟩
  let F : Frame Q := ⟨F₁.P, P', horth⟩
  have hF0 : ∀ y ∈ F₀.span, polar Q F.e₁ y = 0 ∧ polar Q F.f₁ y = 0 ∧ polar Q F.e₂ y = 0 ∧
      polar Q F.f₂ y = 0 := by
    intro y hy
    have hb0 : polar Q b y = 0 := orth_symm' h01 b hbspan y hy
    refine ⟨orth_symm' h01 _ F₁.e₁_mem_span y hy, orth_symm' h01 _ F₁.f₁_mem_span y hy, ?_, ?_⟩
    · show polar Q (a + (Q a) • b) y = 0
      rw [polar_add_left, polar_smul_left, ha₀ y hy, hb0]
      simp
    · show polar Q ((4 * Q a)⁻¹ • (a + (-Q a) • b)) y = 0
      rw [polar_smul_left, polar_add_left, polar_smul_left, ha₀ y hy, hb0]
      simp
  refine ⟨F, fun x hx y hy => ?_, ⟨F₁.e₁, F.e₁_mem_span, F₁.P.e_ne_zero, F₁.e₁_mem_span,
    fun y hy => h12 _ F₁.e₁_mem_span y hy⟩, ⟨a, ?_, ha0, ha₁, ha₂⟩,
    ⟨F₁.e₁, F.e₁_mem_span, F₁.f₁, F₁.f₁_mem_span, F₁.polar_e₁_f₁⟩⟩
  · exact Frame.polar_span_of_vecs F (hF0 y hy).1 (hF0 y hy).2.1 (hF0 y hy).2.2.1
      (hF0 y hy).2.2.2 x hx
  · have h4 : (4 : K) ≠ 0 := left_ne_zero_of_mul hqa4
    have e1 : F.e₂ + (4 * Q a) • F.f₂ = (2 : K) • a := by
      show (a + (Q a) • b) + (4 * Q a) • ((4 * Q a)⁻¹ • (a + (-Q a) • b)) = (2 : K) • a
      rw [smul_smul, mul_inv_cancel₀ hqa4, one_smul]
      module
    have e2 : a = (2 : K)⁻¹ • (F.e₂ + (4 * Q a) • F.f₂) := by
      rw [e1, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [e2]
    exact F.span.smul_mem _ (F.span.add_mem F.e₂_mem_span (F.span.smul_mem _ F.f₂_mem_span))

end Mixed

section Opposite

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_frame_of_neg_planes (h2 : (2 : K) ≠ 0) (ι α : (Fin 2 → K) →ₗ[K] V)
    (hQ : ∀ x, Q (ι x) = -Q (α x)) (horth : ∀ x y, polar Q (ι x) (α y) = 0)
    (w w' : Fin 2 → Fin 2 → K)
    (hdual : ∀ i j, polar Q (α (w i)) (α (w' j)) = if i = j then 1 else 0)
    (hw : ∀ x : Fin 2 → K, ∃ a b : K, x = a • w 0 + b • w 1)
    (hw' : ∀ x : Fin 2 → K, ∃ a b : K, x = a • w' 0 + b • w' 1) :
    ∃ F : Frame Q, (∀ x, ι x ∈ F.span) ∧ (∀ x, α x ∈ F.span) ∧
      F.span ≤ LinearMap.range ι ⊔ LinearMap.range α := by
  have hpol : ∀ x y, polar Q (ι x) (ι y) = -polar Q (α x) (α y) := fun x y => by
    have h1 : polar Q (ι x) (ι y) = Q (ι (x + y)) - Q (ι x) - Q (ι y) := by
      rw [map_add]
      rfl
    have h2' : polar Q (α x) (α y) = Q (α (x + y)) - Q (α x) - Q (α y) := by
      rw [map_add]
      rfl
    rw [h1, h2', hQ, hQ, hQ]
    ring
  have hcross : ∀ x y, polar Q (α x) (ι y) = 0 := fun x y => by
    rw [polar_comm]
    exact horth y x
  have hQe : ∀ x, Q (ι x + α x) = 0 := fun x => by
    rw [QuadraticMap.map_add Q, hQ]
    have := horth x x
    simp [this]
  have hQf : ∀ x, Q (ι x - α x) = 0 := fun x => by
    rw [sub_eq_add_neg, QuadraticMap.map_add Q, polar_neg_right, QuadraticMap.map_neg, hQ]
    have := horth x x
    simp [this]
  obtain ⟨e, he⟩ : ∃ e : Fin 2 → V, ∀ i, e i = ι (w i) + α (w i) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin 2 → V, ∀ j, g j = ι (w' j) - α (w' j) := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : Fin 2 → V, ∀ j, f j = (-(2 : K)⁻¹) • g j := ⟨_, fun _ => rfl⟩
  have hQe' : ∀ i, Q (e i) = 0 := fun i => by rw [he]; exact hQe _
  have hQf' : ∀ j, Q (f j) = 0 := fun j => by
    rw [hf, QuadraticMap.map_smul, hg, hQf, smul_zero]
  have hef : ∀ i j, polar Q (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hf, polar_smul_right]
    have : polar Q (e i) (g j) = -2 * polar Q (α (w i)) (α (w' j)) := by
      simp only [he, hg, polar_add_left, polar_sub_right, hpol, hcross, horth]
      ring
    rw [this, hdual]
    simp only [smul_eq_mul]
    split_ifs
    · field_simp
    · simp
  have hee : ∀ i j, polar Q (e i) (e j) = 0 := fun i j => by
    simp only [he, polar_add_left, polar_add_right, hpol, hcross, horth]
    ring
  have hff : ∀ i j, polar Q (f i) (f j) = 0 := fun i j => by
    simp only [hf, polar_smul_left, polar_smul_right, hg, polar_sub_left, polar_sub_right, hpol,
      hcross, horth]
    ring
  let P : HypPair Q := ⟨e 0, f 0, hQe' _, hQf' 0, by rw [hef]; simp⟩
  let P' : HypPair Q := ⟨e 1, f 1, hQe' _, hQf' 1, by rw [hef]; simp⟩
  have horthP : P.Orth P' :=
    ⟨hee 0 1, by show polar Q (e 0) (f 1) = 0; rw [hef]; simp,
      by show polar Q (f 0) (e 1) = 0; rw [polar_comm, hef]; simp, hff 0 1⟩
  let F : Frame Q := ⟨P, P', horthP⟩
  have hesp : ∀ i, e i ∈ F.span := fun i => by
    fin_cases i
    · exact F.e₁_mem_span
    · exact F.e₂_mem_span
  have hfsp : ∀ j, f j ∈ F.span := fun j => by
    fin_cases j
    · exact F.f₁_mem_span
    · exact F.f₂_mem_span
  have hplus : ∀ x, ι x + α x ∈ F.span := fun x => by
    obtain ⟨a, b, rfl⟩ := hw x
    have : ι (a • w 0 + b • w 1) + α (a • w 0 + b • w 1) = a • e 0 + b • e 1 := by
      simp only [he, map_add, map_smul]
      module
    rw [this]
    exact F.span.add_mem (F.span.smul_mem _ (hesp 0)) (F.span.smul_mem _ (hesp 1))
  have hg' : ∀ j, g j = (-2 : K) • f j := fun j => by
    rw [hf, smul_smul]
    have : (-2 : K) * -(2 : K)⁻¹ = 1 := by field_simp
    rw [this, one_smul]
  have hminus : ∀ x, ι x - α x ∈ F.span := fun x => by
    obtain ⟨a, b, rfl⟩ := hw' x
    have e1 : ι (a • w' 0 + b • w' 1) - α (a • w' 0 + b • w' 1) = a • g 0 + b • g 1 := by
      simp only [hg, map_add, map_smul]
      module
    have : ι (a • w' 0 + b • w' 1) - α (a • w' 0 + b • w' 1) =
        (-2 * a) • f 0 + (-2 * b) • f 1 := by
      rw [e1, hg' 0, hg' 1, smul_smul, smul_smul, mul_comm a, mul_comm b]
    rw [this]
    exact F.span.add_mem (F.span.smul_mem _ (hfsp 0)) (F.span.smul_mem _ (hfsp 1))
  refine ⟨F, fun x => ?_, fun x => ?_, ?_⟩
  · have : ι x = (2 : K)⁻¹ • ((ι x + α x) + (ι x - α x)) := by
      rw [add_add_sub_cancel, ← two_smul K (ι x), smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [this]
    exact F.span.smul_mem _ (F.span.add_mem (hplus x) (hminus x))
  · have : α x = (2 : K)⁻¹ • ((ι x + α x) - (ι x - α x)) := by
      rw [add_sub_sub_cancel, ← two_smul K (α x), smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [this]
    exact F.span.smul_mem _ (F.span.sub_mem (hplus x) (hminus x))
  · intro x hx
    obtain ⟨a, b, c, d, rfl⟩ := (Frame.mem_span_iff_comb F).mp hx
    have hS : ∀ i, e i ∈ LinearMap.range ι ⊔ LinearMap.range α := fun i => by
      rw [he]
      exact Submodule.add_mem_sup ⟨w i, rfl⟩ ⟨w i, rfl⟩
    have hT : ∀ j, f j ∈ LinearMap.range ι ⊔ LinearMap.range α := fun j => by
      rw [hf, hg]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.mem_sup_left ⟨w' j, rfl⟩)
        (Submodule.mem_sup_right ⟨w' j, rfl⟩))
    have e1 : F.e₁ = e 0 := rfl
    have e2 : F.f₁ = f 0 := rfl
    have e3 : F.e₂ = e 1 := rfl
    have e4 : F.f₂ = f 1 := rfl
    rw [e1, e2, e3, e4]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (hS 0)) (Submodule.smul_mem _ _ (hT 0)))
      (Submodule.smul_mem _ _ (hS 1))) (Submodule.smul_mem _ _ (hT 1))

end Opposite

section Commuting

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem Frame.La_neg_one_comm_of_span_invariant (h2 : (2 : K) ≠ 0) (F F' : Frame Q)
    (hinv : ∀ x ∈ F'.span, F.La (-1) x ∈ F'.span) :
    F.La (-1) * F'.La (-1) = F'.La (-1) * F.La (-1) := by
  have hiO := F.La_mem_orthogonalGroup (-1)
  have hii : ∀ v, F.La (-1) (F.La (-1) v) = v := fun v => by
    have := LinearEquiv.congr_fun F.La_neg_one_mul_self v
    simpa using this
  refine LinearEquiv.ext fun x => ?_
  have hx : x ∈ F'.span ⊔ F'.perp := by
    rw [(Frame.isCompl_span_perp F').sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨xs, hxs, xp, hxp, rfl⟩ := Submodule.mem_sup.mp hx
  have hip : F.La (-1) xp ∈ F'.perp := by
    rw [Frame.mem_perp_iff_forall_incl]
    intro Y
    have h1 := polar_map_of_mem hiO (F.La (-1) xp) (F'.incl Y)
    rw [hii] at h1
    rw [← h1, polar_comm]
    exact Frame.polar_eq_zero_of_mem_perp (hinv _ ⟨Y, rfl⟩) hxp
  have hxs' := hinv xs hxs
  simp only [LinearEquiv.mul_apply, map_add]
  rw [(Frame.mem_span_iff_inv F' h2).mp hxs, (Frame.mem_perp_iff_fix F' h2).mp hxp,
    (Frame.mem_span_iff_inv F' h2).mp hxs', (Frame.mem_perp_iff_fix F' h2).mp hip, map_neg]

end Commuting

section Opposite2

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem neg_planes_data (h2 : (2 : K) ≠ 0) (F_D F_N : Frame Q) (ι α : (Fin 2 → K) →ₗ[K] V)
    (hQ : ∀ x, Q (ι x) = -Q (α x)) (w w' : Fin 2 → Fin 2 → K)
    (hdual : ∀ i j, polar Q (α (w i)) (α (w' j)) = if i = j then 1 else 0)
    (hw : ∀ x : Fin 2 → K, ∃ a b : K, x = a • w 0 + b • w 1)
    (hι : ∀ x, ι x ∈ F_N.span) (hα : ∀ x, α x ∈ F_N.span)
    (hle : F_N.span ≤ LinearMap.range ι ⊔ LinearMap.range α)
    (hD1 : ∀ x, ι x ∈ F_D.span) (hD2 : ∀ x, α x ∈ F_D.perp) :
    F_D.La (-1) * F_N.La (-1) = F_N.La (-1) * F_D.La (-1) ∧
      F_D.span ⊓ F_N.span = LinearMap.range ι ∧ Function.Injective ι := by
  have hinvι : ∀ x, F_D.La (-1) (ι x) = -ι x := fun x =>
    (Frame.mem_span_iff_inv F_D h2).mp (hD1 x)
  have hinvα : ∀ x, F_D.La (-1) (α x) = α x := fun x =>
    (Frame.mem_perp_iff_fix F_D h2).mp (hD2 x)
  refine ⟨Frame.La_neg_one_comm_of_span_invariant h2 F_D F_N fun z hz => ?_, ?_, ?_⟩
  · obtain ⟨u, ⟨u', rfl⟩, v, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.mp (hle hz)
    rw [map_add, hinvι, hinvα]
    exact F_N.span.add_mem (F_N.span.neg_mem (hι u')) (hα v')
  · refine le_antisymm ?_ ?_
    · rintro z ⟨hzD, hzN⟩
      obtain ⟨u, ⟨u', rfl⟩, v, ⟨v', rfl⟩, rfl⟩ := Submodule.mem_sup.mp (hle hzN)
      have h1 : α v' ∈ F_D.span := by
        have := F_D.span.sub_mem hzD (hD1 u')
        rwa [add_sub_cancel_left] at this
      have h0 : α v' = 0 := by
        refine F_D.polarNondegOn_span _ h1 fun y hy => ?_
        rw [polar_comm]
        exact Frame.polar_eq_zero_of_mem_perp hy (hD2 v')
      rw [h0, add_zero]
      exact ⟨u', rfl⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨hD1 x, hι x⟩
  · have hpol : ∀ x y, polar Q (ι x) (ι y) = -polar Q (α x) (α y) := fun x y => by
      have h1 : polar Q (ι x) (ι y) = Q (ι (x + y)) - Q (ι x) - Q (ι y) := by
        rw [map_add]
        rfl
      have h2' : polar Q (α x) (α y) = Q (α (x + y)) - Q (α x) - Q (α y) := by
        rw [map_add]
        rfl
      rw [h1, h2', hQ, hQ, hQ]
      ring
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨a, b, rfl⟩ := hw x
    have key : ∀ y, polar Q (α (a • w 0 + b • w 1)) (α y) = 0 := fun y => by
      rw [← neg_eq_zero, ← hpol, hx, polar_zero_left]
    have e0 := key (w' 0)
    have e1 := key (w' 1)
    simp only [map_add, map_smul, polar_add_left, polar_smul_left, hdual] at e0 e1
    simp at e0 e1
    simp [e0, e1]

end Opposite2

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
