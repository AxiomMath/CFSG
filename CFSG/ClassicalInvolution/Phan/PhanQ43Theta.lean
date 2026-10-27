module

public import CFSG.ClassicalInvolution.Phan.PhanQ42Solid
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianBasis

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Phan

section Theta

variable {F K : Type} [Field F] [Field K] [Algebra F K] {ε : F} (D : KData F K ε)

theorem B8_nondeg {w : V8 K} (h : ∀ v, B8 w v = 0) : w = 0 := by
  ext i
  rcases i with i | i
  · have := h (Pi.single (Sum.inr i) 1)
    rw [B8_eq_sum] at this
    simpa [Pi.single_apply, Finset.sum_add_distrib] using this
  · have := h (Pi.single (Sum.inl i) 1)
    rw [B8_eq_sum] at this
    simpa [Pi.single_apply, Finset.sum_add_distrib] using this

@[expose] noncomputable def herW (W : Submodule K (V8 K)) (σ : K ≃+* K) (hσ : ∀ x, σ x = D.τ x) :
    ↥W →ₛₗ[σ.toRingHom] ↥W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ σ.toRingHom (RingHom.id K) (fun a b => her D b.1 a.1)
    (fun a a' b => her_add_right D _ _ _)
    (fun c a b => by
      show her D b.1 (c • a.1) = σ c * her D b.1 a.1
      rw [her_smul_right, hσ])
    (fun a b b' => her_add_left D _ _ _)
    (fun c a b => by
      show her D (c • b.1) a.1 = c * her D b.1 a.1
      rw [her_smul_left])

theorem herW_apply (W : Submodule K (V8 K)) (σ : K ≃+* K) (hσ : ∀ x, σ x = D.τ x)
    (a b : ↥W) : herW D W σ hσ a b = her D b.1 a.1 := rfl

theorem herW_isSymm (W : Submodule K (V8 K)) (σ : K ≃+* K) (hσ : ∀ x, σ x = D.τ x) :
    (herW D W σ hσ).IsSymm := by
  refine ⟨fun a b => ?_⟩
  rw [herW_apply, herW_apply]
  show σ (her D b.1 a.1) = her D a.1 b.1
  rw [hσ, ← her_conj_symm]

theorem herW_nondeg {W : Submodule K (V8 K)} (hW : PhanSolid D W) (σ : K ≃+* K)
    (hσ : ∀ x, σ x = D.τ x) : (herW D W σ hσ).Nondegenerate := by
  constructor
  · intro x hx
    apply Subtype.ext
    have hcx : conj D x.1 = 0 := by
      apply B8_nondeg
      intro v
      rw [B8_comm]
      obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hW.sup v
      rw [B8_add_left]
      have h1 : B8 w₁ (conj D x.1) = 0 := by
        have := hx ⟨w₁, hw₁⟩
        rwa [herW_apply, her] at this
      have h2 : B8 (conj D w₂) (conj D x.1) = 0 := by
        rw [B8_conj, hW.ts _ hw₂ _ x.2, map_zero]
      rw [h1, h2, add_zero]
    have := congrArg (conj D) hcx
    rw [conj_conj] at this
    rw [this]
    ext i
    simp [conj]
  · intro y hy
    apply Subtype.ext
    apply B8_nondeg
    intro v
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := hW.sup v
    rw [B8_add_right, hW.ts _ y.2 _ hw₁, zero_add]
    have := hy ⟨w₂, hw₂⟩
    rwa [herW_apply, her] at this

theorem PhanSolid.exists_isometry [Finite K] {W : Submodule K (V8 K)} (hW : PhanSolid D W)
    (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x) :
    ∃ Θ : (Fin 4 → K) ≃ₗ[K] ↥W, ∀ u v, herm σ u v = her D (Θ v : V8 K) (Θ u : V8 K) := by
  have hfin := hW.finrank_eq h2
  have hsq : σ ^ 2 = 1 := by
    ext x
    simp [pow_two, hσ, D.tau_tau]
  have hne : σ ≠ 1 := by
    intro h
    have h1 : D.τ D.θ = D.θ := by rw [← hσ, h]; rfl
    rw [D.tau_theta] at h1
    have h22 : (2 : K) * D.θ = 0 := by linear_combination -h1
    exact theta_ne_zero D hε ((mul_eq_zero.1 h22).resolve_left h2)
  obtain ⟨b, hb⟩ := CFSG.ComponentClassification.CatalogueBHermitian.exists_orthonormal_basis
    (herW D W σ hσ) (herW_isSymm D W σ hσ) (herW_nondeg D hW σ hσ) hsq hne
  let b' : Module.Basis (Fin 4) K ↥W := b.reindex (finCongr hfin)
  have hb' : ∀ i j, herW D W σ hσ (b' i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    have := hb ((finCongr hfin).symm i) ((finCongr hfin).symm j)
    simpa [b'] using this
  refine ⟨b'.equivFun.symm, fun u v => ?_⟩
  rw [← herW_apply D W σ hσ]
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, hb']
  simp [herm_def, mul_comm]

@[expose] def ffLines (W : Submodule K (V8 K)) : Set (Submodule K (V8 K)) :=
  {ℓ | ℓ ≤ W ∧ ∃ v : V8 K, v ≠ 0 ∧ ffK D v ∧ ℓ = Submodule.span K {v}}

@[expose] def AdjL (ℓ ℓ' : Submodule K (V8 K)) : Prop :=
  ∃ u v : V8 K, ℓ = Submodule.span K {u} ∧ ℓ' = Submodule.span K {v} ∧ ColK D u v

theorem B8_zero_left' (v : V8 K) : B8 (0 : V8 K) v = 0 := by
  simp

theorem ColK.left_ne_zero {u v : V8 K} (h : ColK D u v) : u ≠ 0 := by
  rintro rfl
  apply h.2
  unfold gram her
  rw [B8_zero_left', B8_zero_left']
  ring

theorem adjL_span_iff {u v : V8 K} :
    AdjL D (Submodule.span K {u}) (Submodule.span K {v}) ↔ ColK D u v := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hx0 := hxy.left_ne_zero
    have hy0 := hxy.symm.left_ne_zero
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hx.symm ▸ Submodule.mem_span_singleton_self x)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (hy.symm ▸ Submodule.mem_span_singleton_self y)
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hx0 (by rw [← ha, zero_smul])
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hy0 (by rw [← hb, zero_smul])
    rw [← ha, ← hb, colK_smul D ha0 hb0] at hxy
    exact hxy
  · intro h
    exact ⟨u, v, rfl, rfl, h⟩

theorem PhanSolid.exists_pointEquiv [Finite K] {W : Submodule K (V8 K)} (hW : PhanSolid D W)
    (h2 : (2 : K) ≠ 0) (hε : ε ≠ 0) {σ : K ≃+* K} (hσ : ∀ x, σ x = D.τ x)
    (hσu : IsUnitaryInvolution σ) :
    ∃ β : ↥(nsPts σ (⊤ : Submodule K (Fin 4 → K))) ≃ ↥(ffLines D W),
      ∀ a b, IsCollinear σ a.1 b.1 ↔ AdjL D (β a).1 (β b).1 := by
  obtain ⟨Θ, hΘ⟩ := PhanSolid.exists_isometry D hW h2 hε hσ
  let Θ' : (Fin 4 → K) →ₗ[K] V8 K := W.subtype ∘ₗ Θ.toLinearMap
  have hΘ'W : ∀ u, Θ' u ∈ W := fun u => (Θ u).2
  have hΘ'inj : Function.Injective Θ' := fun u v h =>
    Θ.injective (Subtype.ext h)
  have hΘ'range : ∀ w ∈ W, ∃ u, Θ' u = w := fun w hw => by
    obtain ⟨u, hu⟩ := Θ.surjective ⟨w, hw⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  have hher : ∀ u v, her D (Θ' v) (Θ' u) = herm σ u v := fun u v => (hΘ u v).symm
  have hQ : ∀ u, Q8 (Θ' u) = 0 := fun u => by
    have h1 := hW.ts _ (hΘ'W u) _ (hΘ'W u)
    rw [B8_self] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  have hff : ∀ u, herm σ u u ≠ 0 → ffK D (Θ' u) := fun u hu =>
    ⟨hQ u, by rw [hher]; exact hu⟩
  have hmem : ∀ a : ↥(nsPts σ (⊤ : Submodule K (Fin 4 → K))),
      a.1.map Θ' ∈ ffLines D W := by
    intro a
    obtain ⟨v, hv, -, hav⟩ := mem_nsPts_iff.mp a.2
    rw [hav, Submodule.map_span, Set.image_singleton]
    refine ⟨(Submodule.span_singleton_le_iff_mem _ _).2 (hΘ'W v), Θ' v, ?_, hff v hv, rfl⟩
    intro h0
    have := hff v hv
    rw [h0] at this
    apply this.2
    unfold her
    simp
  refine ⟨Equiv.ofBijective (fun a => ⟨a.1.map Θ', hmem a⟩) ⟨?_, ?_⟩, ?_⟩
  · intro a b hab
    exact Subtype.ext (Submodule.map_injective_of_injective hΘ'inj (congrArg Subtype.val hab))
  · rintro ⟨ℓ, hℓW, v, hv0, hvff, rfl⟩
    have hvW : v ∈ W := hℓW (Submodule.mem_span_singleton_self v)
    obtain ⟨u, rfl⟩ := hΘ'range v hvW
    have hu : herm σ u u ≠ 0 := by
      have := hvff.2
      rwa [hher] at this
    refine ⟨⟨_, span_singleton_mem_nsPts hu (Submodule.mem_top)⟩, ?_⟩
    apply Subtype.ext
    show (Submodule.span K {u}).map Θ' = _
    rw [Submodule.map_span, Set.image_singleton]
  · intro a b
    obtain ⟨u, hu, -, hau⟩ := mem_nsPts_iff.mp a.2
    obtain ⟨u', hu', -, hbu⟩ := mem_nsPts_iff.mp b.2
    show IsCollinear σ a.1 b.1 ↔ AdjL D (a.1.map Θ') (b.1.map Θ')
    rw [hau, hbu, Submodule.map_span, Submodule.map_span, Set.image_singleton,
      Set.image_singleton, isCollinear_span_iff hσu hu hu', adjL_span_iff]
    unfold ColK gram
    rw [hher u u, hher u' u', hher u u', hher u' u, hW.ts _ (hΘ'W u) _ (hΘ'W u')]
    constructor
    · intro h
      exact ⟨rfl, by intro h0; apply h; linear_combination h0⟩
    · intro h h0
      apply h.2
      linear_combination h0

end Theta

end CFSG.ClassicalInvolution.PhanQ
