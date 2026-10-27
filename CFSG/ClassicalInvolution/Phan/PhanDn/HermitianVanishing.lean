module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace

public section

namespace CFSG.ClassicalInvolution.PhanDn

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.GroupTheory.WeirSylow

section Generic

variable {K : Type*} [Field K] {σ : K ≃+* K}
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {h : V →ₗ[K] V →ₛₗ[(σ : K →+* K)] K}

theorem herm_eq_zero_of_singular_orthogonal
    (hne : ∃ c : K, σ c ≠ c)
    (hHerm : ∀ u v, h v u = σ (h u v))
    {Y : Submodule K V} (hY : ∀ x ∈ Y, Q x = 0 → h x x = 0)
    {e f : V} (he : e ∈ Y) (hf : f ∈ Y)
    (heQ : Q e = 0) (hfQ : Q f = 0) (hef : polar Q e f = 0) :
    h e f = 0 := by
  have hfam : ∀ μ : K, h (e + μ • f) (e + μ • f) = 0 := by
    intro μ
    refine hY _ (Y.add_mem he (Y.smul_mem μ hf)) ?_
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
      heQ, hfQ, hef]
    simp
  have hexp : ∀ μ : K, h (e + μ • f) (e + μ • f) = σ μ * h e f + μ * σ (h e f) := by
    intro μ
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [hY e he heQ, hY f hf hfQ, hHerm e f]
    rw [show ((σ : K →+* K) μ) = σ μ from rfl]
    ring
  have h1 : h e f + σ (h e f) = 0 := by
    have h0 := hfam 1
    rw [hexp 1] at h0
    simpa using h0
  have h2 : ∀ μ : K, (σ μ - μ) * h e f = 0 := by
    intro μ
    have hsa : σ (h e f) = -h e f := by linear_combination h1
    have h0 := hfam μ
    rw [hexp μ, hsa] at h0
    linear_combination h0
  obtain ⟨c, hc⟩ := hne
  exact (mul_eq_zero.mp (h2 c)).resolve_left (sub_ne_zero.mpr hc)

theorem herm_eq_zero_of_hyperbolic_pairs
    (hne : ∃ c : K, σ c ≠ c)
    (hHerm : ∀ u v, h v u = σ (h u v))
    {Y : Submodule K V} (hY : ∀ x ∈ Y, Q x = 0 → h x x = 0)
    {e₁ f₁ e₂ f₂ : V}
    (he₁ : e₁ ∈ Y) (hf₁ : f₁ ∈ Y) (he₂ : e₂ ∈ Y) (hf₂ : f₂ ∈ Y)
    (he₁Q : Q e₁ = 0) (hf₁Q : Q f₁ = 0) (he₂Q : Q e₂ = 0) (hf₂Q : Q f₂ = 0)
    (hb : polar Q e₁ f₁ = polar Q e₂ f₂)
    (hb₁₂ : polar Q e₁ e₂ = 0) (hb₁₂' : polar Q e₁ f₂ = 0)
    (hb₂₁ : polar Q f₁ e₂ = 0) (hb₂₂ : polar Q f₁ f₂ = 0) :
    h e₁ f₁ = 0 := by
  have hb₂₁' : polar Q e₂ f₁ = 0 := by rw [polar_comm]; exact hb₂₁
  have h12 : h e₁ f₂ = 0 :=
    herm_eq_zero_of_singular_orthogonal hne hHerm hY he₁ hf₂ he₁Q hf₂Q hb₁₂'
  have h21 : h e₂ f₁ = 0 :=
    herm_eq_zero_of_singular_orthogonal hne hHerm hY he₂ hf₁ he₂Q hf₁Q hb₂₁'
  have horth : ∀ mu : K, mu ≠ 0 →
      polar Q (e₁ + mu • e₂) (f₁ - mu⁻¹ • f₂) = 0 := by
    intro mu hmu
    have key : polar Q (e₁ + mu • e₂) (f₁ - mu⁻¹ • f₂)
        = (1 - mu * mu⁻¹) * polar Q e₁ f₁ := by
      simp only [polar_add_left, polar_smul_left, polar_sub_right, polar_smul_right,
        smul_eq_mul, hb₁₂', hb₂₁', hb.symm, mul_zero, add_zero, zero_add]
      ring
    rw [key, mul_inv_cancel₀ hmu]
    ring
  have hcomb : ∀ mu : K, mu ≠ 0 → h (e₁ + mu • e₂) (f₁ - mu⁻¹ • f₂) = 0 := by
    intro mu hmu
    refine herm_eq_zero_of_singular_orthogonal hne hHerm hY
      (Y.add_mem he₁ (Y.smul_mem mu he₂)) (Y.sub_mem hf₁ (Y.smul_mem (mu⁻¹) hf₂)) ?_ ?_ ?_
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.polar_smul_right,
        he₁Q, he₂Q, hb₁₂]
      simp
    · rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul,
        QuadraticMap.polar_smul_right, hf₁Q, hf₂Q, hb₂₂]
      simp
    · exact horth mu hmu
  have hformula : ∀ mu : K, h (e₁ + mu • e₂) (f₁ - mu⁻¹ • f₂)
      = h e₁ f₁ - mu * (σ mu)⁻¹ * h e₂ f₂ := by
    intro mu
    rw [sub_eq_add_neg, ← neg_smul]
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, h12, h21, map_neg, map_inv₀, mul_zero, add_zero, zero_add]
    rw [show ((σ : K →+* K) mu)⁻¹ = (σ mu)⁻¹ from rfl]
    ring
  have hA : h e₁ f₁ = h e₂ f₂ := by
    have h0 := hcomb 1 one_ne_zero
    rw [hformula 1] at h0
    have h0' : h e₁ f₁ - h e₂ f₂ = 0 := by simpa using h0
    exact sub_eq_zero.mp h0'
  obtain ⟨c, hc⟩ := hne
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (map_zero σ)
  have hcc : c * (σ c)⁻¹ ≠ 1 := by
    intro hc1
    have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
    have hceq : c = σ c := by
      have h := congrArg (fun t => t * σ c) hc1
      rwa [mul_assoc, inv_mul_cancel₀ hσc, mul_one, one_mul] at h
    exact hc hceq.symm
  have h0 := hcomb c hc0
  rw [hformula c, ← hA] at h0
  have hcoef : 1 - c * (σ c)⁻¹ ≠ 0 := sub_ne_zero.mpr (Ne.symm hcc)
  have hfin : (1 - c * (σ c)⁻¹) * h e₁ f₁ = 0 := by linear_combination h0
  exact (mul_eq_zero.mp hfin).resolve_left hcoef

theorem herm_comp_eq_zero_of_quadPlus_isotropic
    {k : ℕ} (hk : 2 ≤ k)
    (hne : ∃ c : K, σ c ≠ c)
    (hHerm : ∀ u v, h v u = σ (h u v))
    {φ : (Fin k ⊕ Fin k → K) →ₗ[K] V}
    (hSing : ∀ x, quadPlus k K x = 0 → h (φ x) (φ x) = 0) :
    ∀ x y, h (φ x) (φ y) = 0 := by
  classical
  let M := Fin k ⊕ Fin k → K
  let Q₀ : QuadraticForm K M := quadPlus k K
  let h' : M →ₗ[K] M →ₛₗ[(σ : K →+* K)] K :=
    { toFun := fun u => (h (φ u)).comp φ
      map_add' := fun u u' => by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
      map_smul' := fun c u => by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply] }
  have h'_apply : ∀ x y, h' x y = h (φ x) (φ y) := fun _ _ => rfl
  have h'_herm : ∀ x y, h' y x = σ (h' x y) := fun x y => hHerm (φ x) (φ y)
  have h'_sing : ∀ x ∈ (⊤ : Submodule K M), Q₀ x = 0 → h' x x = 0 :=
    fun x _ hx => hSing x hx
  let E : Fin k → M := fun i => Pi.single (.inl i) 1
  let F : Fin k → M := fun i => Pi.single (.inr i) 1
  have hE_sing : ∀ a, Q₀ (E a) = 0 := by
    intro a
    rw [show Q₀ (E a) = quadPlus k K (Pi.single (.inl a) 1) by rfl, quadPlus_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp
  have hF_sing : ∀ a, Q₀ (F a) = 0 := by
    intro a
    rw [show Q₀ (F a) = quadPlus k K (Pi.single (.inr a) 1) by rfl, quadPlus_apply]
    apply Finset.sum_eq_zero
    intro i _
    simp
  have hb_ll : ∀ a b : Fin k, polar Q₀ (E a) (E b) = 0 := by
    intro a b
    change polar (quadPlus k K) (Pi.single (.inl a) 1) (Pi.single (.inl b) 1) = 0
    rw [polar_quadPlus_single_inl]
    simp
  have hb_lr : ∀ a b : Fin k, polar Q₀ (E a) (F b) = if a = b then 1 else 0 := by
    intro a b
    change polar (quadPlus k K) (Pi.single (.inl a) 1) (Pi.single (.inr b) 1) = _
    rw [polar_quadPlus_single_inr, Pi.single_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hb_rl : ∀ a b : Fin k, polar Q₀ (F a) (E b) = if a = b then 1 else 0 := by
    intro a b
    change polar (quadPlus k K) (Pi.single (.inr a) 1) (Pi.single (.inl b) 1) = _
    rw [polar_quadPlus_single_inl, Pi.single_apply]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  have hb_rr : ∀ a b : Fin k, polar Q₀ (F a) (F b) = 0 := by
    intro a b
    change polar (quadPlus k K) (Pi.single (.inr a) 1) (Pi.single (.inr b) 1) = 0
    rw [polar_quadPlus_single_inr]
    simp
  have hsecond : ∀ a : Fin k, ∃ t : Fin k, t ≠ a :=
    fun a => Fintype.exists_ne_of_one_lt_card (α := Fin k) (by simpa using (show 1 < k by omega)) a
  have h_lr : ∀ a b : Fin k, h' (E a) (F b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      obtain ⟨t, hta⟩ := hsecond a
      have hb_aa : polar Q₀ (E a) (F a) = polar Q₀ (E t) (F t) := by
        rw [hb_lr a a, hb_lr t t]
        simp
      have hb_at : polar Q₀ (E a) (F t) = 0 := by
        rw [hb_lr a t, if_neg (Ne.symm hta)]
      have hb_ta : polar Q₀ (F a) (E t) = 0 := by
        rw [hb_rl a t, if_neg (Ne.symm hta)]
      exact herm_eq_zero_of_hyperbolic_pairs (Q := Q₀) (h := h')
        hne h'_herm h'_sing (Y := ⊤) (by trivial) (by trivial) (by trivial) (by trivial)
        (hE_sing a) (hF_sing a) (hE_sing t) (hF_sing t)
        hb_aa (hb_ll a t) hb_at hb_ta (hb_rr a t)
    · exact herm_eq_zero_of_singular_orthogonal (Q := Q₀) (h := h')
        hne h'_herm h'_sing (Y := ⊤) (by trivial) (by trivial) (hE_sing a) (hF_sing b)
        (by rw [hb_lr a b, if_neg hab])
  have h_rl : ∀ a b : Fin k, h' (F a) (E b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [h'_herm (E a) (F a), h_lr a a, map_zero]
    · exact herm_eq_zero_of_singular_orthogonal (Q := Q₀) (h := h')
        hne h'_herm h'_sing (Y := ⊤) (by trivial) (by trivial) (hF_sing a) (hE_sing b)
        (by rw [hb_rl a b, if_neg hab])
  have h_ll : ∀ a b : Fin k, h' (E a) (E b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact h'_sing (E a) (by trivial) (hE_sing a)
    · exact herm_eq_zero_of_singular_orthogonal (Q := Q₀) (h := h')
        hne h'_herm h'_sing (Y := ⊤) (by trivial) (by trivial) (hE_sing a) (hE_sing b)
        (hb_ll a b)
  have h_rr : ∀ a b : Fin k, h' (F a) (F b) = 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact h'_sing (F a) (by trivial) (hF_sing a)
    · exact herm_eq_zero_of_singular_orthogonal (Q := Q₀) (h := h')
        hne h'_herm h'_sing (Y := ⊤) (by trivial) (by trivial) (hF_sing a) (hF_sing b)
        (hb_rr a b)
  have h_basis : ∀ i j : Fin k ⊕ Fin k,
      h' (Pi.single i (1 : K)) (Pi.single j (1 : K)) = 0 := by
    intro i j
    rcases i with a | a <;> rcases j with b | b
    · simpa [E] using h_ll a b
    · simpa [E, F] using h_lr a b
    · simpa [E, F] using h_rl a b
    · simpa [F] using h_rr a b
  have h'_zero : ∀ x y : M, h' x y = 0 := by
    have houter : h' = 0 := by
      refine (Pi.basisFun K (Fin k ⊕ Fin k)).ext fun i => ?_
      refine (Pi.basisFun K (Fin k ⊕ Fin k)).ext fun j => ?_
      simpa [Pi.basisFun_apply] using h_basis i j
    intro x y
    simpa using congrArg (fun f : M →ₗ[K] M →ₛₗ[(σ : K →+* K)] K => f x y) houter
  intro x y
  rw [← h'_apply x y]
  exact h'_zero x y

end Generic

section PlusType

variable {K : Type} [Field K] {σ : K ≃+* K}
variable {V : Type} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {h : V →ₗ[K] V →ₛₗ[(σ : K →+* K)] K}

theorem herm_eq_zero_on_of_isPlusType
    {Y : Submodule K V} [FiniteDimensional K Y]
    {k : ℕ} (hk : 2 ≤ k)
    (hne : ∃ c : K, σ c ≠ c)
    (hHerm : ∀ u v, h v u = σ (h u v))
    (hdim : finrank K Y = 2 * k)
    (hnd : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hplus : IsPlusType (Q.comp Y.subtype))
    (hSing : ∀ x ∈ Y, Q x = 0 → h x x = 0) :
    ∀ u ∈ Y, ∀ v ∈ Y, h u v = 0 := by
  classical
  obtain ⟨e⟩ := nonempty_isometry_quadPlus (V := Y) (Q := Q.comp Y.subtype) hnd hdim hplus
  let φ : (Fin k ⊕ Fin k → K) →ₗ[K] V :=
    Y.subtype.comp (e.symm.toLinearEquiv : (Fin k ⊕ Fin k → K) →ₗ[K] Y)
  have hφ : ∀ x, Q (φ x) = quadPlus k K x := fun x => e.symm.map_app' x
  have hzero : ∀ x y, h (φ x) (φ y) = 0 :=
    herm_comp_eq_zero_of_quadPlus_isotropic hk hne hHerm fun x hx => by
      exact hSing (φ x) (e.symm x).2 (by rw [hφ x]; exact hx)
  intro u hu v hv
  obtain ⟨x, hx⟩ := e.symm.toLinearEquiv.surjective ⟨u, hu⟩
  obtain ⟨y, hy⟩ := e.symm.toLinearEquiv.surjective ⟨v, hv⟩
  have hxu : φ x = u := by
    change (e.symm.toLinearEquiv x).val = u
    rw [hx]
  have hyv : φ y = v := by
    change (e.symm.toLinearEquiv y).val = v
    rw [hy]
  rw [← hxu, ← hyv]
  exact hzero x y

theorem exists_singular_herm_ne_zero_of_isPlusType
    {Y : Submodule K V} [FiniteDimensional K Y]
    {k : ℕ} (hk : 2 ≤ k)
    (hne : ∃ c : K, σ c ≠ c)
    (hHerm : ∀ u v, h v u = σ (h u v))
    (hdim : finrank K Y = 2 * k)
    (hnd : (polarBilin (Q.comp Y.subtype)).Nondegenerate)
    (hplus : IsPlusType (Q.comp Y.subtype))
    (hne' : ∃ u ∈ Y, ∃ v ∈ Y, h u v ≠ 0) :
    ∃ p ∈ Y, Q p = 0 ∧ h p p ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨u, hu, v, hv, huv⟩ := hne'
  exact huv (herm_eq_zero_on_of_isPlusType hk hne hHerm hdim hnd hplus h u hu v hv)

end PlusType

section Flipflop

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_isFlipflopPt_le_of_isPlusType
    {Y : Submodule K (Fin n ⊕ Fin n → K)} [FiniteDimensional K Y]
    {k : ℕ} (hk : 2 ≤ k)
    (hne : ∃ c : K, σ c ≠ c)
    (hσ : ∀ x, σ (σ x) = x)
    (hdim : finrank K Y = 2 * k)
    (hnd : (polarBilin ((quadPlus n K).comp Y.subtype)).Nondegenerate)
    (hplus : IsPlusType ((quadPlus n K).comp Y.subtype))
    (hne' : ∃ u ∈ Y, ∃ v ∈ Y, flipHerm σ u v ≠ 0) :
    ∃ p : Submodule K (Fin n ⊕ Fin n → K), p ≤ Y ∧ IsFlipflopPt σ p := by
  classical
  let h' : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) →ₛₗ[(σ : K →+* K)] K :=
    (flipHermSesq (n := n) σ).flip
  have h'_apply : ∀ u v, h' u v = flipHerm σ u v := by
    intro u v
    change flipHermSesq σ v u = flipHerm σ u v
    rfl
  have h'_herm : ∀ u v, h' v u = σ (h' u v) := by
    intro u v
    rw [h'_apply, h'_apply]
    exact ((hσ _).symm).trans (congrArg σ (flipHerm_conj hσ v u))
  have hne'' : ∃ u ∈ Y, ∃ v ∈ Y, h' u v ≠ 0 := by
    obtain ⟨u, hu, v, hv, huv⟩ := hne'
    exact ⟨u, hu, v, hv, by rwa [h'_apply]⟩
  obtain ⟨p, hpY, hpQ, hpp⟩ :=
    exists_singular_herm_ne_zero_of_isPlusType (Q := quadPlus n K) (h := h')
      hk hne h'_herm hdim hnd hplus hne''
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact hpp (by rw [h'_apply]; simp)
  have hpp' : flipHerm σ p p ≠ 0 := by
    rwa [h'_apply] at hpp
  refine ⟨Submodule.span K {p}, ?_, ?_⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hpY
  · exact (isFlipflopPt_span_singleton_iff (σ := σ) (n := n) hp0).mpr ⟨hpQ, hpp'⟩

end Flipflop

end CFSG.ClassicalInvolution.PhanDn
