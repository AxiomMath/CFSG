module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix LinearFlag Module

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

omit [Finite K] in
theorem coordImage_span_single (σ : K ≃+* K) (i : Fin n) :
    coordImage σ (K ∙ (Pi.single i 1 : Fin n → K)) = K ∙ (Pi.single i 1 : Fin n → K) := by
  ext w
  rw [mem_coordImage, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨σ c, funext fun j => ?_⟩
    have h := congrFun hc j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h ⊢
      rw [h, RingEquiv.apply_symm_apply]
    · simp only [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero] at h ⊢
      rw [← map_zero σ, h, RingEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    refine ⟨σ.symm c, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]

theorem dualAut_not_mem_semilinearAutGroup (hn : 3 ≤ n) :
    dualAut n K ∉ semilinearAutGroup n K := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨-, hdisj, -, -, -⟩ := intrinsic_extremal_parabolics (K := K) p hn
  have htrans := standard_automorphism_transport (K := K) (n := n)
  intro hδ
  obtain ⟨A, σ, hA⟩ := mem_semilinearAutGroup_iff.mp hδ
  set L : Submodule K (Fin n → K) := K ∙ (Pi.single ⟨0, by omega⟩ 1 : Fin n → K) with hLdef
  have hL1 : finrank K L = 1 :=
    finrank_span_singleton (Pi.single_ne_zero_iff.2 one_ne_zero)
  have hδL := htrans.2.2.2.2.2.2.2.2.1 L
  have hEL : (projStabilizer L).map (dualAut n K : projectiveSL n K →* projectiveSL n K) =
      projStabilizer (L.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) := by
    rw [hA]
    change (projStabilizer L).map ((conjAut n K A : projectiveSL n K →* projectiveSL n K).comp
      (fieldAut n K σ : projectiveSL n K →* projectiveSL n K)) = _
    rw [← Subgroup.map_map, htrans.2.2.2.2.2.2.2.1, hLdef, coordImage_span_single,
      htrans.2.2.2.2.2.2.1]
  have hAL : finrank K (L.map (mulVecLin (A : Matrix (Fin n) (Fin n) K))) = 1 := by
    rw [hLdef, Submodule.map_span, Set.image_singleton]
    refine finrank_span_singleton fun hv => ?_
    have h := congrArg (fun w => ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) hv
    simp only [mulVecLin_apply, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      one_mulVec, mulVec_zero] at h
    exact (Pi.single_ne_zero_iff.2 one_ne_zero) h
  have hH : finrank K (dotOrth L) = n - 1 := by rw [finrank_dotOrth, hL1]
  exact Set.disjoint_left.mp hdisj ⟨_, hAL, rfl⟩ ⟨_, hH, hδL.symm.trans hEL⟩

theorem standard_form_unique (hn : 3 ≤ n) {A B : GL (Fin n) K} {σ τ : K ≃+* K} {ε η : ℕ}
    (hε : ε ≤ 1) (hη : η ≤ 1)
    (h : conjAut n K A * fieldAut n K σ * dualAut n K ^ ε =
      conjAut n K B * fieldAut n K τ * dualAut n K ^ η) : σ = τ ∧ ε = η := by
  have hcf : ∀ {A B : GL (Fin n) K} {σ τ : K ≃+* K},
      conjAut n K A * fieldAut n K σ = conjAut n K B * fieldAut n K τ → σ = τ := by
    intro A B σ τ h
    have h1 : conjAut n K (B⁻¹ * A) * fieldAut n K (σ * τ⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, ← mul_inv_eq_one]
      calc (conjAut n K B)⁻¹ * conjAut n K A * (fieldAut n K σ * (fieldAut n K τ)⁻¹) * 1⁻¹ =
          (conjAut n K B)⁻¹ * (conjAut n K A * fieldAut n K σ) * (fieldAut n K τ)⁻¹ := by group
        _ = 1 := by rw [h]; group
    obtain ⟨hστ, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1
    exact mul_inv_eq_one.1 hστ
  have hmem : ∀ {A B : GL (Fin n) K} {σ τ : K ≃+* K},
      conjAut n K A * fieldAut n K σ * dualAut n K ≠ conjAut n K B * fieldAut n K τ := by
    intro A B σ τ h
    apply dualAut_not_mem_semilinearAutGroup (K := K) hn
    have hδ : dualAut n K = (conjAut n K A * fieldAut n K σ)⁻¹ *
        (conjAut n K B * fieldAut n K τ) := by
      rw [← h]
      group
    rw [hδ]
    refine mul_mem (inv_mem ?_) ?_ <;>
      exact mul_mem (linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _))
        (fieldAut_mem_semilinearAutGroup _)
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl <;>
    rcases (by omega : η = 0 ∨ η = 1) with rfl | rfl
  · rw [pow_zero, mul_one, mul_one] at h
    exact ⟨hcf h, rfl⟩
  · rw [pow_zero, mul_one, pow_one] at h
    exact absurd h.symm hmem
  · rw [pow_zero, mul_one, pow_one] at h
    exact absurd h hmem
  · rw [pow_one] at h
    exact ⟨hcf (mul_right_cancel h), rfl⟩

omit [Finite K] in
theorem standard_form_mul (A B : GL (Fin n) K) (σ τ : K ≃+* K) {ε η : ℕ} (hε : ε ≤ 1)
    (hη : η ≤ 1) : ∃ (C : GL (Fin n) K) (θ : ℕ), θ ≤ 1 ∧
      conjAut n K A * fieldAut n K σ * dualAut n K ^ ε *
          (conjAut n K B * fieldAut n K τ * dualAut n K ^ η) =
        conjAut n K C * fieldAut n K (σ * τ) * dualAut n K ^ θ := by
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hδδ : dualAut n K * dualAut n K = 1 := htrans.2.2.2.1
  have hfc : ∀ B' : GL (Fin n) K, fieldAut n K σ * conjAut n K B' =
      conjAut n K (GeneralLinearGroup.map (σ : K →+* K) B') * fieldAut n K σ := fun B' => by
    rw [← htrans.2.2.1 σ B']
    group
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · refine ⟨A * GeneralLinearGroup.map (σ : K →+* K) B, η, hη, ?_⟩
    rw [pow_zero, mul_one, map_mul, ← htrans.2.1]
    calc conjAut n K A * fieldAut n K σ * (conjAut n K B * fieldAut n K τ * dualAut n K ^ η) =
        conjAut n K A * (fieldAut n K σ * conjAut n K B) * fieldAut n K τ * dualAut n K ^ η := by
          group
      _ = _ := by rw [hfc]; group
  ·
    have hδc : dualAut n K * conjAut n K B * fieldAut n K τ =
        conjAut n K (GeneralLinearGroup.inverseTranspose B) * fieldAut n K τ * dualAut n K := by
      rw [← htrans.2.2.2.2.1 B]
      conv_rhs => rw [← htrans.2.2.2.2.2.1 τ]
      calc dualAut n K * conjAut n K B * fieldAut n K τ =
          dualAut n K * conjAut n K B * (dualAut n K * dualAut n K) * fieldAut n K τ *
            (dualAut n K * dualAut n K) := by rw [hδδ, mul_one, mul_one]
        _ = dualAut n K * conjAut n K B * dualAut n K *
            (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by group
    have hform : conjAut n K A * fieldAut n K σ * dualAut n K ^ 1 *
        (conjAut n K B * fieldAut n K τ * dualAut n K ^ η) =
        conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K)
          (GeneralLinearGroup.inverseTranspose B)) * fieldAut n K (σ * τ) *
            (dualAut n K * dualAut n K ^ η) := by
      rw [pow_one, map_mul, ← htrans.2.1]
      calc conjAut n K A * fieldAut n K σ * dualAut n K *
            (conjAut n K B * fieldAut n K τ * dualAut n K ^ η) =
          conjAut n K A * fieldAut n K σ *
            (dualAut n K * conjAut n K B * fieldAut n K τ) * dualAut n K ^ η := by group
        _ = conjAut n K A * (fieldAut n K σ *
            conjAut n K (GeneralLinearGroup.inverseTranspose B)) * fieldAut n K τ *
              (dualAut n K * dualAut n K ^ η) := by rw [hδc]; group
        _ = _ := by rw [hfc]; group
    rcases (by omega : η = 0 ∨ η = 1) with rfl | rfl
    · exact ⟨_, 1, le_rfl, by rw [hform, pow_zero, mul_one, pow_one]⟩
    · exact ⟨_, 0, zero_le_one, by rw [hform, pow_one, hδδ, pow_zero]⟩

variable (n K) in
theorem exists_standard_form (hn : 3 ≤ n) (α : MulAut (projectiveSL n K)) :
    ∃ (σ : K ≃+* K) (A : GL (Fin n) K) (ε : ℕ), ε ≤ 1 ∧
      α = conjAut n K A * fieldAut n K σ * dualAut n K ^ ε := by
  obtain ⟨A, σ, ε, hε, h⟩ := (automorphism_generation (K := K) hn).2 α
  exact ⟨σ, A, ε, hε, h⟩

variable (K) in
@[expose] noncomputable def linearFieldPart (hn : 3 ≤ n) :
    MulAut (projectiveSL n K) →* (K ≃+* K) where
  toFun α := (exists_standard_form K n hn α).choose
  map_one' := by
    obtain ⟨A, ε, hε, h⟩ := (exists_standard_form K n hn 1).choose_spec
    have h1 : (1 : MulAut (projectiveSL n K)) =
        conjAut n K 1 * fieldAut n K 1 * dualAut n K ^ 0 := by
      rw [map_one, map_one, pow_zero, mul_one, mul_one]
    exact (standard_form_unique hn hε zero_le_one (h.symm.trans h1)).1
  map_mul' α β := by
    obtain ⟨A, ε, hε, hα⟩ := (exists_standard_form K n hn α).choose_spec
    obtain ⟨B, η, hη, hβ⟩ := (exists_standard_form K n hn β).choose_spec
    obtain ⟨A', ε', hε', hαβ⟩ := (exists_standard_form K n hn (α * β)).choose_spec
    obtain ⟨C, θ, hθ, hC⟩ := standard_form_mul A B (exists_standard_form K n hn α).choose
      (exists_standard_form K n hn β).choose hε hη
    rw [← hα, ← hβ] at hC
    exact (standard_form_unique hn hε' hθ (hαβ.symm.trans hC)).1

theorem linearFieldPart_eq (hn : 3 ≤ n) {A : GL (Fin n) K} {σ : K ≃+* K} {ε : ℕ} (hε : ε ≤ 1) :
    linearFieldPart K hn (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε) = σ := by
  obtain ⟨B, η, hη, h⟩ := (exists_standard_form K n hn
    (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε)).choose_spec
  exact (standard_form_unique hn hη hε h.symm).1

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
