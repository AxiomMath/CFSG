module

public import CFSG.ClassicalInvolution.ModelFacts.D4RigidLinear

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.LieType.Universal.Spin QuadraticMap CFSG.ClassicalInvolution.ModelFacts.D4Rigid

variable {F : Type} [Field F]

@[expose] def ve0 (F : Type) [Field F] : Idx → F := Pi.single (Sum.inl 0) 1
@[expose] def vf0 (F : Type) [Field F] : Idx → F := Pi.single (Sum.inr 0) 1
@[expose] def ve1 (F : Type) [Field F] : Idx → F := Pi.single (Sum.inl 1) 1
@[expose] def vf1 (F : Type) [Field F] : Idx → F := Pi.single (Sum.inr 1) 1

@[expose] def X1 (v : Idx → F) : Idx → F :=
  v (Sum.inl 1) • ve0 F - v (Sum.inr 0) • vf1 F

@[expose] def X2 (v : Idx → F) : Idx → F :=
  v (Sum.inr 1) • ve0 F - v (Sum.inr 0) • ve1 F

@[expose] def tauM (v : Idx → F) : Idx → F :=
  fun μ => if (Sum.elim id id μ).val < 2 then -v μ else v μ

@[expose] def VpC (c : Idx → F) : Prop := ∀ μ : Idx, (Sum.elim id id μ).val < 2 → c μ = 0

@[expose] noncomputable def eich (c v : Idx → F) : Idx → F :=
  v + v (Sum.inr 0) • c - polar (quadPlus 4 F) v c • ve0 F -
    (quadPlus 4 F c * v (Sum.inr 0)) • ve0 F

@[expose] def Pp (u : Idx → F) : Idx → F :=
  fun μ => if (Sum.elim id id μ).val < 2 then 0 else u μ

section Coord

theorem ve0_apply (μ : Idx) : ve0 F μ = if μ = Sum.inl 0 then 1 else 0 := by
  simp [ve0, Pi.single_apply]

theorem vf0_apply (μ : Idx) : vf0 F μ = if μ = Sum.inr 0 then 1 else 0 := by
  simp [vf0, Pi.single_apply]

theorem ve1_apply (μ : Idx) : ve1 F μ = if μ = Sum.inl 1 then 1 else 0 := by
  simp [ve1, Pi.single_apply]

theorem vf1_apply (μ : Idx) : vf1 F μ = if μ = Sum.inr 1 then 1 else 0 := by
  simp [vf1, Pi.single_apply]

theorem X1_apply (v : Idx → F) (μ : Idx) :
    X1 v μ = v (Sum.inl 1) * (if μ = Sum.inl 0 then 1 else 0) -
      v (Sum.inr 0) * (if μ = Sum.inr 1 then 1 else 0) := by
  simp [X1, ve0_apply, vf1_apply]

theorem X2_apply (v : Idx → F) (μ : Idx) :
    X2 v μ = v (Sum.inr 1) * (if μ = Sum.inl 0 then 1 else 0) -
      v (Sum.inr 0) * (if μ = Sum.inl 1 then 1 else 0) := by
  simp [X2, ve0_apply, ve1_apply]

theorem tauM_apply (v : Idx → F) (μ : Idx) :
    tauM v μ = if (Sum.elim id id μ).val < 2 then -v μ else v μ := rfl

theorem eich_apply (c v : Idx → F) (μ : Idx) :
    eich c v μ = v μ + v (Sum.inr 0) * c μ - polar (quadPlus 4 F) v c *
      (if μ = Sum.inl 0 then 1 else 0) - quadPlus 4 F c * v (Sum.inr 0) *
        (if μ = Sum.inl 0 then 1 else 0) := by
  simp [eich, ve0_apply]

theorem quadPlus_of_VpC {c : Idx → F} (hc : VpC c) :
    quadPlus 4 F c = c (Sum.inl 2) * c (Sum.inr 2) + c (Sum.inl 3) * c (Sum.inr 3) := by
  have h0 := hc (Sum.inl 0) (by decide)
  have h1 := hc (Sum.inl 1) (by decide)
  rw [quadPlus_apply, Fin.sum_univ_four, h0, h1]
  simp

theorem polar_of_VpC {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    polar (quadPlus 4 F) v c = v (Sum.inl 2) * c (Sum.inr 2) + c (Sum.inl 2) * v (Sum.inr 2) +
      (v (Sum.inl 3) * c (Sum.inr 3) + c (Sum.inl 3) * v (Sum.inr 3)) := by
  have h0 := hc (Sum.inl 0) (by decide)
  have h1 := hc (Sum.inl 1) (by decide)
  have h2 := hc (Sum.inr 0) (by decide)
  have h3 := hc (Sum.inr 1) (by decide)
  rw [polar_quadPlus, Fin.sum_univ_four]
  simp [h0, h1, h2, h3]

theorem VpC_Pp (u : Idx → F) : VpC (Pp u) := fun μ hμ => by
  rw [Pp]
  simp only [hμ, ↓reduceIte]

theorem Pp_apply_of_lt (u : Idx → F) {μ : Idx} (hμ : (Sum.elim id id μ).val < 2) : Pp u μ = 0 := by
  rw [Pp]
  simp only [hμ, ↓reduceIte]

theorem Pp_apply_of_not_lt (u : Idx → F) {μ : Idx} (hμ : ¬ (Sum.elim id id μ).val < 2) :
    Pp u μ = u μ := by
  rw [Pp]
  simp only [hμ, ↓reduceIte]

theorem Pp_of_VpC {v : Idx → F} (hv : VpC v) : Pp v = v := by
  ext μ
  by_cases hμ : (Sum.elim id id μ).val < 2
  · rw [Pp_apply_of_lt v hμ, hv μ hμ]
  · exact Pp_apply_of_not_lt v hμ

end Coord

section Main

theorem polar_ve0 (v : Idx → F) : polar (quadPlus 4 F) v (ve0 F) = v (Sum.inr 0) :=
  polar_quadPlus_single_inl 4 F v 0

theorem polar_vf0 (v : Idx → F) : polar (quadPlus 4 F) v (vf0 F) = v (Sum.inl 0) :=
  polar_quadPlus_single_inr 4 F v 0

theorem polar_map_of_Q (h : (Idx → F) ≃ₗ[F] (Idx → F))
    (hQ : ∀ v, quadPlus 4 F (h v) = quadPlus 4 F v) (u v : Idx → F) :
    polar (quadPlus 4 F) (h u) (h v) = polar (quadPlus 4 F) u v := by
  simp only [QuadraticMap.polar, ← map_add, hQ]

theorem X1_X2 (v : Idx → F) : X1 (X2 v) = -(v (Sum.inr 0)) • ve0 F := by
  ext μ
  simp [X1_apply, X2_apply, ve0_apply]

variable {p : ℕ}

theorem eich_of_commute (hp2 : (2 : F) ≠ 0) [CharP F p] (hpodd : Odd p)
    (h : (Idx → F) ≃ₗ[F] (Idx → F))
    (hX₁ : ∀ v, h (X1 v) = X1 (h v)) (hX₂ : ∀ v, h (X2 v) = X2 (h v))
    (hτ : ∀ v, h (tauM (h (tauM v))) = v) (hQ : ∀ v, quadPlus 4 F (h v) = quadPlus 4 F v)
    (hpow : h ^ p = 1) :
    ∃ c : Idx → F, VpC c ∧ ∀ v, h v = eich c v := by
  have hS1 : ∀ v, v (Sum.inr 0) • h (ve0 F) = (h v) (Sum.inr 0) • ve0 F := by
    intro v
    have h1 : h (X1 (X2 v)) = X1 (X2 (h v)) := by rw [hX₁, hX₂]
    rw [X1_X2, X1_X2, map_smul] at h1
    simpa using h1
  set κ : F := (h (vf0 F)) (Sum.inr 0) with hκdef
  have hf0j0 : vf0 F (Sum.inr 0) = 1 := by simp [vf0_apply]
  have hκ : h (ve0 F) = κ • ve0 F := by
    have := hS1 (vf0 F)
    rwa [hf0j0, one_smul] at this
  have hrow0 : ∀ v, (h v) (Sum.inr 0) = κ * v (Sum.inr 0) := by
    intro v
    have h1 := congrFun (hS1 v) (Sum.inl 0)
    rw [hκ] at h1
    simp [ve0_apply] at h1
    rw [← h1]
    ring
  have hκ2 : κ * κ = 1 := by
    have h1 := polar_map_of_Q h hQ (vf0 F) (ve0 F)
    rw [hκ, QuadraticMap.polar_smul_right, polar_ve0, polar_ve0, hrow0] at h1
    simpa [hf0j0, hκdef] using h1
  have hpowe0 : ∀ n : ℕ, (h ^ n) (ve0 F) = κ ^ n • ve0 F := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, hκ, smul_smul, pow_succ]
  have hκp : κ ^ p = 1 := by
    have h1 := congrFun (hpowe0 p) (Sum.inl 0)
    rw [hpow] at h1
    simpa [ve0_apply] using h1.symm
  have hκ1 : κ = 1 := by
    obtain ⟨m, hm⟩ := hpodd
    rw [hm, pow_succ, pow_mul, _root_.sq, hκ2, one_pow, one_mul] at hκp
    exact hκp
  have he0 : h (ve0 F) = ve0 F := by rw [hκ, hκ1, one_smul]
  have hrowj0 : ∀ v, (h v) (Sum.inr 0) = v (Sum.inr 0) := fun v => by rw [hrow0, hκ1, one_mul]
  have hA1 : ∀ v, v (Sum.inl 1) • ve0 F - v (Sum.inr 0) • h (vf1 F) =
      (h v) (Sum.inl 1) • ve0 F - v (Sum.inr 0) • vf1 F := by
    intro v
    have h1 := hX₁ v
    simp only [X1, map_sub, map_smul, he0, hrowj0] at h1
    exact h1
  have hA2 : ∀ v, v (Sum.inr 1) • ve0 F - v (Sum.inr 0) • h (ve1 F) =
      (h v) (Sum.inr 1) • ve0 F - v (Sum.inr 0) • ve1 F := by
    intro v
    have h1 := hX₂ v
    simp only [X2, map_sub, map_smul, he0, hrowj0] at h1
    exact h1
  obtain ⟨b₁, hb₁⟩ : ∃ b : F, b = (h (vf0 F)) (Sum.inl 1) := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ b : F, b = (h (vf0 F)) (Sum.inr 1) := ⟨_, rfl⟩
  have hf1 : h (vf1 F) = vf1 F - b₁ • ve0 F := by
    have h1 := hA1 (vf0 F)
    simp [vf0_apply] at h1
    have h2 : h (vf1 F) = -((h (vf0 F)) (Sum.inl 1) • ve0 F - vf1 F) := by rw [← h1, neg_neg]
    rw [h2, ← hb₁]
    abel
  have he1 : h (ve1 F) = ve1 F - b₂ • ve0 F := by
    have h1 := hA2 (vf0 F)
    simp [vf0_apply] at h1
    have h2 : h (ve1 F) = -((h (vf0 F)) (Sum.inr 1) • ve0 F - ve1 F) := by rw [← h1, neg_neg]
    rw [h2, ← hb₂]
    abel
  have hrowi1 : ∀ v, (h v) (Sum.inl 1) = v (Sum.inl 1) + b₁ * v (Sum.inr 0) := by
    intro v
    have h1 := congrFun (hA1 v) (Sum.inl 0)
    rw [hf1] at h1
    simp [ve0_apply, vf1_apply] at h1
    rw [← h1]
    ring
  have hrowj1 : ∀ v, (h v) (Sum.inr 1) = v (Sum.inr 1) + b₂ * v (Sum.inr 0) := by
    intro v
    have h1 := congrFun (hA2 v) (Sum.inl 0)
    rw [he1] at h1
    simp [ve0_apply, ve1_apply] at h1
    rw [← h1]
    ring
  have hw1 : tauM (h (tauM (vf0 F))) (Sum.inl 1) = b₁ := by
    simp [tauM_apply, hrowi1, vf0_apply]
  have hw0 : tauM (h (tauM (vf0 F))) (Sum.inr 0) = 1 := by
    simp [tauM_apply, hrowj0, vf0_apply]
  have hw2 : tauM (h (tauM (vf0 F))) (Sum.inr 1) = b₂ := by
    simp [tauM_apply, hrowj1, vf0_apply]
  have hb1 : b₁ = 0 := by
    have h1 := congrFun (hτ (vf0 F)) (Sum.inl 1)
    rw [hrowi1, hw1, hw0] at h1
    simp [vf0_apply] at h1
    have h2 : (2 : F) * b₁ = 0 := by rw [two_mul]; exact h1
    exact (mul_eq_zero.mp h2).resolve_left hp2
  have hb2 : b₂ = 0 := by
    have h1 := congrFun (hτ (vf0 F)) (Sum.inr 1)
    rw [hrowj1, hw2, hw0] at h1
    simp [vf0_apply] at h1
    have h2 : (2 : F) * b₂ = 0 := by rw [two_mul]; exact h1
    exact (mul_eq_zero.mp h2).resolve_left hp2
  subst hb1 hb2
  have hri1 : ∀ v, (h v) (Sum.inl 1) = v (Sum.inl 1) := fun v => by rw [hrowi1]; ring
  have hrj1 : ∀ v, (h v) (Sum.inr 1) = v (Sum.inr 1) := fun v => by rw [hrowj1]; ring
  have hf1' : h (vf1 F) = vf1 F := by rw [hf1]; simp
  have he1' : h (ve1 F) = ve1 F := by rw [he1]; simp
  obtain ⟨c, hcdef⟩ : ∃ c : Idx → F,
      c = fun μ => if (Sum.elim id id μ).val < 2 then 0 else (h (vf0 F)) μ := ⟨_, rfl⟩
  have hcV : VpC c := fun μ hμ => by rw [hcdef]; simp only [hμ, ↓reduceIte]
  obtain ⟨a, hadef⟩ : ∃ a : F, a = (h (vf0 F)) (Sum.inl 0) := ⟨_, rfl⟩
  have hf0 : h (vf0 F) = a • ve0 F + vf0 F + c := by
    ext μ
    rcases μ with i | i <;> fin_cases i <;>
      simp [hcdef, hadef, ve0_apply, vf0_apply, hrowj0 (vf0 F), hri1 (vf0 F), hrj1 (vf0 F)]
  have hca : a = - quadPlus 4 F c := by
    have h1 := hQ (vf0 F)
    rw [hf0, quadPlus_apply, quadPlus_apply, Fin.sum_univ_four, Fin.sum_univ_four] at h1
    have c0 := hcV (Sum.inl 0) (by decide)
    have c1 := hcV (Sum.inl 1) (by decide)
    have c2 := hcV (Sum.inr 0) (by decide)
    have c3 := hcV (Sum.inr 1) (by decide)
    simp [ve0_apply, vf0_apply, c0, c1, c2, c3] at h1
    rw [quadPlus_of_VpC hcV]
    linear_combination h1
  have hVrows : ∀ v, VpC v →
      (h v) (Sum.inr 0) = 0 ∧ (h v) (Sum.inl 1) = 0 ∧ (h v) (Sum.inr 1) = 0 := by
    intro v hv
    exact ⟨by rw [hrowj0]; exact hv _ (by decide), by rw [hri1]; exact hv _ (by decide),
      by rw [hrj1]; exact hv _ (by decide)⟩
  have hdecV : ∀ v, VpC v → h v = (h v) (Sum.inl 0) • ve0 F + Pp (h v) := by
    intro v hv
    obtain ⟨r0, r1, r2⟩ := hVrows v hv
    ext μ
    rcases μ with i | i <;> fin_cases i <;> simp [Pp, ve0_apply, r0, r1, r2]
  have hβ : ∀ v, VpC v → (h v) (Sum.inl 0) = - polar (quadPlus 4 F) (h v) c := by
    intro v hv
    have h1 := polar_map_of_Q h hQ v (vf0 F)
    have hv0 : polar (quadPlus 4 F) v (vf0 F) = 0 := by
      rw [polar_vf0]
      exact hv _ (by decide)
    rw [hv0, hf0] at h1
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right,
      polar_ve0, polar_vf0] at h1
    obtain ⟨r0, -, -⟩ := hVrows v hv
    rw [r0] at h1
    linear_combination h1
  have htauV : ∀ v : Idx → F, VpC v → tauM v = v := by
    intro v hv
    ext μ
    by_cases hμ : (Sum.elim id id μ).val < 2
    · simp [tauM_apply, hμ, hv μ hμ]
    · simp [tauM_apply, hμ]
  have htauU : ∀ v, VpC v → tauM (h v) = (-(h v) (Sum.inl 0)) • ve0 F + Pp (h v) := by
    intro v hv
    obtain ⟨r0, r1, r2⟩ := hVrows v hv
    ext μ
    rcases μ with i | i <;> fin_cases i <;> simp [tauM_apply, Pp, ve0_apply, r0, r1, r2]
  have hDD : ∀ v, VpC v →
      Pp (h (Pp (h v))) = v ∧ (h (Pp (h v))) (Sum.inl 0) = (h v) (Sum.inl 0) := by
    intro v hv
    have h1 := hτ v
    rw [htauV v hv, htauU v hv, map_add, map_smul, he0,
      hdecV (Pp (h v)) (VpC_Pp _)] at h1
    constructor
    · ext μ
      by_cases hμ : (Sum.elim id id μ).val < 2
      · rw [Pp_apply_of_lt _ hμ, hv μ hμ]
      · have hμ0 : μ ≠ Sum.inl 0 := by
          rintro rfl
          exact hμ (by decide)
        have := congrFun h1 μ
        simp [ve0_apply, hμ0] at this
        exact this
    · have := congrFun h1 (Sum.inl 0)
      simp [ve0_apply, Pp_apply_of_lt _ (show (Sum.elim id id (Sum.inl (0 : Fin 4))).val < 2 by
        decide), hv _ (show (Sum.elim id id (Sum.inl (0 : Fin 4))).val < 2 by decide)] at this
      linear_combination this
  have hh : ∀ v, VpC v → h (h v) = v + (2 * (h v) (Sum.inl 0)) • ve0 F := by
    intro v hv
    obtain ⟨hD, hβ'⟩ := hDD v hv
    conv_lhs => rw [hdecV v hv]
    rw [map_add, map_smul, he0, hdecV (Pp (h v)) (VpC_Pp _), hβ', hD]
    module
  have hpow2 : ∀ m : ℕ, ∀ v, VpC v →
      ((h * h) ^ m) v = v + (((2 * m : ℕ) : F) * (h v) (Sum.inl 0)) • ve0 F := by
    intro m
    induction m with
    | zero => intro v hv; simp
    | succ m ih =>
      intro v hv
      have e1 : (h * h) (ve0 F) = ve0 F := by rw [LinearEquiv.mul_apply, he0, he0]
      have e2 : (h * h) v = v + (2 * (h v) (Sum.inl 0)) • ve0 F := hh v hv
      rw [pow_succ', LinearEquiv.mul_apply, ih v hv, map_add, map_smul, e1, e2]
      push_cast
      module
  obtain ⟨m, hm⟩ := hpodd
  have hhm : h = (h * h) ^ (m + 1) := by
    rw [← _root_.sq, ← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hpow, one_mul]
  have hVfinal : ∀ v, VpC v → h v = v + (h v) (Sum.inl 0) • ve0 F := by
    intro v hv
    have h1 := hpow2 (m + 1) v hv
    rw [← hhm] at h1
    have hcast : (((2 * (m + 1) : ℕ) : F)) = 1 := by
      have : ((p : ℕ) : F) = 0 := CharP.cast_eq_zero F p
      have e : 2 * (m + 1) = p + 1 := by omega
      rw [e]
      push_cast
      rw [this, zero_add]
    rw [hcast, one_mul] at h1
    exact h1
  refine ⟨c, hcV, fun v => ?_⟩
  have hdec : v = v (Sum.inl 0) • ve0 F + v (Sum.inr 0) • vf0 F + v (Sum.inl 1) • ve1 F +
      v (Sum.inr 1) • vf1 F + Pp v := by
    ext μ
    rcases μ with i | i <;> fin_cases i <;> simp [Pp, ve0_apply, vf0_apply, ve1_apply, vf1_apply]
  have hPpV : VpC (Pp v) := VpC_Pp v
  have hpolar0 : polar (quadPlus 4 F) (ve0 F) c = 0 := by
    rw [QuadraticMap.polar_comm, polar_ve0]
    exact hcV _ (by decide)
  have hhPv : h (Pp v) = Pp v - polar (quadPlus 4 F) (Pp v) c • ve0 F := by
    obtain ⟨β, hβdef⟩ : ∃ β : F, β = (h (Pp v)) (Sum.inl 0) := ⟨_, rfl⟩
    have h1 := hβ (Pp v) hPpV
    have h2 := hVfinal (Pp v) hPpV
    rw [← hβdef] at h1 h2
    rw [h2, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hpolar0, smul_zero,
      add_zero] at h1
    rw [h2, h1]
    module
  have hpolar : polar (quadPlus 4 F) v c = polar (quadPlus 4 F) (Pp v) c := by
    rw [polar_of_VpC hcV, polar_of_VpC hcV]
    simp [Pp]
  have hL : h v = (v (Sum.inl 0) • ve0 F + v (Sum.inr 0) • (a • ve0 F + vf0 F + c) +
      v (Sum.inl 1) • ve1 F + v (Sum.inr 1) • vf1 F) +
        (Pp v - polar (quadPlus 4 F) (Pp v) c • ve0 F) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, he0, hf0,
      he1', hf1', hhPv]
  rw [hL]
  ext μ
  have hc0 := hcV (Sum.inl 0) (by decide)
  rcases μ with i | i <;> fin_cases i <;>
    simp [eich_apply, ve0_apply, vf0_apply, ve1_apply, vf1_apply, Pp, hc0, hpolar, hca] <;> ring

end Main

section Eich

@[expose] noncomputable def eich1 (c v : Idx → F) : Idx → F :=
  v - v (Sum.inr 1) • c + polar (quadPlus 4 F) v c • ve1 F -
    (quadPlus 4 F c * v (Sum.inr 1)) • ve1 F

theorem eich1_apply (c v : Idx → F) (μ : Idx) :
    eich1 c v μ = v μ - v (Sum.inr 1) * c μ + polar (quadPlus 4 F) v c *
      (if μ = Sum.inl 1 then 1 else 0) - quadPlus 4 F c * v (Sum.inr 1) *
        (if μ = Sum.inl 1 then 1 else 0) := by
  simp [eich1, ve1_apply]

theorem eich_injective {c c' : Idx → F} (hc : VpC c) (hc' : VpC c')
    (h : ∀ v, eich c v = eich c' v) : c = c' := by
  have h1 := h (vf0 F)
  ext μ
  by_cases hμ : (Sum.elim id id μ).val < 2
  · rw [hc μ hμ, hc' μ hμ]
  · have h2 := congrFun h1 μ
    have hμ0 : μ ≠ Sum.inl 0 := by
      rintro rfl
      exact hμ (by decide)
    have hμ1 : μ ≠ Sum.inr 0 := by
      rintro rfl
      exact hμ (by decide)
    simp [eich_apply, vf0_apply, hμ0, hμ1] at h2
    exact h2

theorem polar_ve0_VpC {c : Idx → F} (hc : VpC c) : polar (quadPlus 4 F) (ve0 F) c = 0 := by
  rw [QuadraticMap.polar_comm, polar_ve0]
  exact hc _ (by decide)

theorem polar_ve1_VpC {c : Idx → F} (hc : VpC c) : polar (quadPlus 4 F) (ve1 F) c = 0 := by
  rw [QuadraticMap.polar_comm]
  have := polar_quadPlus_single_inl (n := 4) (K := F) c 1
  rw [show ve1 F = Pi.single (Sum.inl 1) 1 from rfl, this]
  exact hc _ (by decide)

theorem eich_apply_inr0 {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    eich c v (Sum.inr 0) = v (Sum.inr 0) := by
  have := hc (Sum.inr 0) (by decide)
  simp [eich_apply, this]

theorem eich_eich {c c' : Idx → F} (hc : VpC c) (hc' : VpC c') (v : Idx → F) :
    eich c (eich c' v) = eich (c + c') v := by
  have hp : polar (quadPlus 4 F) (eich c' v) c =
      polar (quadPlus 4 F) v c + v (Sum.inr 0) * polar (quadPlus 4 F) c' c := by
    simp only [eich, QuadraticMap.polar_add_left, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_smul_left, polar_ve0_VpC hc, smul_eq_mul]
    ring
  have hpc : polar (quadPlus 4 F) c' c = polar (quadPlus 4 F) c c' := QuadraticMap.polar_comm _ _ _
  have hq : quadPlus 4 F (c + c') = quadPlus 4 F c + quadPlus 4 F c' + polar (quadPlus 4 F) c c' :=
    QuadraticMap.map_add _ _ _
  have hpadd : polar (quadPlus 4 F) v (c + c') = polar (quadPlus 4 F) v c +
      polar (quadPlus 4 F) v c' := QuadraticMap.polar_add_right _ _ _ _
  conv_lhs => rw [eich, eich_apply_inr0 hc', hp, hpc]
  conv_rhs => rw [eich, hq, hpadd]
  simp only [eich]
  module

theorem eich1_apply_inr0 {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    eich1 c v (Sum.inr 0) = v (Sum.inr 0) := by
  have := hc (Sum.inr 0) (by decide)
  simp [eich1_apply, this]

theorem eich_apply_inr1 {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    eich c v (Sum.inr 1) = v (Sum.inr 1) := by
  have := hc (Sum.inr 1) (by decide)
  simp [eich_apply, this]

theorem eich1_apply_inr1 {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    eich1 c v (Sum.inr 1) = v (Sum.inr 1) := by
  have := hc (Sum.inr 1) (by decide)
  simp [eich1_apply, this]

theorem X2_eich {c : Idx → F} (hc : VpC c) (v : Idx → F) : X2 (eich c v) = X2 v := by
  simp only [X2, eich_apply_inr1 hc, eich_apply_inr0 hc]

theorem X2_eich1 {c : Idx → F} (hc : VpC c) (v : Idx → F) : X2 (eich1 c v) = X2 v := by
  simp only [X2, eich1_apply_inr1 hc, eich1_apply_inr0 hc]

theorem eich_eich1_sub {c c' : Idx → F} (hc : VpC c) (hc' : VpC c') (v : Idx → F) :
    eich c (eich1 c' v) - eich1 c' (eich c v) = polar (quadPlus 4 F) c c' • X2 v := by
  have hp : polar (quadPlus 4 F) (eich1 c' v) c =
      polar (quadPlus 4 F) v c - v (Sum.inr 1) * polar (quadPlus 4 F) c' c := by
    simp only [eich1, QuadraticMap.polar_add_left, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_smul_left, polar_ve1_VpC hc, smul_eq_mul]
    ring
  have hp' : polar (quadPlus 4 F) (eich c v) c' =
      polar (quadPlus 4 F) v c' + v (Sum.inr 0) * polar (quadPlus 4 F) c c' := by
    simp only [eich, QuadraticMap.polar_add_left, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_smul_left, polar_ve0_VpC hc', smul_eq_mul]
    ring
  have hpc : polar (quadPlus 4 F) c' c = polar (quadPlus 4 F) c c' := QuadraticMap.polar_comm _ _ _
  have hj : (eich c v) (Sum.inr 1) = v (Sum.inr 1) := eich_apply_inr1 hc v
  have hj0 : (eich1 c' v) (Sum.inr 0) = v (Sum.inr 0) := eich1_apply_inr0 hc' v
  have h1 : eich c (eich1 c' v) = eich1 c' v + v (Sum.inr 0) • c -
      (polar (quadPlus 4 F) v c - v (Sum.inr 1) * polar (quadPlus 4 F) c c') • ve0 F -
        (quadPlus 4 F c * v (Sum.inr 0)) • ve0 F := by
    rw [eich, hj0, hp, hpc]
  have h2 : eich1 c' (eich c v) = eich c v - v (Sum.inr 1) • c' +
      (polar (quadPlus 4 F) v c' + v (Sum.inr 0) * polar (quadPlus 4 F) c c') • ve1 F -
        (quadPlus 4 F c' * v (Sum.inr 1)) • ve1 F := by
    rw [eich1, hj, hp']
  rw [h1, h2]
  simp only [eich, eich1, X2]
  module

theorem polar_eq_of_comm {c c' : Idx → F} (hc : VpC c) (hc' : VpC c') (κ : F)
    (h : ∀ v, eich c (eich1 c' v) = eich1 c' (eich c v) + κ • X2 v) :
    polar (quadPlus 4 F) c c' = κ := by
  have h1 := eich_eich1_sub hc hc' (vf0 F)
  have h2 : eich c (eich1 c' (vf0 F)) - eich1 c' (eich c (vf0 F)) = κ • X2 (vf0 F) := by
    rw [h (vf0 F)]
    abel
  rw [h2] at h1
  have h3 : X2 (vf0 F) = -ve1 F := by
    ext μ
    simp [X2_apply, vf0_apply, ve1_apply]
  rw [h3] at h1
  have h4 := congrFun h1 (Sum.inl 1)
  simp [ve1_apply] at h4
  exact h4.symm

@[expose] def lamS (s : F) (μ : Idx) : F :=
  if μ = Sum.inl 0 ∨ μ = Sum.inr 1 then s else
    if μ = Sum.inr 0 ∨ μ = Sum.inl 1 then s⁻¹ else 1

@[expose] def Dt (s : F) (v : Idx → F) : Idx → F := fun μ => lamS s μ * v μ

theorem Dt_eich {s : F} (hs : s ≠ 0) {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    Dt s (eich c v) = eich (s • c) (Dt s v) := by
  have hcs : VpC (s • c) := fun μ hμ => by simp [hc μ hμ]
  have hpol : polar (quadPlus 4 F) (Dt s v) c = polar (quadPlus 4 F) v c := by
    rw [polar_of_VpC hc, polar_of_VpC hc]
    simp [Dt, lamS]
  have hQ : quadPlus 4 F (s • c) = s ^ 2 * quadPlus 4 F c := by
    rw [QuadraticMap.map_smul, smul_eq_mul, _root_.sq]
  have c0 := hc (Sum.inl 0) (by decide)
  have c1 := hc (Sum.inr 1) (by decide)
  have c2 := hc (Sum.inr 0) (by decide)
  have c3 := hc (Sum.inl 1) (by decide)
  ext μ
  rw [eich_apply, Dt, eich_apply, QuadraticMap.polar_smul_right, hpol, hQ]
  rcases μ with i | i <;> fin_cases i <;>
    simp [Dt, lamS, c0, c1, c2, c3] <;> field_simp

@[expose] def Nw (v : Idx → F) : Idx → F := fun μ =>
  if μ = Sum.inl 0 then v (Sum.inl 1) else if μ = Sum.inl 1 then -v (Sum.inl 0) else
    if μ = Sum.inr 0 then v (Sum.inr 1) else if μ = Sum.inr 1 then -v (Sum.inr 0) else v μ

theorem Nw_eich {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    Nw (eich c v) = eich1 c (Nw v) := by
  have hpol : polar (quadPlus 4 F) (Nw v) c = polar (quadPlus 4 F) v c := by
    rw [polar_of_VpC hc, polar_of_VpC hc]
    simp [Nw]
  have c0 := hc (Sum.inl 0) (by decide)
  have c1 := hc (Sum.inr 1) (by decide)
  have c2 := hc (Sum.inr 0) (by decide)
  have c3 := hc (Sum.inl 1) (by decide)
  ext μ
  rw [eich1_apply, hpol]
  rcases μ with i | i <;> fin_cases i <;>
    simp [Nw, eich_apply, c0, c1, c2, c3]
  ring

end Eich

section IsoExt

@[expose] def kap : Fin 4 → Idx := ![Sum.inl 2, Sum.inr 2, Sum.inl 3, Sum.inr 3]

@[expose] def ek (F : Type) [Field F] (k : Fin 4) : Idx → F := Pi.single (kap k) 1

@[expose] noncomputable def U0 (w : Fin 4 → Idx → F) : (Idx → F) →ₗ[F] (Idx → F) :=
  ∑ k : Fin 4, (LinearMap.proj (kap k)).smulRight (w k)

theorem U0_apply (w : Fin 4 → Idx → F) (v : Idx → F) :
    U0 w v = ∑ k : Fin 4, v (kap k) • w k := by
  simp [U0]

theorem ek_apply (k : Fin 4) (μ : Idx) : ek F k μ = if μ = kap k then 1 else 0 := by
  simp [ek, Pi.single_apply]

theorem Pp_eq_sum (v : Idx → F) : Pp v = ∑ k : Fin 4, v (kap k) • ek F k := by
  ext μ
  rcases μ with i | i <;> fin_cases i <;>
    simp [Pp, kap, Fin.sum_univ_four, ek_apply]

theorem U0_ek (w : Fin 4 → Idx → F) (k : Fin 4) : U0 w (ek F k) = w k := by
  rw [U0_apply]
  simp [ek_apply, Fin.sum_univ_four]
  fin_cases k <;> simp [kap]

theorem VpC_U0 {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k)) (v : Idx → F) : VpC (U0 w v) := by
  intro μ hμ
  rw [U0_apply]
  simp [Finset.sum_apply, hw _ μ hμ]

theorem U0_Pp (w : Fin 4 → Idx → F) (v : Idx → F) : U0 w (Pp v) = U0 w v := by
  rw [U0_apply, U0_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : Pp v (kap k) = v (kap k) := by
    fin_cases k <;> simp [kap, Pp]
  rw [this]

theorem U0_of_vanish (w : Fin 4 → Idx → F) {u : Idx → F} (hu : ∀ k, u (kap k) = 0) :
    U0 w u = 0 := by
  rw [U0_apply]
  simp [hu]

theorem polar_U0 {w : Fin 4 → Idx → F}
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l))
    (v x : Idx → F) : polar (quadPlus 4 F) (U0 w v) (U0 w x) = polar (quadPlus 4 F) (Pp v) (Pp x) := by
  rw [Pp_eq_sum v, Pp_eq_sum x, U0_apply, U0_apply]
  simp only [Fin.sum_univ_four, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hG]

@[expose] noncomputable def Ppl : (Idx → F) →ₗ[F] (Idx → F) :=
  ∑ k : Fin 4, (LinearMap.proj (kap k)).smulRight (ek F k)

theorem Ppl_apply (v : Idx → F) : Ppl v = Pp v := by
  rw [Pp_eq_sum]
  simp [Ppl]

@[expose] noncomputable def AL (w : Fin 4 → Idx → F) : (Idx → F) →ₗ[F] (Idx → F) :=
  LinearMap.id - Ppl + U0 w

theorem AL_apply (w : Fin 4 → Idx → F) (v : Idx → F) : AL w v = v - Pp v + U0 w v := by
  simp [AL, Ppl_apply]

theorem Pp_ve0 : Pp (ve0 F) = 0 := by
  ext μ
  by_cases hμ : (Sum.elim id id μ).val < 2
  · simp [Pp_apply_of_lt _ hμ]
  · rw [Pp_apply_of_not_lt _ hμ, ve0_apply]
    have : μ ≠ Sum.inl 0 := by
      rintro rfl
      exact hμ (by decide)
    simp [this]

theorem AL_ve0 (w : Fin 4 → Idx → F) : AL w (ve0 F) = ve0 F := by
  rw [AL_apply, Pp_ve0, U0_of_vanish]
  · simp
  · intro k
    fin_cases k <;> simp [kap, ve0_apply]

theorem AL_inr0 {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k)) (v : Idx → F) :
    (AL w v) (Sum.inr 0) = v (Sum.inr 0) := by
  have h1 := VpC_U0 hw v (Sum.inr 0) (by decide)
  simp [AL_apply, h1, Pp_apply_of_lt _ (show (Sum.elim id id (Sum.inr (0 : Fin 4))).val < 2 by
    decide)]

theorem AL_VpC {w : Fin 4 → Idx → F} {c : Idx → F} (hc : VpC c) : AL w c = U0 w c := by
  rw [AL_apply, Pp_of_VpC hc]
  simp

theorem polar_AL_VpC {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l))
    {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    polar (quadPlus 4 F) (AL w v) (AL w c) = polar (quadPlus 4 F) v c := by
  rw [AL_VpC hc, AL_apply, QuadraticMap.polar_add_left, polar_U0 hG, Pp_of_VpC hc]
  have h1 : polar (quadPlus 4 F) (v - Pp v) (U0 w c) = 0 := by
    rw [polar_of_VpC (VpC_U0 hw c)]
    have e : ∀ μ, ¬ (Sum.elim id id μ).val < 2 → (v - Pp v) μ = 0 := fun μ hμ => by
      simp [Pp_apply_of_not_lt _ hμ]
    simp [e _ (show ¬ (Sum.elim id id (Sum.inl (2 : Fin 4))).val < 2 by decide),
      e _ (show ¬ (Sum.elim id id (Sum.inr (2 : Fin 4))).val < 2 by decide),
      e _ (show ¬ (Sum.elim id id (Sum.inl (3 : Fin 4))).val < 2 by decide),
      e _ (show ¬ (Sum.elim id id (Sum.inr (3 : Fin 4))).val < 2 by decide)]
  rw [h1, zero_add, polar_of_VpC hc, polar_of_VpC hc]
  simp [Pp]

theorem polar_AL_self {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l))
    (v : Idx → F) : polar (quadPlus 4 F) (AL w v) (AL w v) = polar (quadPlus 4 F) v v := by
  have hU := polar_U0 hG v v
  have h1 : ∀ x y : Idx → F, VpC y → polar (quadPlus 4 F) (x - Pp x) y = 0 := by
    intro x y hy
    rw [polar_of_VpC hy]
    have e : ∀ μ, ¬ (Sum.elim id id μ).val < 2 → (x - Pp x) μ = 0 := fun μ hμ => by
      simp [Pp_apply_of_not_lt _ hμ]
    simp [e _ (show ¬ (Sum.elim id id (Sum.inl (2 : Fin 4))).val < 2 by decide),
      e _ (show ¬ (Sum.elim id id (Sum.inr (2 : Fin 4))).val < 2 by decide),
      e _ (show ¬ (Sum.elim id id (Sum.inl (3 : Fin 4))).val < 2 by decide),
      e _ (show ¬ (Sum.elim id id (Sum.inr (3 : Fin 4))).val < 2 by decide)]
  have h2 : polar (quadPlus 4 F) v v = polar (quadPlus 4 F) (v - Pp v) (v - Pp v) +
      polar (quadPlus 4 F) (Pp v) (Pp v) := by
    have : v = (v - Pp v) + Pp v := by abel
    conv_lhs => rw [this]
    rw [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      h1 v _ (VpC_Pp v), QuadraticMap.polar_comm (quadPlus 4 F) (Pp v) (v - Pp v), h1 v _
        (VpC_Pp v)]
    ring
  rw [AL_apply, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_add_right, h1 v _ (VpC_U0 hw v), QuadraticMap.polar_comm (quadPlus 4 F)
      (U0 w v) (v - Pp v), h1 v _ (VpC_U0 hw v), h2, hU]
  ring

theorem Q_AL (h2 : (2 : F) ≠ 0) {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l))
    (v : Idx → F) : quadPlus 4 F (AL w v) = quadPlus 4 F v := by
  have h := polar_AL_self hw hG v
  rw [QuadraticMap.polar_self, QuadraticMap.polar_self] at h
  have h3 : (2 : F) * (quadPlus 4 F (AL w v) - quadPlus 4 F v) = 0 := by
    linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left h2)

theorem AL_eich (h2 : (2 : F) ≠ 0) {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l))
    {c : Idx → F} (hc : VpC c) (v : Idx → F) :
    AL w (eich c v) = eich (AL w c) (AL w v) := by
  simp only [eich, map_add, map_sub, map_smul, AL_ve0, AL_inr0 hw, polar_AL_VpC hw hG hc,
    Q_AL h2 hw hG]

@[expose] def VmC (u : Idx → F) : Prop := ∀ μ : Idx, ¬ (Sum.elim id id μ).val < 2 → u μ = 0

theorem Pp_of_VmC {u : Idx → F} (hu : VmC u) : Pp u = 0 := by
  ext μ
  by_cases hμ : (Sum.elim id id μ).val < 2
  · simp [Pp_apply_of_lt _ hμ]
  · simp [Pp_apply_of_not_lt _ hμ, hu μ hμ]

theorem AL_of_VmC (w : Fin 4 → Idx → F) {u : Idx → F} (hu : VmC u) : AL w u = u := by
  rw [AL_apply, Pp_of_VmC hu, U0_of_vanish]
  · simp
  · intro k
    exact hu _ (by fin_cases k <;> decide)

theorem AL_comm {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k)) {N : (Idx → F) →ₗ[F] (Idx → F)}
    (hN1 : ∀ x, N (Pp x) = 0) (hN2 : ∀ x, VmC (N x)) (v : Idx → F) :
    AL w (N v) = N (AL w v) := by
  have e1 : N (U0 w v) = 0 := by
    have := hN1 (U0 w v)
    rwa [Pp_of_VpC (VpC_U0 hw v)] at this
  rw [AL_of_VmC w (hN2 v), AL_apply, map_add, map_sub, hN1 v, e1]
  simp

theorem AL_injective {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l)) :
    Function.Injective (AL w) := by
  refine (injective_iff_map_eq_zero (AL w)).2 fun v hv => ?_
  have hco : ∀ μ, AL w v μ = 0 := fun μ => by rw [hv]; rfl
  have hU : U0 w v = 0 := by
    ext μ
    by_cases hμ : (Sum.elim id id μ).val < 2
    · exact VpC_U0 hw v μ hμ
    · have := hco μ
      rw [AL_apply] at this
      simpa [Pp_apply_of_not_lt _ hμ] using this
  have hV : ∀ μ, (Sum.elim id id μ).val < 2 → v μ = 0 := fun μ hμ => by
    have := hco μ
    rw [AL_apply] at this
    simpa [Pp_apply_of_lt _ hμ, VpC_U0 hw v μ hμ] using this
  have hP : ∀ l, polar (quadPlus 4 F) (Pp v) (ek F l) = 0 := by
    intro l
    have h1 := polar_U0 hG v (ek F l)
    rw [hU, QuadraticMap.polar_zero_left, Pp_of_VpC (show VpC (ek F l) from fun μ hμ => by
      rw [ek_apply]
      have : μ ≠ kap l := fun h => by
        subst h
        fin_cases l <;> simp [kap] at hμ
      simp [this])] at h1
    exact h1.symm
  have h0 := hP 0
  have h1 := hP 1
  have h2 := hP 2
  have h3 := hP 3
  have e0 : polar (quadPlus 4 F) (Pp v) (ek F 0) = Pp v (Sum.inr 2) :=
    polar_quadPlus_single_inl 4 F (Pp v) 2
  have e1 : polar (quadPlus 4 F) (Pp v) (ek F 1) = Pp v (Sum.inl 2) :=
    polar_quadPlus_single_inr 4 F (Pp v) 2
  have e2 : polar (quadPlus 4 F) (Pp v) (ek F 2) = Pp v (Sum.inr 3) :=
    polar_quadPlus_single_inl 4 F (Pp v) 3
  have e3 : polar (quadPlus 4 F) (Pp v) (ek F 3) = Pp v (Sum.inl 3) :=
    polar_quadPlus_single_inr 4 F (Pp v) 3
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  ext μ
  by_cases hμ : (Sum.elim id id μ).val < 2
  · exact hV μ hμ
  · rw [← Pp_apply_of_not_lt v hμ]
    rcases μ with i | i <;> fin_cases i <;> simp_all

@[expose] noncomputable def ALe {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l)) :
    (Idx → F) ≃ₗ[F] (Idx → F) :=
  LinearEquiv.ofInjectiveEndo (AL w) (AL_injective hw hG)

theorem ALe_apply {w : Fin 4 → Idx → F} (hw : ∀ k, VpC (w k))
    (hG : ∀ k l, polar (quadPlus 4 F) (w k) (w l) = polar (quadPlus 4 F) (ek F k) (ek F l))
    (v : Idx → F) : ALe hw hG v = AL w v := rfl

end IsoExt

end CFSG.ClassicalInvolution.G2D4Models.Twin
