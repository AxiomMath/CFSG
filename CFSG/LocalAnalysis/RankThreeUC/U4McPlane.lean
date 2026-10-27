module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFQuad
public import CFSG.ClassicalGroups.Unitary.Transitivity

public section

namespace CFSG.LocalAnalysis.RankThreeUC.U4Mc

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.RankThreeUC (sesqPerp mem_sesqPerp_iff qd_finrank_sesqPerp_add)

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def IsTI (σ : F ≃+* F) (W : Submodule F (Fin 4 → F)) : Prop :=
  ∀ w ∈ W, ∀ w' ∈ W, herm σ w w' = 0

theorem IsTI.le_sesqPerp {W : Submodule F (Fin 4 → F)} (h : IsTI σ W) : W ≤ sesqPerp σ W :=
  fun x hx => mem_sesqPerp_iff.mpr fun w hw => h w hw x hx

theorem IsTI.finrank_le [Finite F] {W : Submodule F (Fin 4 → F)} (h : IsTI σ W) :
    Module.finrank F W ≤ 2 := by
  have h1 := qd_finrank_sesqPerp_add σ W
  have h2 := Submodule.finrank_mono h.le_sesqPerp
  omega

theorem IsTI.sesqPerp_eq [Finite F] {W : Submodule F (Fin 4 → F)} (h : IsTI σ W)
    (h2 : Module.finrank F W = 2) : sesqPerp σ W = W := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq h.le_sesqPerp ?_
  have := qd_finrank_sesqPerp_add σ W
  omega

theorem IsTI.mem_of_herm_eq_zero [Finite F] {W : Submodule F (Fin 4 → F)} (h : IsTI σ W)
    (h2 : Module.finrank F W = 2) {x : Fin 4 → F} (hx : ∀ w ∈ W, herm σ w x = 0) : x ∈ W := by
  rw [← h.sesqPerp_eq h2]
  exact mem_sesqPerp_iff.mpr hx

theorem exists_mem_T_smul_fix (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {a a' : Fin n → F}
    (ha : herm σ a a = 0) (ha' : herm σ a' a' = 0) (hs0 : herm σ a a' ≠ 0)
    (hs : herm σ a a' + σ (herm σ a a') = 0) :
    ∃ t ∈ T σ n, t • a = a' ∧ ∀ v, herm σ a v = 0 → herm σ a' v = 0 → t • v = v := by
  have hσs : σ (herm σ a a') = -herm σ a a' := by linear_combination hs
  have hc : -(herm σ a a')⁻¹ + σ (-(herm σ a a')⁻¹) = 0 := by
    rw [map_neg, map_inv₀, hσs, inv_neg]
    ring
  refine ⟨tv hσ ha hc * tv hσ ha' hc,
    (T σ n).mul_mem (tv_mem_T hσ ha hc) (tv_mem_T hσ ha' hc), ?_, fun v hav ha'v => ?_⟩
  · have hsa : herm σ a' a = σ (herm σ a a') := herm_conj σ hσ a a'
    rw [mul_smul, tv_smul, tv_smul]
    simp only [herm_add_right, herm_smul_right, ha, hsa, hσs]
    match_scalars
    all_goals field_simp
    all_goals ring
  · have h1 : tv hσ ha' hc • v = v := by
      rw [tv_smul, ha'v, mul_zero, zero_smul, add_zero]
    rw [mul_smul, h1, tv_smul, hav, mul_zero, zero_smul, add_zero]

theorem exists_pair_of_finrank_eq_two [Finite F] {X : Submodule F (Fin 4 → F)}
    (hX2 : Module.finrank F X = 2) :
    ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ 0 ∧ (∀ z ∈ X, ∃ α β : F, α • x₁ + β • x₂ = z) ∧
      ∀ α β : F, α • x₁ + β • x₂ = 0 → α = 0 ∧ β = 0 := by
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [finrank_bot] at hX2
    omega
  obtain ⟨x₁, hx₁X, hx₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
  have hlt : (F ∙ x₁) < X := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁X) fun h => ?_
    rw [← h, finrank_span_singleton hx₁0] at hX2
    omega
  obtain ⟨x₂, hx₂X, hx₂⟩ := SetLike.exists_of_lt hlt
  have hspan : Submodule.span F {x₁, x₂} = X := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      intro z hz
      rcases hz with rfl | hz
      · exact hx₁X
      · rw [Set.mem_singleton_iff.mp hz]
        exact hx₂X
    · have h1 : (F ∙ x₁) < Submodule.span F {x₁, x₂} := by
        refine lt_of_le_of_ne (Submodule.span_mono (by simp)) fun h => hx₂ ?_
        rw [h]
        exact Submodule.subset_span (by simp)
      have := Submodule.finrank_lt_finrank_of_lt h1
      rw [finrank_span_singleton hx₁0] at this
      omega
  refine ⟨x₁, hx₁X, x₂, hx₂X, hx₁0, fun z hz => ?_, fun α β h => ?_⟩
  · rw [← hspan] at hz
    exact Submodule.mem_span_pair.mp hz
  · have hβ : β = 0 := by
      by_contra hβ
      apply hx₂
      have e : x₂ = (-(α / β)) • x₁ := by
        have h' : β • x₂ = -(α • x₁) := eq_neg_of_add_eq_zero_right h
        calc x₂ = β⁻¹ • (β • x₂) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
          _ = (-(α / β)) • x₁ := by rw [h', smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x₁)
    rw [hβ, zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right hx₁0, hβ⟩

theorem exists_smul_mem_of_isTI [Finite F] (hσ : IsUnitaryInvolution σ)
    {X Y : Submodule F (Fin 4 → F)} (hX : IsTI σ X) (hX2 : Module.finrank F X = 2)
    (hY : IsTI σ Y) (hY2 : Module.finrank F Y = 2) :
    ∃ g : SUid σ 4, ∀ x ∈ X, g • x ∈ Y := by
  obtain ⟨x₁, hx₁X, x₂, hx₂X, hx₁0, hXspan, -⟩ := exists_pair_of_finrank_eq_two hX2
  obtain ⟨y₁, hy₁Y, -, -, hy₁0, -, -⟩ := exists_pair_of_finrank_eq_two hY2
  obtain ⟨t₁, -, ht₁⟩ := exists_mem_T_smul_eq_of_iso hσ (by norm_num) hx₁0
    (hX x₁ hx₁X x₁ hx₁X) hy₁0 (hY y₁ hy₁Y y₁ hy₁Y)
  have hx'x' : herm σ (t₁ • x₂) (t₁ • x₂) = 0 := by
    rw [herm_smul_smul]
    exact hX x₂ hx₂X x₂ hx₂X
  have hy₁x' : herm σ y₁ (t₁ • x₂) = 0 := by
    rw [← ht₁, herm_smul_smul]
    exact hX x₁ hx₁X x₂ hx₂X
  have hx'y₁ : herm σ (t₁ • x₂) y₁ = 0 := herm_eq_zero_comm σ hσ.invol hy₁x'
  obtain ⟨t₂, ht₂y, ht₂x⟩ : ∃ t₂ : SUid σ 4, t₂ • y₁ = y₁ ∧ t₂ • (t₁ • x₂) ∈ Y := by
    by_cases hperp : ∀ y ∈ Y, herm σ (t₁ • x₂) y = 0
    · refine ⟨1, one_smul _ _, ?_⟩
      rw [one_smul]
      exact hY.mem_of_herm_eq_zero hY2 fun y hy =>
        herm_eq_zero_comm σ hσ.invol (hperp y hy)
    · push Not at hperp
      obtain ⟨y'', hy''Y, hs⟩ := hperp
      obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
      have hy₃Y : (τ / herm σ (t₁ • x₂) y'') • y'' ∈ Y := Y.smul_mem _ hy''Y
      have h3 : herm σ (t₁ • x₂) ((τ / herm σ (t₁ • x₂) y'') • y'') = τ := by
        rw [herm_smul_right]
        field_simp
      obtain ⟨t₂, -, ht₂a, ht₂v⟩ := exists_mem_T_smul_fix hσ.invol hx'x' (hY _ hy₃Y _ hy₃Y)
        (by rw [h3]; exact hτ0) (by rw [h3]; exact hτ)
      refine ⟨t₂, ht₂v y₁ hx'y₁ (hY _ hy₃Y y₁ hy₁Y), ?_⟩
      rw [ht₂a]
      exact hy₃Y
  refine ⟨t₂ * t₁, fun z hz => ?_⟩
  obtain ⟨α, β, rfl⟩ := hXspan z hz
  rw [smul_add, smul_comm (t₂ * t₁) α, smul_comm (t₂ * t₁) β, mul_smul, mul_smul, ht₁, ht₂y]
  exact Y.add_mem (Y.smul_mem _ hy₁Y) (Y.smul_mem _ ht₂x)

@[expose] def eigenSub (M : Matrix (Fin 4) (Fin 4) F) (c : F) : Submodule F (Fin 4 → F) :=
  LinearMap.ker (Matrix.toLin' M - c • LinearMap.id)

theorem mem_eigenSub {M : Matrix (Fin 4) (Fin 4) F} {c : F} {v : Fin 4 → F} :
    v ∈ eigenSub M c ↔ M *ᵥ v = c • v := by
  rw [eigenSub, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.toLin'_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem card_le_finrank_add_finrank_eigen {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {M : Matrix ι ι K} (hM3 : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v)) = v)
    (hfix : ∀ v, M *ᵥ v = v → v = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    Fintype.card ι ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' M - ω • LinearMap.id)) +
      Module.finrank K (LinearMap.ker (Matrix.toLin' M - ω ^ 2 • LinearMap.id)) := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hrange : LinearMap.range (Matrix.toLin' M - ω ^ 2 • LinearMap.id) ≤
      LinearMap.ker (Matrix.toLin' M - ω • LinearMap.id) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    have hz : M *ᵥ (M *ᵥ v) + M *ᵥ v + v = 0 := by
      apply hfix
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hM3 v]
      abel
    simp only [LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Matrix.mulVec_sub, Matrix.mulVec_smul]
    linear_combination (norm := module) hz - hω • (M *ᵥ v) + hω3 • v
  have hr := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M - ω ^ 2 • LinearMap.id)
  rw [Module.finrank_fintype_fun_eq_card] at hr
  have h1 := Submodule.finrank_mono hrange
  omega

theorem isTI_eigenSub {M : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ x y, herm σ (M *ᵥ x) (M *ᵥ y) = herm σ x y) {c : F} (hc : σ c * c ≠ 1) :
    IsTI σ (eigenSub M c) := by
  intro v hv w hw
  have h1 := hM v w
  rw [mem_eigenSub.mp hv, mem_eigenSub.mp hw, herm_smul_left, herm_smul_right] at h1
  have h2 : (σ c * c - 1) * herm σ v w = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hc
  · exact h

theorem finrank_eigenSub [Finite F] (h2 : (2 : F) = 0) {M : Matrix (Fin 4) (Fin 4) F}
    (hM : ∀ x y, herm σ (M *ᵥ x) (M *ᵥ y) = herm σ x y) (hM3 : ∀ v, M *ᵥ (M *ᵥ (M *ᵥ v)) = v)
    (hfix : ∀ v, M *ᵥ v = v → v = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (hσω : σ ω = ω) :
    Module.finrank F (eigenSub M ω) = 2 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : σ ω * ω ≠ 1 := by
    rw [hσω]
    intro h
    have hω0 : ω = 0 := by linear_combination hω - h - h2
    rw [hω0, mul_zero] at h
    exact zero_ne_one h
  have hω21 : σ (ω ^ 2) * ω ^ 2 ≠ 1 := by
    rw [map_pow, hσω]
    intro h
    have hω' : ω = 1 := by linear_combination h - ω * hω3
    rw [hω'] at hω
    have h10 : (1 : F) = 0 := by linear_combination hω - h2
    exact one_ne_zero h10
  have hTI1 := isTI_eigenSub hM hω1
  have hTI2 := isTI_eigenSub hM hω21
  have hsum := card_le_finrank_add_finrank_eigen hM3 hfix hω
  rw [Fintype.card_fin] at hsum
  have h2' : Module.finrank F (LinearMap.ker (Matrix.toLin' M - ω ^ 2 • LinearMap.id)) ≤ 2 :=
    hTI2.finrank_le
  have h3 := hTI1.finrank_le
  change 4 ≤ Module.finrank F (eigenSub M ω) + _ at hsum
  omega

theorem exists_cubeRoot [Finite F] {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2) (hn : Even n) :
    ∃ ω : F, ω ^ 2 + ω + 1 = 0 ∧ ω ^ (2 ^ n) = ω := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : 3 ∣ Fintype.card Fˣ := by
    have e : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF, e]
    have h : 1 ≡ 4 ^ n [MOD 3] := by
      have := (show 1 ≡ 4 [MOD 3] by decide).pow n
      rwa [one_pow] at this
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
  have hu3 : (u : F) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  have hu1 : (u : F) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  refine ⟨u, ?_, ?_⟩
  · have h : ((u : F) - 1) * ((u : F) ^ 2 + u + 1) = 0 := by linear_combination hu3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hu1
    · exact h
  · obtain ⟨m, rfl⟩ := hn
    have hmod : 2 ^ (m + m) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    have h := pow_mod_orderOf u (2 ^ (m + m))
    rw [hu, hmod, pow_one] at h
    rw [← Units.val_pow_eq_pow_val, ← h]

end CFSG.LocalAnalysis.RankThreeUC.U4Mc
