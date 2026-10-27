module

public import CFSG.GH74.Generic.S1.KL3ClEig
public import CFSG.GH74.Generic.S1.KL3ClSL3
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.S1

section Duality

variable {Ω : Type*} [Field Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem kl3cl_eig_transpose (A : Matrix ι ι Ω) (c : Ω) :
    (∃ v : ι → Ω, v ≠ 0 ∧ Aᵀ *ᵥ v = c • v) ↔ ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = c • v := by
  have key : ∀ M : Matrix ι ι Ω, (∃ v : ι → Ω, v ≠ 0 ∧ M *ᵥ v = c • v) ↔ (M - c • 1).det = 0 := by
    intro M
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [key, key]
  have : (Aᵀ - c • (1 : Matrix ι ι Ω)) = (A - c • 1)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rw [this, Matrix.det_transpose]

theorem kl3cl_dual_sp (A J : Matrix ι ι Ω) (hJ : J.det ≠ 0) (hA : Aᵀ * J * A = J) {μ : Ω}
    (h : ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = μ • v) : ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = μ⁻¹ • v := by
  obtain ⟨v, hv, hAv⟩ := h
  have hJinj : ∀ w : ι → Ω, J *ᵥ w = 0 → w = 0 := by
    intro w hw
    by_contra hw0
    exact hJ (Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw0, hw⟩)
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hAv
    have : J *ᵥ v = 0 := by
      calc J *ᵥ v = (Aᵀ * J * A) *ᵥ v := by rw [hA]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hAv]; simp
    exact hv (hJinj v this)
  have hJv : J *ᵥ v ≠ 0 := fun h0 => hv (hJinj v h0)
  have h1 : Aᵀ *ᵥ (J *ᵥ v) = μ⁻¹ • (J *ᵥ v) := by
    have h2 : μ • (Aᵀ *ᵥ (J *ᵥ v)) = J *ᵥ v := by
      calc μ • (Aᵀ *ᵥ (J *ᵥ v)) = Aᵀ *ᵥ (J *ᵥ (μ • v)) := by
            simp only [Matrix.mulVec_smul]
        _ = (Aᵀ * J * A) *ᵥ v := by
            rw [← hAv]; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = J *ᵥ v := by rw [hA]
    calc Aᵀ *ᵥ (J *ᵥ v) = μ⁻¹ • (μ • (Aᵀ *ᵥ (J *ᵥ v))) := by
          rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • (J *ᵥ v) := by rw [h2]
  exact (kl3cl_eig_transpose A μ⁻¹).1 ⟨J *ᵥ v, hJv, h1⟩

theorem kl3cl_dual_su (A : Matrix ι ι Ω) (σ : Ω ≃+* Ω) (hA : (A.map σ)ᵀ * A = 1) {μ : Ω}
    (h : ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = μ • v) :
    ∃ v : ι → Ω, v ≠ 0 ∧ A *ᵥ v = σ.symm μ⁻¹ • v := by
  obtain ⟨v, hv, hAv⟩ := h
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hAv
    apply hv
    calc v = (A.map σ)ᵀ *ᵥ (A *ᵥ v) := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
      _ = 0 := by rw [hAv, Matrix.mulVec_zero]
  have h1 : (A.map σ)ᵀ *ᵥ v = μ⁻¹ • v := by
    have h2 : μ • ((A.map σ)ᵀ *ᵥ v) = v := by
      calc μ • ((A.map σ)ᵀ *ᵥ v) = (A.map σ)ᵀ *ᵥ (A *ᵥ v) := by
            rw [hAv, Matrix.mulVec_smul]
        _ = v := by rw [Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]
    calc (A.map σ)ᵀ *ᵥ v = μ⁻¹ • (μ • ((A.map σ)ᵀ *ᵥ v)) := by
          rw [smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      _ = μ⁻¹ • v := by rw [h2]
  obtain ⟨w, hw, hAw⟩ := (kl3cl_eig_transpose (A.map σ) μ⁻¹).1 ⟨v, hv, h1⟩
  refine ⟨fun j => σ.symm (w j), ?_, ?_⟩
  · intro h0
    apply hw
    ext i
    have := congrFun h0 i
    simpa using this
  · ext i
    apply σ.injective
    have h3 := RingHom.map_mulVec (σ : Ω →+* Ω) A (fun j => σ.symm (w j)) i
    have h4 : ((σ : Ω →+* Ω) ∘ fun j => σ.symm (w j)) = w := by
      ext j; simp
    rw [h4] at h3
    have h5 := congrFun hAw i
    simp only [Pi.smul_apply, smul_eq_mul] at h5 ⊢
    simp only [RingEquiv.coe_toRingHom] at h3
    rw [h3, h5]
    simp

theorem kl3cl_frob_symm_pow [PerfectRing Ω 3] [ExpChar Ω 3] (f : ℕ) {y : Ω} (hy : y ^ 13 = 1) :
    (iterateFrobeniusEquiv Ω 3 f).symm y = y ^ (9 ^ f) := by
  rw [RingEquiv.symm_apply_eq, iterateFrobeniusEquiv_apply, iterateFrobenius_def, ← pow_mul,
    pow_eq_pow_mod _ hy]
  have h : (9 ^ f * 3 ^ f) % 13 = 1 := by
    rw [← mul_pow, Nat.pow_mod]
    norm_num
  rw [h, pow_one]

end Duality

section Rep

theorem kl3cl_gl_mulVec_inj {Ω : Type*} [Field Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : GL ι Ω) (v : ι → Ω) (h : (x : Matrix ι ι Ω) *ᵥ v = 0) : v = 0 := by
  have := congrArg (fun w => ((x⁻¹ : GL ι Ω) : Matrix ι ι Ω) *ᵥ w) h
  simpa [Matrix.mulVec_mulVec] using this

theorem kl3cl_base_injective {ι : Type*} [Fintype ι] [DecidableEq ι] {K Ω : Type*} [Field K]
    [Field Ω] [Algebra K Ω] :
    Function.Injective (Matrix.GeneralLinearGroup.map (algebraMap K Ω) : GL ι K →* GL ι Ω) :=
  fun _ _ h => Units.ext (Matrix.map_injective (algebraMap K Ω).injective
    (congrArg (fun u : GL ι Ω => (u : Matrix ι ι Ω)) h))

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {F : Type} [Field F] [Finite F]

theorem kl3cl_card_ge_six_of_char_ne_three (h3 : (3 : K) ≠ 0) (hF : Nat.card F = 3)
    (ρ : SL(3, F) →* GL ι K) (hρ : Function.Injective ρ) : 6 ≤ Fintype.card ι := by
  classical
  obtain ⟨a, b, z, s, hab, hza, hzb, hz3, hzne, hsz⟩ := kl3cl_heis F hF
  let Ω := AlgebraicClosure K
  let Φ : GL ι K →* GL ι Ω := Matrix.GeneralLinearGroup.map (algebraMap K Ω)
  let ψ : SL(3, F) →* GL ι Ω := Φ.comp ρ
  have hψinj : Function.Injective ψ := kl3cl_base_injective.comp hρ
  have h3Ω : ((3 : ℕ) : Ω) ≠ 0 := by
    have h1 : (3 : Ω) ≠ 0 := by
      intro h
      apply h3
      apply (algebraMap K Ω).injective
      rw [map_ofNat, map_zero]
      exact h
    simpa using h1
  have hval : ∀ x y : SL(3, F), ψ x * ψ y = ψ (x * y) := fun x y => (map_mul ψ x y).symm
  refine kl3cl_heisenberg_dim h3Ω (ψ a : Matrix ι ι Ω) (ψ b) (ψ z) (ψ s) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← Units.val_pow_eq_pow_val, ← map_pow, hz3, map_one, Units.val_one]
  · intro h
    have : ψ z = 1 := Units.ext (by simpa using h)
    exact hzne (hψinj (by rw [this, map_one]))
  · have := congrArg (fun u : GL ι Ω => (u : Matrix ι ι Ω)) (congrArg ψ hza)
    simpa [map_mul] using this
  · have := congrArg (fun u : GL ι Ω => (u : Matrix ι ι Ω)) (congrArg ψ hzb)
    simpa [map_mul] using this
  · have := congrArg (fun u : GL ι Ω => (u : Matrix ι ι Ω)) (congrArg ψ hab)
    simpa [map_mul] using this
  · exact fun v hv => kl3cl_gl_mulVec_inj (ψ a) v hv
  · exact fun v hv => kl3cl_gl_mulVec_inj (ψ b) v hv
  · exact fun v hv => kl3cl_gl_mulVec_inj (ψ s) v hv
  · have := congrArg (fun u : GL ι Ω => (u : Matrix ι ι Ω)) (congrArg ψ hsz)
    simpa [map_mul, map_pow] using this

theorem kl3cl_nine_pow_mod (f : ℕ) :
    9 ^ f % 13 = 1 ∨ 9 ^ f % 13 = 3 ∨ 9 ^ f % 13 = 9 := by
  induction f with
  | zero => left; norm_num
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod]
    omega

theorem kl3cl_card_ge_six_of_dual [CharP K 3] (hF : Nat.card F = 3) (ρ : SL(3, F) →* GL ι K)
    (hρ : Function.Injective ρ) (r : ℕ) (hr : r % 13 = 1 ∨ r % 13 = 3 ∨ r % 13 = 9)
    (hdual : ∀ g : SL(3, F), g ^ 13 = 1 → ∀ μ : AlgebraicClosure K, μ ^ 13 = 1 →
      (∃ v : ι → AlgebraicClosure K, v ≠ 0 ∧
        (((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) *ᵥ v = μ • v) →
      ∃ v : ι → AlgebraicClosure K, v ≠ 0 ∧
        (((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) *ᵥ v =
          (μ⁻¹) ^ r • v) :
    6 ≤ Fintype.card ι := by
  classical
  obtain ⟨g, h, hg13, hgne, hhg⟩ := kl3cl_frob F hF
  let Ω := AlgebraicClosure K
  let Φ : GL ι K →* GL ι Ω := Matrix.GeneralLinearGroup.map (algebraMap K Ω)
  let ψ : SL(3, F) →* GL ι Ω := Φ.comp ρ
  have hψinj : Function.Injective ψ := kl3cl_base_injective.comp hρ
  have h13 : ((13 : ℕ) : Ω) ≠ 0 := by
    have h12 : ((12 : ℕ) : Ω) = 0 := (CharP.cast_eq_zero_iff Ω 3 12).2 (by norm_num)
    have : ((13 : ℕ) : Ω) = ((12 : ℕ) : Ω) + 1 := by norm_num
    rw [this, h12, zero_add]
    exact one_ne_zero
  refine kl3cl_frobenius_dim h13 (ψ g : Matrix ι ι Ω) (ψ h) ?_ ?_ ?_ ?_ r hr ?_
  · rw [← Units.val_pow_eq_pow_val, ← map_pow, hg13, map_one, Units.val_one]
  · intro hc
    have : ψ g = 1 := Units.ext (by simpa using hc)
    exact hgne (hψinj (by rw [this, map_one]))
  · exact fun v hv => kl3cl_gl_mulVec_inj (ψ h) v hv
  · have := congrArg (fun u : GL ι Ω => (u : Matrix ι ι Ω)) (congrArg ψ hhg)
    simpa [map_mul, map_pow] using this
  · intro μ hμ hex
    exact hdual g hg13 μ hμ hex

theorem kl3cl_card_ge_six_sp [CharP K 3] (hF : Nat.card F = 3) (ρ : SL(3, F) →* GL ι K)
    (hρ : Function.Injective ρ) (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hform : ∀ g : SL(3, F),
      ((ρ g : GL ι K) : Matrix ι ι K)ᵀ * J * ((ρ g : GL ι K) : Matrix ι ι K) = J) :
    6 ≤ Fintype.card ι := by
  classical
  refine kl3cl_card_ge_six_of_dual hF ρ hρ 1 (Or.inl rfl) ?_
  intro g _ μ _ hex
  have hJΩ : (J.map (algebraMap K (AlgebraicClosure K))).det ≠ 0 := by
    have h : (J.map (algebraMap K (AlgebraicClosure K))).det =
        algebraMap K (AlgebraicClosure K) J.det :=
      (RingHom.map_det (algebraMap K (AlgebraicClosure K)) J).symm
    rw [h]
    exact fun h0 => hJ ((algebraMap K (AlgebraicClosure K)).injective (by rw [h0, map_zero]))
  have hA : ((((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)))ᵀ *
      J.map (algebraMap K (AlgebraicClosure K)) *
      ((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))) =
      J.map (algebraMap K (AlgebraicClosure K)) := by
    have h2 := congrArg (fun M : Matrix ι ι K => M.map (algebraMap K (AlgebraicClosure K)))
      (hform g)
    simpa [Matrix.map_mul, Matrix.transpose_map] using h2
  simpa using kl3cl_dual_sp _ _ hJΩ hA hex

theorem kl3cl_card_ge_six_su [CharP K 3] (f : ℕ) (hF : Nat.card F = 3)
    (ρ : SL(3, F) →* GL ι K) (hρ : Function.Injective ρ)
    (hform : ∀ g : SL(3, F),
      (((ρ g : GL ι K) : Matrix ι ι K).map (· ^ (3 ^ f)))ᵀ * ((ρ g : GL ι K) : Matrix ι ι K) = 1) :
    6 ≤ Fintype.card ι := by
  classical
  refine kl3cl_card_ge_six_of_dual hF ρ hρ (9 ^ f) (kl3cl_nine_pow_mod f) ?_
  intro g _ μ hμ hex
  let σ : AlgebraicClosure K ≃+* AlgebraicClosure K := iterateFrobeniusEquiv (AlgebraicClosure K) 3 f
  have hA : ((((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))).map σ)ᵀ *
      ((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K)) = 1 := by
    have h2 := congrArg (fun M : Matrix ι ι K => M.map (algebraMap K (AlgebraicClosure K)))
      (hform g)
    have h3 : ((((ρ g : GL ι K) : Matrix ι ι K).map (algebraMap K (AlgebraicClosure K))).map σ) =
        (((ρ g : GL ι K) : Matrix ι ι K).map (· ^ (3 ^ f))).map
          (algebraMap K (AlgebraicClosure K)) := by
      ext i j
      simp [σ, iterateFrobenius_def, map_pow]
    rw [h3]
    simpa [Matrix.map_mul, Matrix.transpose_map] using h2
  obtain ⟨v, hv, hAv⟩ := kl3cl_dual_su _ σ hA hex
  refine ⟨v, hv, ?_⟩
  rw [hAv]
  have hinv : (μ⁻¹) ^ 13 = 1 := by rw [inv_pow, hμ, inv_one]
  rw [kl3cl_frob_symm_pow f hinv]

end Rep

end CFSG.GH74.Generic.S1
