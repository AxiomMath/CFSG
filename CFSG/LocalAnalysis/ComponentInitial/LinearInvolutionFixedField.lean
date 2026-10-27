module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedTools
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_fixed_basis_of_ne {σ : K ≃+* K} {x₀ : K} (hx₀ : σ x₀ ≠ x₀)
    (T : (Fin n → K) → (Fin n → K)) (hadd : ∀ v w, T (v + w) = T v + T w)
    (hsmul : ∀ (c : K) v, T (c • v) = σ c • T v) (hTT : ∀ v, T (T v) = v) :
    ∃ H : GL (Fin n) K, ∀ c : Fin n,
      T (fun r => (H : Matrix (Fin n) (Fin n) K) r c) =
        fun r => (H : Matrix (Fin n) (Fin n) K) r c := by
  classical
  have hd : σ x₀ - x₀ ≠ 0 := sub_ne_zero.2 hx₀
  set Fix : Set (Fin n → K) := {v | T v = v} with hFix
  have hspan : Submodule.span K Fix = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hw₁ : v + T v ∈ Fix := by
      change T (v + T v) = v + T v
      rw [hadd, hTT, add_comm]
    have hw₂ : x₀ • v + T (x₀ • v) ∈ Fix := by
      change T (x₀ • v + T (x₀ • v)) = x₀ • v + T (x₀ • v)
      rw [hadd, hTT, add_comm]
    have hv : v = (σ x₀ - x₀)⁻¹ • (σ x₀ • (v + T v) - (x₀ • v + T (x₀ • v))) := by
      rw [hsmul, smul_add, add_sub_add_comm, sub_self, add_zero, ← sub_smul, smul_smul,
        inv_mul_cancel₀ hd, one_smul]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span hw₁)) (Submodule.subset_span hw₂))
  obtain ⟨b, hbFix, hbspan, hbli⟩ := exists_linearIndependent K Fix
  rw [hspan] at hbspan
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → Fin n → K)) := by
    rw [Subtype.range_coe, hbspan]
  let bas₀ := Basis.mk hbli hsp
  let _ := FiniteDimensional.fintypeBasisIndex bas₀
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bas₀, Module.finrank_fin_fun]
  let bas := bas₀.reindex (Fintype.equivFinOfCardEq hcard)
  have hbas : ∀ c, T (bas c) = bas c := fun c => by
    rw [Basis.reindex_apply, Basis.mk_apply]
    exact hbFix (Subtype.mem _)
  obtain ⟨Hm, hHm⟩ : ∃ Hm : Matrix (Fin n) (Fin n) K, Hm = Matrix.of fun r c => bas c r :=
    ⟨_, rfl⟩
  have hHunit : IsUnit Hm := by
    rw [← mulVec_surjective_iff_isUnit]
    intro u
    refine ⟨bas.repr u, ?_⟩
    conv_rhs => rw [← bas.sum_repr u]
    ext r
    simp only [hHm, mulVec, dotProduct, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  refine ⟨hHunit.unit, fun c => ?_⟩
  have hcol : (fun r => (hHunit.unit : Matrix (Fin n) (Fin n) K) r c) = bas c := by
    rw [IsUnit.unit_spec, hHm]
    rfl
  rw [hcol]
  exact hbas c

theorem linear_field_involution_descent [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    Even f ∧ (∀ x, σ x = x ^ p ^ (f / 2)) ∧
      ∃ H : GL (Fin n) K, conjAut n K A * fieldAut n K σ =
        conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  classical
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have hsq :
      conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut n K (σ * σ) = 1 := by
    rw [← conjAut_mul_fieldAut_mul, ← pow_two]
    exact hα
  obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ hsq
  obtain ⟨hfeven, hσpow⟩ := even_and_eq_pow_of_involution_prime hp hf hK hσ hσσ
  have hσσx : ∀ x, σ (σ x) = x := fun x => by rw [← RingAut.mul_apply, hσσ]; rfl
  have hmapmap : GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.map (σ : K →+* K) A) =
      A := by
    ext i j
    simp [hσσx]
  have h1 : GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.scalar (Fin n) c) =
      GeneralLinearGroup.map (σ : K →+* K) A * A := by
    rw [hc, map_mul, hmapmap]
  have h2 : GeneralLinearGroup.map (σ : K →+* K) A * A = GeneralLinearGroup.scalar (Fin n) c := by
    have h3 :
        GeneralLinearGroup.map (σ : K →+* K) A = A⁻¹ * GeneralLinearGroup.scalar (Fin n) c := by
      rw [hc]
      group
    rw [h3, mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcfix : σ (c : K) = c := by
    have h3 := h1.trans h2
    have h4 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h3
    simpa [GeneralLinearGroup.coe_scalar] using h4
  obtain ⟨h, hh⟩ := hfeven
  have hud : UnitaryFieldData p h K := ⟨hp, by omega, by rw [hK, hh, two_mul]⟩
  have hbar : ∀ x, hud.bar x = σ x := fun x => by
    rw [UnitaryFieldData.bar_apply, hσpow, show f / 2 = h by omega]
  have hcinv : ((c⁻¹ : Kˣ) : K) ∈ hud.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, hbar, Units.val_inv_eq_inv_val, map_inv₀, hcfix]
  obtain ⟨b, hb⟩ := (unitary_field_norm hud).1 ⟨_, hcinv⟩
  have hb' : b * σ b = ((c⁻¹ : Kˣ) : K) := by
    have := congrArg Subtype.val hb
    rwa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm, hbar] at this
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hb'
    exact (Units.ne_zero _) hb'.symm
  set B := GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A with hB
  have hcB : conjAut n K B = conjAut n K A := by rw [hB, map_mul, conjAut_scalar, one_mul]
  have hBB : B * GeneralLinearGroup.map (σ : K →+* K) B = 1 := by
    rw [hB, map_mul, GeneralLinearGroup.map_scalar]
    calc GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) * A *
          (GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) (Units.mk0 b hb0)) *
            GeneralLinearGroup.map (σ : K →+* K) A)
        _ = GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0) *
            GeneralLinearGroup.scalar (Fin n) (Units.map (σ : K →* K) (Units.mk0 b hb0)) *
            (A * GeneralLinearGroup.map (σ : K →+* K) A) := by
          rw [mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
          group
        _ = 1 := by
          rw [← hc, ← map_mul, ← map_mul, ← map_one (GeneralLinearGroup.scalar (Fin n))]
          congr 1
          ext
          simp [hb']
  set T : (Fin n → K) → (Fin n → K) := fun v =>
    (B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i) with hT
  have hBBm : (B : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K).map σ = 1 := by
    have := congrArg Units.val hBB
    simpa using this
  have hTT : ∀ v, T (T v) = v := by
    intro v
    have hσBv : (fun i => σ (((B : Matrix (Fin n) (Fin n) K) *ᵥ fun i => σ (v i)) i)) =
        (B : Matrix (Fin n) (Fin n) K).map σ *ᵥ v := by
      funext i
      have h1 := RingHom.map_mulVec (σ : K →+* K) (B : Matrix (Fin n) (Fin n) K)
        (fun i => σ (v i)) i
      simp only [RingEquiv.coe_toRingHom] at h1
      rw [h1]
      congr 2
      funext j
      exact hσσx (v j)
    simp only [hT]
    rw [hσBv, mulVec_mulVec, hBBm, one_mulVec]
  have hadd : ∀ v w, T (v + w) = T v + T w := fun v w => by
    simp only [hT, Pi.add_apply, map_add]
    rw [← mulVec_add]
    rfl
  have hsmul : ∀ (a : K) v, T (a • v) = σ a • T v := fun a v => by
    simp only [hT, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← mulVec_smul]
    rfl
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, σ x₀ ≠ x₀ := by
    by_contra hall
    exact hσ (RingEquiv.ext fun x => by
      by_contra hx
      exact hall ⟨x, hx⟩)
  obtain ⟨H, hH⟩ := exists_fixed_basis_of_ne hx₀ T hadd hsmul hTT
  have hBH : B * GeneralLinearGroup.map (σ : K →+* K) H = H := by
    ext r c
    have := congrFun (hH c) r
    simp only [hT, mulVec, dotProduct] at this
    rw [← this]
    simp [Matrix.mul_apply]
  have hBeq : B = H * (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hBH
  refine ⟨⟨h, hh⟩, hσpow, H, ?_⟩
  have hfH : conjAut n K (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ * fieldAut n K σ =
      fieldAut n K σ * conjAut n K H⁻¹ := by
    rw [← map_inv, ← htrans.2.2.1 σ H⁻¹]
    group
  rw [← hcB, hBeq, map_mul, mul_assoc, hfH, ← mul_assoc, map_inv]

theorem toGL_slQuatI_ne_one : SpecialLinearGroup.toGL (QuaternionMatrices.slQuatI K) ≠ 1 := by
  intro h1
  have h1' : QuaternionMatrices.slQuatI K = 1 :=
    SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1'
  simp [QuaternionMatrices.slQuatI, QuaternionMatrices.quatI] at this

theorem map_blockSL_ne_scalar {F : Type*} [Field F] (ι : F →+* K) {m : ℕ} (hm : 1 ≤ m)
    {X : SpecialLinearGroup (Fin 2) F} (hX : (X : Matrix (Fin 2) (Fin 2) F) 0 0 = 0) (c : K) :
    ((SpecialLinearGroup.toGL (SpecialLinearGroup.map ι (blockSL F 2 m X)) :
        GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) ≠ scalar (Fin (2 + m)) c := by
  intro h
  have h0 := congrFun (congrFun h (finSumFinEquiv (Sum.inl 0))) (finSumFinEquiv (Sum.inl 0))
  have h1 := congrFun (congrFun h (finSumFinEquiv (Sum.inr ⟨0, by omega⟩)))
    (finSumFinEquiv (Sum.inr ⟨0, by omega⟩))
  rw [scalar_apply_finSumFinEquiv] at h0 h1
  simp only [↓reduceIte] at h0 h1
  change ι ((blockSL F 2 m X : Matrix (Fin (2 + m)) (Fin (2 + m)) F) _ _) = c at h0
  change ι ((blockSL F 2 m X : Matrix (Fin (2 + m)) (Fin (2 + m)) F) _ _) = c at h1
  rw [coe_blockSL, blockGL_apply_inl, SpecialLinearGroup.coe_GL_coe_matrix, hX, map_zero] at h0
  rw [coe_blockSL, blockGL_apply_inr, one_apply_eq, map_one] at h1
  exact zero_ne_one (h0.trans h1.symm)

theorem exists_fixed_perfect_even_fieldAut (hn : 3 ≤ n) (σ : K ≃+* K) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, fieldAut n K σ s = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
  set K₀ : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K) with hK₀
  have : Group.IsPerfect (SpecialLinearGroup (Fin (2 + m)) K₀) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn
  set ρ : SpecialLinearGroup (Fin (2 + m)) K₀ →* GL (Fin (2 + m)) K :=
    SpecialLinearGroup.toGL.comp (SpecialLinearGroup.map K₀.subtype) with hρ
  refine exists_fixed_perfect_even_of_hom ρ (fieldAut (2 + m) K σ) ?_
    (blockSL K₀ 2 m (QuaternionMatrices.slQuatI K₀)) ?_
    (map_blockSL_ne_scalar K₀.subtype (by omega) (by simp [QuaternionMatrices.slQuatI,
      QuaternionMatrices.quatI]))
  · intro g hg
    refine (fieldAut_proj σ _).trans ?_
    congr 1
    ext i j
    change σ ((g i j : K₀) : K) = ((g i j : K₀) : K)
    exact (g i j).2
  · rw [← map_pow, QuaternionMatrices.slQuatI_pow_four, map_one]

theorem exists_fixed_perfect_even_conjAut_fieldAut [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hK : Nat.card K = p ^ f) (hn : 3 ≤ n) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hα : (conjAut n K A * fieldAut n K σ) ^ 2 = 1) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, (conjAut n K A * fieldAut n K σ) s = s := by
  obtain ⟨-, -, H, hH⟩ := linear_field_involution_descent hp hf hK hn A σ hσ hα
  exact exists_fixed_perfect_even_conj hH (exists_fixed_perfect_even_fieldAut hn σ)

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
