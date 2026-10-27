module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearFlag

open Matrix Module Polynomial

variable {n : ℕ} {K : Type*} [Field K]

theorem exists_fixed_perfect_even_conjAut_of_mul_self_eq_nonsquare
    (h4 : ∃ s : Finset K, s.card = 4) (hn : 3 ≤ n) (A : GL (Fin n) K) {c : K}
    (hc : ∀ μ : K, μ * μ ≠ c) (hA : (A : Matrix (Fin n) (Fin n) K) * A = c • 1) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, conjAut n K A s = s := by
  classical
  have : Group.IsPerfect (SpecialLinearGroup (Fin 2) K) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  set q : K[X] := X ^ 2 - C c with hqdef
  have hq : Irreducible q := X_pow_sub_C_irreducible_of_prime Nat.prime_two
    (fun μ hμ => hc μ (by rw [← sq]; exact hμ))
  have : Fact (Irreducible q) := ⟨hq⟩
  set T : Module.End K (Fin n → K) := toLin' (A : Matrix (Fin n) (Fin n) K) with hTdef
  have hT : aeval T q = 0 := by
    rw [hqdef, map_sub, map_pow, aeval_X, aeval_C, sq, hTdef, Module.End.mul_eq_comp,
      ← Matrix.toLin'_mul, hA, Algebra.algebraMap_eq_smul_one, map_smul, Matrix.toLin'_one]
    exact sub_eq_zero.2 rfl
  let φ : AdjoinRoot q →ₐ[K] Module.End K (Fin n → K) :=
    Ideal.Quotient.liftₐ (Ideal.span {q}) (aeval T) fun a ha => by
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, hT, mul_zero]
  have hφroot : φ (AdjoinRoot.root q) = T := aeval_X T
  let _ : Module (AdjoinRoot q) (Fin n → K) := Module.compHom (Fin n → K) φ.toRingHom
  have : IsScalarTower K (AdjoinRoot q) (Fin n → K) := ⟨fun a e v => by
    change φ (a • e) v = a • φ e v
    rw [map_smul, LinearMap.smul_apply]⟩
  have : Module.Finite (AdjoinRoot q) (Fin n → K) :=
    Module.Finite.of_restrictScalars_finite K _ _
  have hdeg : q.natDegree = 2 := by rw [hqdef]; exact natDegree_X_pow_sub_C
  have hE : finrank K (AdjoinRoot q) = 2 := by
    rw [(AdjoinRoot.powerBasis hq.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hfr := Module.finrank_mul_finrank K (AdjoinRoot q) (Fin n → K)
  rw [hE, finrank_fin_fun] at hfr
  have hroot : ∀ v : Fin n → K, (AdjoinRoot.root q) • v = T v := fun v => by
    change φ (AdjoinRoot.root q) v = T v
    rw [hφroot]
  obtain ⟨m, hm⟩ : ∃ m, finrank (AdjoinRoot q) (Fin n → K) = 2 + m :=
    ⟨finrank (AdjoinRoot q) (Fin n → K) - 2, by omega⟩
  let b : Basis (Fin (2 + m)) (AdjoinRoot q) (Fin n → K) := Module.finBasisOfFinrankEq _ _ hm
  let rs : Module.End (AdjoinRoot q) (Fin n → K) →* Module.End K (Fin n → K) :=
    { toFun := fun g => g.restrictScalars K
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρ : SpecialLinearGroup (Fin 2) K →* GL (Fin n) K :=
    GeneralLinearGroup.toLin.symm.toMonoidHom.comp
      ((Units.map (rs.comp (MonoidHom.ofClass (Matrix.toLinAlgEquiv b)))).comp
        ((GeneralLinearGroup.map (algebraMap K (AdjoinRoot q))).comp
          ((blockGL K 2 m).comp SpecialLinearGroup.toGL)))
  have hρ : ∀ X, toLin' ((ρ X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Matrix.toLinAlgEquiv b ((((blockGL K 2 m (SpecialLinearGroup.toGL X) :
        GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K)).map
          (algebraMap K (AdjoinRoot q)))).restrictScalars K := fun X =>
    Matrix.toLin'_toMatrix' _
  have hcomm : ∀ X, (A : Matrix (Fin n) (Fin n) K) * (ρ X : Matrix (Fin n) (Fin n) K) =
      (ρ X : Matrix (Fin n) (Fin n) K) * A := fun X => by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hρ, ← hTdef]
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalars_apply, ← hroot, ← hroot, LinearMap.map_smul]
  refine exists_fixed_perfect_even_of_hom ρ (conjAut n K A) ?_ (QuaternionMatrices.slQuatI K)
    QuaternionMatrices.slQuatI_pow_four ?_
  · intro X hX
    refine (conjAut_proj A _).trans ?_
    congr 1
    apply Subtype.ext
    refine (coe_slConjugation A _).trans ?_
    change (A : Matrix (Fin n) (Fin n) K) * (ρ X : Matrix (Fin n) (Fin n) K) *
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = ρ X
    rw [hcomm, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  · intro c' hc'
    set i₀ : Fin (2 + m) := finSumFinEquiv (Sum.inl 0) with hi₀
    set i₁ : Fin (2 + m) := finSumFinEquiv (Sum.inl 1) with hi₁
    have hL := congrArg (fun M => toLin' M (b i₀)) hc'
    rw [hρ, LinearMap.restrictScalars_apply, Matrix.toLinAlgEquiv_self] at hL
    have hs : toLin' (scalar (Fin n) c') (b i₀) =
        algebraMap K (AdjoinRoot q) c' • b i₀ := by
      rw [algebraMap_smul, scalar_apply, ← smul_one_eq_diagonal, map_smul, Matrix.toLin'_one,
        LinearMap.smul_apply, LinearMap.id_apply]
    rw [hs] at hL
    have h1 := congrArg (fun v => b.repr v i₁) hL
    have hne : i₀ ≠ i₁ := fun h => by
      have := finSumFinEquiv.injective h
      simp at this
    simp only [map_sum, map_smul, Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, hne] at h1
    rw [map_apply, hi₁, hi₀, blockGL_apply_inl, SpecialLinearGroup.coe_GL_coe_matrix] at h1
    change algebraMap K (AdjoinRoot q) (QuaternionMatrices.quatI K 1 0) = 0 at h1
    simp [QuaternionMatrices.quatI] at h1

theorem exists_fixed_perfect_even_conjAut [Finite K] (hK : ringChar K ≠ 2)
    (h4 : ∃ s : Finset K, s.card = 4) (hn : 3 ≤ n) (A : GL (Fin n) K)
    (hα : conjAut n K A ^ 2 = 1) :
    ∃ P : Subgroup (projectiveSL n K), Group.IsPerfect P ∧ Even (Nat.card P) ∧
      ∀ s ∈ P, conjAut n K A s = s := by
  have h1 : conjAut n K (A * A) * fieldAut n K 1 = 1 := by
    rw [map_one, mul_one, map_mul, ← sq, hα]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1
  by_cases hsq : ∃ μ : K, μ * μ = c
  · obtain ⟨μ, hμ⟩ := hsq
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hμ
      exact c.ne_zero hμ.symm
    set B := GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0)⁻¹ * A with hB
    have hcB : conjAut n K B = conjAut n K A := by rw [hB, map_mul, conjAut_scalar, one_mul]
    have hs : (Units.mk0 μ hμ0)⁻¹ * (Units.mk0 μ hμ0)⁻¹ * c = 1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_one]
      rw [← hμ]
      field_simp
    have hBB : B * B = 1 := by
      calc B * B = GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0)⁻¹ *
            GeneralLinearGroup.scalar (Fin n) (Units.mk0 μ hμ0)⁻¹ * (A * A) := by
            rw [hB, mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute]
            group
        _ = 1 := by rw [← hc, ← map_mul, ← map_mul, hs, map_one]
    obtain ⟨m, rfl⟩ : ∃ m, n = 2 + m := ⟨n - 2, by omega⟩
    obtain ⟨P, hP, he, hfix⟩ :=
      exists_fixed_perfect_even_conjAut_of_mul_self_eq_one hK h4 (by omega) B hBB
    exact ⟨P, hP, he, fun s hs => by rw [← hcB]; exact hfix s hs⟩
  · have hsq' : ∀ μ : K, μ * μ ≠ c := fun μ h => hsq ⟨μ, h⟩
    have hAA : (A : Matrix (Fin n) (Fin n) K) * A = (c : K) • 1 := by
      have := congrArg Units.val hc
      rw [Units.val_mul] at this
      rw [← this, smul_one_eq_diagonal]
      rfl
    exact exists_fixed_perfect_even_conjAut_of_mul_self_eq_nonsquare h4 hn A hsq' hAA

end LinearFlag

end CFSG.LocalAnalysis.ComponentInitial
