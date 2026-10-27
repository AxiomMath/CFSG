module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33OCTools

public section

namespace CFSG.ComponentClassification.HarrisLit.L33.OC

open CFSG Subgroup Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type*} [Field K] {n : ℕ}

theorem exists_fixed_odd_conjAut_of_mul_self_eq_one {p : ℕ} [CharP K p] (hp : p.Prime)
    (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) (B : GL (Fin (2 + m)) K) (hB : B * B = 1) :
    ∃ T : Set (projectiveSL (2 + m) K),
      (∀ t ∈ T, conjAut (2 + m) K B t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have key : ∀ B' : GL (Fin (2 + m)) K, B' * B' = 1 →
      2 ≤ finrank K (LinearMap.ker (toLin' B'.val - 1)) →
      ∃ T : Set (projectiveSL (2 + m) K),
        (∀ t ∈ T, conjAut (2 + m) K B' t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
    intro B' hB' h2
    have hBm : (B' : Matrix (Fin (2 + m)) (Fin (2 + m)) K) * B' = 1 := by
      rw [← Units.val_mul, hB', Units.val_one]
    obtain ⟨b, hb⟩ := exists_eigenbasis hK hBm
    obtain ⟨P, D, hPD, hD⟩ := exists_gl_inv_mul_mul_eq_toMatrix b B'
    set k := finrank K (LinearMap.ker (toLin' (B' : Matrix (Fin (2 + m)) (Fin (2 + m)) K) - 1))
      with hk
    set d : Fin (2 + m) → K := fun i => if (i : ℕ) < k then 1 else -1 with hd
    have hDd : (D : Matrix (Fin (2 + m)) (Fin (2 + m)) K) = diagonal d := by
      rw [hD]
      ext a c
      rw [LinearMap.toMatrix_apply, toLin'_apply, hb c, map_smul, Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, diagonal_apply]
      by_cases hac : a = c
      · subst hac
        simp [hd]
      · simp [hac, Ne.symm hac]
    have hconj : conjAut (2 + m) K B' =
        conjAut (2 + m) K P * conjAut (2 + m) K D * (conjAut (2 + m) K P)⁻¹ := by
      rw [← hPD, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    refine exists_fixed_odd_conj hconj ?_
    refine exists_fixed_odd_of_hom hp hp2 LinearGroups.special_linear_elementary_generation
      (fun s hs => elementary_pow_char hs) ((blockGL K 2 m).comp SpecialLinearGroup.toGL)
      (conjAut (2 + m) K D) ?_ (QuaternionMatrices.slQuatI K)
      QuaternionMatrices.slQuatI_pow_four ?_
    · intro X hX
      refine (conjAut_proj D _).trans ?_
      congr 1
      apply Subtype.ext
      refine (coe_slConjugation D _).trans ?_
      change (D : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
          (blockGL K 2 m (SpecialLinearGroup.toGL X) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) *
          ((D⁻¹ : GL (Fin (2 + m)) K) : Matrix (Fin (2 + m)) (Fin (2 + m)) K) = _
      rw [hDd, ← blockGL_mul_diagonal_comm, Matrix.mul_assoc, ← hDd, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.mul_one]
      · rfl
      · intro i j
        have hi : ((finSumFinEquiv (Sum.inl i : Fin 2 ⊕ Fin m) : Fin (2 + m)) : ℕ) < k := by
          simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
          omega
        have hj : ((finSumFinEquiv (Sum.inl j : Fin 2 ⊕ Fin m) : Fin (2 + m)) : ℕ) < k := by
          simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
          omega
        simp only [hd, hi, hj, ↓reduceIte]
    · intro c
      refine blockGL_ne_scalar_of_ne_one hm (fun h1 => ?_) c
      have h1' : QuaternionMatrices.slQuatI K = 1 :=
        SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)
      have := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 0 0)
        h1'
      simp [QuaternionMatrices.slQuatI, QuaternionMatrices.quatI] at this
  by_cases h2 : 2 ≤ finrank K (LinearMap.ker (toLin' B.val - 1))
  · exact key B hB h2
  · have hBm : (B : Matrix (Fin (2 + m)) (Fin (2 + m)) K) * B = 1 := by
      rw [← Units.val_mul, hB, Units.val_one]
    have hsum := Submodule.finrank_add_eq_of_isCompl (isCompl_eigenspaces hK hBm)
    rw [finrank_fin_fun] at hsum
    have hker : LinearMap.ker (toLin' ((-B : GL (Fin (2 + m)) K) :
        Matrix (Fin (2 + m)) (Fin (2 + m)) K) - 1) =
          LinearMap.ker (toLin' (B : Matrix (Fin (2 + m)) (Fin (2 + m)) K) + 1) := by
      ext v
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, toLin'_apply,
        Module.End.one_apply, Units.val_neg, neg_mulVec]
      rw [← neg_add', neg_eq_zero]
    obtain ⟨T, hT, h2T⟩ := key (-B) (by rw [neg_mul_neg, hB]) (by rw [hker]; omega)
    exact ⟨T, fun t ht => ⟨by rw [← conjAut_neg]; exact (hT t ht).1, (hT t ht).2⟩, h2T⟩

theorem exists_fixed_odd_conjAut_of_mul_self_eq_nonsquare {p : ℕ} [CharP K p] (hp : p.Prime)
    (hp2 : p ≠ 2) (hn : 3 ≤ n) (A : GL (Fin n) K) {c : K} (hc : ∀ μ : K, μ * μ ≠ c)
    (hA : (A : Matrix (Fin n) (Fin n) K) * A = c • 1) :
    ∃ T : Set (projectiveSL n K), (∀ t ∈ T, conjAut n K A t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  classical
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
  refine exists_fixed_odd_of_hom hp hp2 LinearGroups.special_linear_elementary_generation
    (fun s hs => elementary_pow_char hs) ρ (conjAut n K A) ?_ (QuaternionMatrices.slQuatI K)
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

theorem exists_fixed_odd_conjAut [Finite K] {p : ℕ} [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 3 ≤ n) (A : GL (Fin n) K) (hα : conjAut n K A ^ 2 = 1) :
    ∃ T : Set (projectiveSL n K), (∀ t ∈ T, conjAut n K A t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
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
    obtain ⟨T, hT, h2T⟩ := exists_fixed_odd_conjAut_of_mul_self_eq_one hp hp2 (by omega) B hBB
    exact ⟨T, fun t ht => ⟨by rw [← hcB]; exact (hT t ht).1, (hT t ht).2⟩, h2T⟩
  · have hsq' : ∀ μ : K, μ * μ ≠ c := fun μ h => hsq ⟨μ, h⟩
    have hAA : (A : Matrix (Fin n) (Fin n) K) * A = (c : K) • 1 := by
      have := congrArg Units.val hc
      rw [Units.val_mul] at this
      rw [← this, smul_one_eq_diagonal]
      rfl
    exact exists_fixed_odd_conjAut_of_mul_self_eq_nonsquare hp hp2 hn A hsq' hAA

end CFSG.ComponentClassification.HarrisLit.L33.OC
