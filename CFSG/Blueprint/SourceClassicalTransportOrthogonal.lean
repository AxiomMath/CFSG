module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Blueprint.SourceQuadraticClassification
public import CFSG.LieType.Universal.IrreducibleQuadratic

public noncomputable section

namespace CFSG.Blueprint.EvenSource

open CFSG.Assembly.LowTwoRank Module Matrix QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadOdd quadMinus coe_quadPlus coe_quadOdd
  coe_quadMinus)

section OrthGroups

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι]
  [DecidableEq ι]

@[expose] def matrixOrthogonal (Q₀ : (ι → K) → K) : Subgroup (GL ι K) where
  carrier := {A | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v}
  mul_mem' {A B} hA hB v := by
    change Q₀ (((A * B : GL ι K) : Matrix ι ι K) *ᵥ v) = Q₀ v
    rw [Units.val_mul, ← mulVec_mulVec, hA, hB]
  one_mem' v := by
    change Q₀ (((1 : GL ι K) : Matrix ι ι K) *ᵥ v) = Q₀ v
    rw [Units.val_one, one_mulVec]
  inv_mem' {A} hA v := by
    change Q₀ (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = Q₀ v
    have h := hA (((A⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v)
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec] at h
    exact h.symm

theorem statedOmega_eq_commutator (Q₀ : (ι → K) → K) :
    StatedOmega Q₀ = ⁅matrixOrthogonal Q₀, matrixOrthogonal Q₀⁆ := by
  have h : Subgroup.closure {A : GL ι K | ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v} =
      matrixOrthogonal Q₀ :=
    Subgroup.closure_eq (matrixOrthogonal Q₀)
  rw [StatedOmega, h]

theorem equivFun_sourceGLEquiv_symm (b : Basis ι K V) (A : GL ι K) (x : V) :
    b.equivFun ((((sourceGLEquiv b).symm A : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) x) = (A : Matrix ι ι K) *ᵥ b.equivFun x := by
  have hg : LinearMap.toMatrix b b (((sourceGLEquiv b).symm A :
      LinearMap.GeneralLinearGroup K V) : Module.End K V) = A := by
    rw [← coe_sourceGLEquiv, MulEquiv.apply_symm_apply]
  rw [← hg]
  exact (LinearMap.toMatrix_mulVec_repr b b _ x).symm

theorem map_sourceOrthogonal (b : Basis ι K V) {Q : V → K} {Q₀ : (ι → K) → K}
    (hQ : ∀ x, Q x = Q₀ (b.equivFun x)) :
    (sourceOrthogonal Q).map (sourceGLEquiv b).toMonoidHom = matrixOrthogonal Q₀ := by
  ext A
  rw [Subgroup.mem_map_equiv]
  change (∀ x, Q ((((sourceGLEquiv b).symm A : LinearMap.GeneralLinearGroup K V) :
    Module.End K V) x) = Q x) ↔ ∀ v, Q₀ ((A : Matrix ι ι K) *ᵥ v) = Q₀ v
  simp only [hQ, equivFun_sourceGLEquiv_symm]
  refine ⟨fun H v => ?_, fun H x => H _⟩
  have := H (b.equivFun.symm v)
  rwa [LinearEquiv.apply_symm_apply] at this

theorem map_sourceOmega (b : Basis ι K V) {Q : V → K} {Q₀ : (ι → K) → K}
    (hQ : ∀ x, Q x = Q₀ (b.equivFun x)) :
    ⁅sourceOrthogonal Q, sourceOrthogonal Q⁆.map (sourceGLEquiv b).toMonoidHom =
      StatedOmega Q₀ := by
  rw [Subgroup.map_commutator, map_sourceOrthogonal b hQ, statedOmega_eq_commutator]

theorem sourceOrthogonal_smul (Q : V → K) {d : K} (hd : d ≠ 0) :
    sourceOrthogonal (fun x => d * Q x) = sourceOrthogonal Q := by
  ext g
  exact forall_congr' fun x => mul_right_inj' hd

end OrthGroups




theorem nonempty_statedProj_statedOmega_equiv {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q₀ : (ι → K) → K) :
    Nonempty (StatedProj (StatedOmega Q₀) ≃*
      (⁅sourceOrthogonal Q₀, sourceOrthogonal Q₀⁆ : Subgroup _) ⧸
        (sourceScalars K (ι → K)).subgroupOf ⁅sourceOrthogonal Q₀, sourceOrthogonal Q₀⁆) := by
  refine ⟨quotientInfCongr (sourceGLEquiv (Pi.basisFun K ι)).symm ?_ ?_⟩
  · rw [← map_sourceOmega (Pi.basisFun K ι) (Q₀ := Q₀) fun x => rfl, Subgroup.map_map]
    simp
  · rw [← map_sourceScalars_sourceGLEquiv (Pi.basisFun K ι), Subgroup.map_map]
    simp

theorem sourceClassicalModel_of_stated_POmegaPlus {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .POmegaPlus n p f) : SourceClassicalModel X .POmegaPlus n p f := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_statedProj_statedOmega_equiv (StatedQuadPlus n K)
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n K
  refine ⟨hadm, K, inferInstance, inferInstance, Fin n ⊕ Fin n → K, inferInstance, inferInstance,
    inferInstance, _, ⟨e.trans e'⟩, hK, ?_, StatedQuadPlus n K, ?_,
    sourceWittIndex_statedQuadPlus n K, rfl⟩
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, two_mul]
  · rw [← coe_quadPlus]
    exact isSourceQuadratic_of_nondegenerate _ hnd

theorem sourceClassicalModel_of_stated_POmegaOdd {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .POmegaOdd n p f) : SourceClassicalModel X .POmegaOdd n p f := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h
  obtain ⟨e'⟩ := nonempty_statedProj_statedOmega_equiv (StatedQuadOdd n K)
  have : Fact p.Prime := ⟨hadm.1⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
    exact hadm.2.2.2 ((Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_two).mp this)
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n K h2
  refine ⟨hadm, K, inferInstance, inferInstance, Fin n ⊕ Fin n ⊕ Unit → K, inferInstance,
    inferInstance, inferInstance, _, ⟨e.trans e'⟩, hK, ?_, StatedQuadOdd n K, ?_,
    sourceWittIndex_statedQuadOdd n K h2, rfl⟩
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  · rw [← coe_quadOdd]
    exact isSourceQuadratic_of_nondegenerate _ hnd

theorem sourceClassicalModel_of_stated_POmegaMinus {X : Type} [Group X] {n p f : ℕ}
    (h : StatedClassicalModel X .POmegaMinus n p f) :
    SourceClassicalModel X .POmegaMinus n p f := by
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  obtain ⟨e'⟩ := nonempty_statedProj_statedOmega_equiv (StatedQuadMinus n K b c)
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  refine ⟨hadm, K, inferInstance, inferInstance, Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
    inferInstance, inferInstance, inferInstance, _, ⟨e.trans e'⟩, hK, ?_, StatedQuadMinus n K b c,
    ?_, sourceWittIndex_statedQuadMinus n K hn hirr, rfl⟩
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  · rw [← coe_quadMinus]
    exact isSourceQuadratic_of_nondegenerate _ hnd

theorem stated_of_sourceClassicalModel_POmegaPlus {X : Type} [Group X] {n p f : ℕ}
    (h : SourceClassicalModel X .POmegaPlus n p f) : StatedClassicalModel X .POmegaPlus n p f := by
  obtain ⟨hadm, K, _, _, V, _, _, _, H, ⟨e⟩, hK, hV, Q, hQ, hw, rfl⟩ := h
  have hnd := hQ.nondegenerate (Or.inr ⟨n, by omega⟩)
  obtain ⟨iso⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hnd hV
    (hQ.isPlusType hV hw)
  let bs : Basis (Fin n ⊕ Fin n) K V := Basis.ofEquivFun iso.toLinearEquiv
  have hQb : ∀ x, Q x = StatedQuadPlus n K (bs.equivFun x) := fun x => by
    rw [Basis.equivFun_ofEquivFun, ← coe_quadPlus]
    exact (iso.map_app x).symm
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans (quotientInfCongr (sourceGLEquiv bs)
    (map_sourceOmega bs hQb) (map_sourceScalars_sourceGLEquiv bs))⟩⟩

theorem stated_of_sourceClassicalModel_POmegaOdd {X : Type} [Group X] {n p f : ℕ}
    (h : SourceClassicalModel X .POmegaOdd n p f) : StatedClassicalModel X .POmegaOdd n p f := by
  obtain ⟨hadm, K, _, _, V, _, _, _, H, ⟨e⟩, hK, hV, Q, hQ, -, rfl⟩ := h
  have : Fact p.Prime := ⟨hadm.1⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hadm.2.2.2
  have hnd := hQ.nondegenerate (Or.inl h2)
  obtain ⟨d, hd, ⟨iso⟩⟩ := CFSG.GroupTheory.WeirSylow.exists_smul_isometry_quadOdd h2
    hQ.toQuadraticForm hnd hV
  let bs : Basis (Fin n ⊕ Fin n ⊕ Unit) K V := Basis.ofEquivFun iso.toLinearEquiv
  have hQb : ∀ x, d * Q x = StatedQuadOdd n K (bs.equivFun x) := fun x => by
    rw [Basis.equivFun_ofEquivFun, ← coe_quadOdd]
    exact (iso.map_app x).symm
  have hH : ⁅sourceOrthogonal Q, sourceOrthogonal Q⁆.map (sourceGLEquiv bs).toMonoidHom =
      StatedOmega (StatedQuadOdd n K) := by
    rw [← map_sourceOmega bs (Q := fun x => d * Q x) hQb, sourceOrthogonal_smul Q hd]
  exact ⟨hadm, K, inferInstance, inferInstance, hK, ⟨e.trans (quotientInfCongr (sourceGLEquiv bs)
    hH (map_sourceScalars_sourceGLEquiv bs))⟩⟩

theorem nonempty_sourceOmega_equiv_minus {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {n : ℕ} (hn : 1 ≤ n)
    (hV : finrank K V = 2 * n) {Q : V → K} (hQ : IsSourceQuadratic Q)
    (hw : sourceWittIndex Q = n - 1) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty ((⁅sourceOrthogonal Q, sourceOrthogonal Q⁆ : Subgroup _) ⧸
        (sourceScalars K V).subgroupOf ⁅sourceOrthogonal Q, sourceOrthogonal Q⁆ ≃*
      StatedProj (StatedOmega (StatedQuadMinus n K b c))) := by
  have hnd := hQ.nondegenerate (Or.inr ⟨n, by omega⟩)
  obtain ⟨iso⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hnd hn hV
    (hQ.not_isPlusType hn hV hw) hirr
  let bs : Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K V := Basis.ofEquivFun iso.toLinearEquiv
  have hQb : ∀ x, Q x = StatedQuadMinus n K b c (bs.equivFun x) := fun x => by
    rw [Basis.equivFun_ofEquivFun, ← coe_quadMinus]
    exact (iso.map_app x).symm
  exact ⟨quotientInfCongr (sourceGLEquiv bs) (map_sourceOmega bs hQb)
    (map_sourceScalars_sourceGLEquiv bs)⟩

theorem stated_of_sourceClassicalModel_POmegaMinus {X : Type} [Group X] {n p f : ℕ}
    (h : SourceClassicalModel X .POmegaMinus n p f) :
    StatedClassicalModel X .POmegaMinus n p f := by
  obtain ⟨hadm, K, _, _, V, _, _, _, H, ⟨e⟩, hK, hV, Q, hQ, hw, rfl⟩ := h
  have hn : 1 ≤ n := by have := hadm.2.2; omega
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic K
  obtain ⟨e'⟩ := nonempty_sourceOmega_equiv_minus hn hV hQ hw hirr
  exact ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hirr, ⟨e.trans e'⟩⟩

theorem nonempty_statedOmegaMinus_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    {b c b' c' : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hirr' : ∀ s : K, s ^ 2 + b' * s + c' ≠ 0) :
    Nonempty (StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus n K b' c'))) := by
  obtain ⟨e₁⟩ := nonempty_statedProj_statedOmega_equiv (StatedQuadMinus n K b c)
  have hnd := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n K hirr
  have hQ : IsSourceQuadratic (StatedQuadMinus n K b c) := by
    rw [← coe_quadMinus]
    exact isSourceQuadratic_of_nondegenerate _ hnd
  obtain ⟨e₂⟩ := nonempty_sourceOmega_equiv_minus hn (by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
        Fintype.card_fin, Fintype.card_fin]
      omega) hQ (sourceWittIndex_statedQuadMinus n K hn hirr) hirr'
  exact ⟨e₁.trans e₂⟩

end CFSG.Blueprint.EvenSource
