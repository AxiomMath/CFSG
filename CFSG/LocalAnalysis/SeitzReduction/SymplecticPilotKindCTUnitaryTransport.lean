module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryBlock

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

section Transport

variable {F F' : Type*} [Field F] [Field F'] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
  [DecidableEq ι₁] [DecidableEq ι₂]

@[expose] def transportMat (θ : F →+* F') (τ : ι₁ ≃ ι₂) (A : Matrix ι₂ ι₂ F) : Matrix ι₁ ι₁ F' :=
  (A.submatrix τ τ).map θ

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem transportMat_mul (θ : F →+* F') (τ : ι₁ ≃ ι₂) (A B : Matrix ι₂ ι₂ F) :
    transportMat θ τ (A * B) = transportMat θ τ A * transportMat θ τ B := by
  rw [transportMat, transportMat, transportMat, ← Matrix.map_mul, submatrix_mul_equiv]

omit [Fintype ι₁] [Fintype ι₂] in
theorem transportMat_one (θ : F →+* F') (τ : ι₁ ≃ ι₂) :
    transportMat θ τ (1 : Matrix ι₂ ι₂ F) = 1 := by
  rw [transportMat, submatrix_one_equiv, Matrix.map_one _ (map_zero θ) (map_one θ)]

theorem det_transportMat (θ : F →+* F') (τ : ι₁ ≃ ι₂) (A : Matrix ι₂ ι₂ F) :
    (transportMat θ τ A).det = θ A.det := by
  rw [transportMat, ← det_submatrix_equiv_self τ A, RingHom.map_det]
  rfl

omit [DecidableEq ι₁] [DecidableEq ι₂] in
theorem transportMat_isometry (θ : F →+* F') (τ : ι₁ ≃ ι₂) {σ : F →+* F} {σ' : F' →+* F'}
    (hθ : ∀ c, θ (σ c) = σ' (θ c)) {A C : Matrix ι₂ ι₂ F} (hA : (A.map σ)ᵀ * C * A = C) :
    ((transportMat θ τ A).map σ')ᵀ * transportMat θ τ C * transportMat θ τ A =
      transportMat θ τ C := by
  have h1 : (transportMat θ τ A).map σ' = transportMat θ τ (A.map σ) := by
    ext i j
    simp [transportMat, hθ]
  have h2 : (transportMat θ τ (A.map σ))ᵀ = transportMat θ τ (A.map σ)ᵀ := by
    ext i j
    simp [transportMat]
  rw [h1, h2, ← transportMat_mul, ← transportMat_mul, hA]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
theorem transportMat_symm_transportMat (θ : F ≃+* F') (τ : ι₁ ≃ ι₂) (A : Matrix ι₂ ι₂ F) :
    transportMat (θ.symm : F' →+* F) τ.symm (transportMat (θ : F →+* F') τ A) = A := by
  ext i j
  simp [transportMat]

omit [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] in
theorem transportMat_transportMat_symm (θ : F ≃+* F') (τ : ι₁ ≃ ι₂) (A : Matrix ι₁ ι₁ F') :
    transportMat (θ : F →+* F') τ (transportMat (θ.symm : F' →+* F) τ.symm A) = A := by
  ext i j
  simp [transportMat]

end Transport

section Gram

variable {m : ℕ}

@[expose] noncomputable def ctuGramIdx (m : ℕ) : Fin (2 * m) ≃ Fin (2 * m + 0) :=
  (spModelIdx m).symm.trans ((Equiv.sumEmpty (Fin m ⊕ Fin m) (Fin 0)).symm.trans (ctuCoord m 0))

theorem ctuGramIdx_spModelIdx (u : Fin m ⊕ Fin m) :
    ctuGramIdx m (spModelIdx m u) = ctuCoord m 0 (Sum.inl u) := by
  simp [ctuGramIdx]

theorem antidiag_submatrix_ctuGramIdx {F : Type} [Field F] :
    (antidiag (2 * m + 0) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F).submatrix
      (ctuGramIdx m) (ctuGramIdx m) = blockSwapJ (2 * m) m := by
  ext i j
  obtain ⟨u, rfl⟩ := (spModelIdx m).surjective i
  obtain ⟨v, rfl⟩ := (spModelIdx m).surjective j
  rw [submatrix_apply, ctuGramIdx_spModelIdx, ctuGramIdx_spModelIdx, antidiag_ctuCoord (by omega),
    blockSwapJ, of_apply]
  have hu := fun (w : Fin m) => w.2
  rcases u with u | u <;> rcases v with v | v <;>
    simp only [ctuPar_inl, par_inl, par_inr, Sum.inl.injEq, reduceCtorEq, spModelIdx_inl_val,
      spModelIdx_inr_val, Sum.inr.injEq, Fin.ext_iff] <;>
    split_ifs <;> first | rfl | (exfalso; have := hu u; have := hu v; omega)

end Gram

theorem exists_ringEquiv_comp_eq {K F F' : Type*} [Field K] [Field F] [Field F'] [Finite F]
    [Finite F'] (ι : K →+* F) (ι' : K →+* F') (h : Nat.card F = Nat.card F') :
    ∃ θ : F ≃+* F', ∀ c, θ (ι c) = ι' c := by
  let _ : Algebra K F := ι.toAlgebra
  let _ : Algebra K F' := ι'.toAlgebra
  have : Finite K := Finite.of_injective ι ι.injective
  have : Module.Finite K F := Module.Finite.of_finite
  have : Module.Finite K F' := Module.Finite.of_finite
  have h1 := Module.natCard_eq_pow_finrank (K := K) (V := F)
  have h2 := Module.natCard_eq_pow_finrank (K := K) (V := F')
  have hK : 2 ≤ Nat.card K := Finite.one_lt_card
  have hfr : Module.finrank K F = Module.finrank K F' :=
    Nat.pow_right_injective hK (by beta_reduce; rw [← h1, ← h2, h])
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := F) (L := F')
    (dvd_of_eq hfr)
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hbij : Function.Bijective φ := hinj.bijective_of_nat_card_le h.ge
  exact ⟨RingEquiv.ofBijective φ hbij, fun c => φ.commutes c⟩

section GramEquiv

variable {f m : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {K' : Type} [Field K']
  (h : UnitaryFieldData 2 f K') {C₀ : GL (Fin (2 * m)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m)
  (θ : F ≃+* K')

omit [Finite F] [CharP F 2] in
include hC₀ in
theorem transportMat_antidiag :
    transportMat (θ : F →+* K') (ctuGramIdx m)
      (antidiag (2 * m + 0) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F) =
        (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') := by
  rw [transportMat, antidiag_submatrix_ctuGramIdx, hC₀]
  ext i j
  simp only [map_apply, blockSwapJ, of_apply]
  split_ifs <;> simp

theorem ringEquiv_unitaryInvolution (c : F) :
    (θ : F →+* K') (unitaryInvolution F 2 f c) = h.bar ((θ : F →+* K') c) := by
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply, map_pow]

theorem ringEquiv_symm_bar (c : K') :
    (θ.symm : K' →+* F) (h.bar c) =
      (unitaryInvolution F 2 f : F →+* F) ((θ.symm : K' →+* F) c) := by
  change θ.symm (h.bar c) = unitaryInvolution F 2 f (θ.symm c)
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, h.bar_apply, map_pow]

include hC₀ in
theorem transportMat_mem_gramSU (y : SU (unitaryInvolution F 2 f) (2 * m + 0)) :
    ((transportMat (θ : F →+* K') (ctuGramIdx m)
        ((y : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F)).map
          h.bar)ᵀ * (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') *
      transportMat (θ : F →+* K') (ctuGramIdx m)
        ((y : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F) =
        (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') ∧
      (transportMat (θ : F →+* K') (ctuGramIdx m)
        ((y : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F)).det = 1 := by
  refine ⟨?_, by rw [det_transportMat, y.2.1, map_one]⟩
  rw [← transportMat_antidiag hC₀ θ]
  exact transportMat_isometry _ _ (ringEquiv_unitaryInvolution h θ) y.2.2

@[expose] noncomputable def ctuGramHom :
    SU (unitaryInvolution F 2 f) (2 * m + 0) →*
      gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') where
  toFun y := ⟨⟨transportMat (θ : F →+* K') (ctuGramIdx m)
      ((y : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F),
      transportMat (θ : F →+* K') (ctuGramIdx m)
        ((y⁻¹ : SU (unitaryInvolution F 2 f) (2 * m + 0)) : GL (Fin (2 * m + 0)) F),
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one],
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one]⟩,
    transportMat_mem_gramSU h hC₀ θ y⟩
  map_one' := Subtype.ext (Units.ext (by
    change transportMat (θ : F →+* K') (ctuGramIdx m) (1 : Matrix (Fin (2 * m + 0))
      (Fin (2 * m + 0)) F) = 1
    rw [transportMat_one]))
  map_mul' y z := Subtype.ext (Units.ext (by
    change transportMat (θ : F →+* K') (ctuGramIdx m)
      (((y : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F) *
        ((z : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F)) = _
    rw [transportMat_mul]
    rfl))

theorem coe_ctuGramHom (y : SU (unitaryInvolution F 2 f) (2 * m + 0)) :
    (((ctuGramHom h hC₀ θ y : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K')) :
      GL (Fin (2 * m)) K') : Matrix (Fin (2 * m)) (Fin (2 * m)) K') =
        transportMat (θ : F →+* K') (ctuGramIdx m)
          ((y : GL (Fin (2 * m + 0)) F) : Matrix (Fin (2 * m + 0)) (Fin (2 * m + 0)) F) := rfl

theorem ctuGramHom_bijective : Function.Bijective (ctuGramHom h hC₀ θ) := by
  constructor
  · intro y z hyz
    have h1 := congrArg (fun g : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') =>
      transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
        ((g : GL (Fin (2 * m)) K') : Matrix (Fin (2 * m)) (Fin (2 * m)) K')) hyz
    simp only [coe_ctuGramHom, transportMat_symm_transportMat] at h1
    exact Subtype.ext (Units.ext h1)
  · intro g
    have hC' : transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
        (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = antidiag (2 * m + 0) := by
      rw [← transportMat_antidiag hC₀ θ, transportMat_symm_transportMat]
    have hiso : ∀ g' : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K'),
        conjTr (unitaryInvolution F 2 f) (transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
          ((g' : GL (Fin (2 * m)) K') : Matrix (Fin (2 * m)) (Fin (2 * m)) K')) *
          antidiag (2 * m + 0) * transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
            ((g' : GL (Fin (2 * m)) K') : Matrix (Fin (2 * m)) (Fin (2 * m)) K') =
          antidiag (2 * m + 0) := by
      intro g'
      rw [← hC']
      exact transportMat_isometry _ _ (ringEquiv_symm_bar h θ) g'.2.1
    refine ⟨⟨⟨transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
        ((g : GL (Fin (2 * m)) K') : Matrix (Fin (2 * m)) (Fin (2 * m)) K'),
      transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
        ((g⁻¹ : gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K')) : GL (Fin (2 * m)) K'),
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one],
      by rw [← transportMat_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
        Subgroup.coe_one, Units.val_one, transportMat_one]⟩,
      by
        change (transportMat (θ.symm : K' →+* F) (ctuGramIdx m).symm
          ((g : GL (Fin (2 * m)) K') : Matrix (Fin (2 * m)) (Fin (2 * m)) K')).det = 1
        rw [det_transportMat, g.2.2, map_one],
      hiso g⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [coe_ctuGramHom]
    exact transportMat_transportMat_symm θ (ctuGramIdx m) _

@[expose] noncomputable def ctuGramEquiv :
    SU (unitaryInvolution F 2 f) (2 * m + 0) ≃*
      gramSU h (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') :=
  MulEquiv.ofBijective (ctuGramHom h hC₀ θ) (ctuGramHom_bijective h hC₀ θ)

theorem ctuGramEquiv_apply (y : SU (unitaryInvolution F 2 f) (2 * m + 0)) :
    ctuGramEquiv h hC₀ θ y = ctuGramHom h hC₀ θ y := rfl

theorem ctuGramEquiv_ctuEmbed {K₀ : Type} [Field K₀] [CharP K₀ 2] [CharP h.fixedField 2]
    {ι : K₀ →+* F} (hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c) (ι' : K₀ ≃+* h.fixedField)
    (hθι : ∀ c, θ (ι c) = (ι' c : K')) (x : StatedSp m K₀) :
    ctuGramEquiv h hC₀ θ (ctuEmbed 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι x) =
      uModelSU h hC₀ (F4Pilot.statedSpMap (ι' : K₀ →+* h.fixedField) m x) := by
  apply Subtype.ext
  apply Units.ext
  rw [ctuGramEquiv_apply, coe_ctuGramHom, coe_uModelSU, coe_ctuEmbed, coe_spModelSL]
  ext i j
  obtain ⟨u, rfl⟩ := (spModelIdx m).surjective i
  obtain ⟨v, rfl⟩ := (spModelIdx m).surjective j
  rw [transportMat, map_apply, submatrix_apply, ctuGramIdx_spModelIdx, ctuGramIdx_spModelIdx,
    ctuEmbedMat_apply, fromBlocks_apply₁₁, map_apply, map_apply, submatrix_apply,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, F4Pilot.coe_statedSpMap]
  change θ (ι _) = _
  rw [hθι]
  rfl

end GramEquiv

section Param

variable {G : Type} [Group G] {L : Subgroup G} {K₀ : Type} [Field K₀] [CharP K₀ 2] {m f : ℕ}
  {F : Type} [Field F] [Finite F] [CharP F 2] {ι : K₀ →+* F}
  {hι : ∀ c, unitaryInvolution F 2 f (ι c) = ι c} {e : L ≃* StatedSp (m + 1) K₀} {t : G}
  {k : Fin (m + 1)} {K' : Type} [Field K'] {h : UnitaryFieldData 2 f K'} [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * m)) K'} {hC : IsPrimeFormGram C₀}
  {hC₀ : (C₀ : Matrix (Fin (2 * m)) (Fin (2 * m)) K') = blockSwapJ (2 * m) m}
  {ι' : K₀ ≃+* h.fixedField}

theorem mem_center_of_mulEquiv_mem_center {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) {x : A}
    (hx : ψ x ∈ center B) : x ∈ center A := by
  rw [mem_center_iff] at hx ⊢
  intro y
  apply ψ.injective
  rw [map_mul, map_mul]
  exact hx (ψ y)

@[expose] noncomputable def ctuParamOfUnitary (θ : F ≃+* K') (hθι : ∀ c, θ (ι c) = (ι' c : K'))
    (P : UnitaryNeighbourParam h e t k hC hC₀ ι') :
    CtuParam 0 (Nat.zero_le 1) (unitaryInvolution F 2 f) ι hι e k where
  Φ := P.Φ.comp (((ctuBlockEquiv (unitaryInvolution F 2 f) (Nat.zero_le 1) k).trans
    (ctuGramEquiv h hC₀ θ)).toMonoidHom)
  ker_le := by
    intro x hx
    exact mem_center_of_mulEquiv_mem_center _ (P.ker_le hx)
  range_eq := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map, P.range_eq]
  N1 y hy := by
    rw [spBlock_compl_singleton] at hy
    obtain ⟨x, hx⟩ := (complSpEquiv k).surjective ⟨y, hy⟩
    have hyx : y = ((complSpEquiv k x : complSp K₀ k) : StatedSp (m + 1) K₀) := by rw [hx]
    subst hyx
    change P.Φ (ctuGramEquiv h hC₀ θ (ctuBlockEquiv (unitaryInvolution F 2 f) (Nat.zero_le 1) k
      ⟨_, _⟩)) = _
    rw [ctuBlockEquiv_ctuEmbed, ctuGramEquiv_ctuEmbed h hC₀ θ hι ι' hθι, P.N1 x]

end Param

theorem spUnitaryEvenCtuParamInput_holds : SpUnitaryEvenCtuParamInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt hP
  obtain ⟨K₀', _, h₀, _, -, -, -, ι₀, -⟩ := hP 0
  have : Finite K₀' := h₀.finite
  have : CharP K₀' 2 := h₀.charP
  have hF : Nat.card K₀' = (2 ^ f) ^ 2 := by rw [h₀.card, ← pow_mul, mul_comm]
  set ι : K →+* K₀' := h₀.fixedField.subtype.comp (ι₀ : K →+* h₀.fixedField) with hιdef
  have hι : ∀ c, unitaryInvolution K₀' 2 f (ι c) = ι c := fun c => by
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, ← h₀.bar_apply]
    exact (h₀.mem_fixedField.1 (ι₀ c).2)
  refine ⟨K₀', inferInstance, inferInstance, inferInstance, hF, ι, hι, fun k => ?_⟩
  obtain ⟨K', _, h, _, C₀, hC, hC₀, ι', ⟨P⟩⟩ := hP k
  have : Finite K' := h.finite
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_comp_eq ι
    (h.fixedField.subtype.comp (ι' : K →+* h.fixedField))
    (by rw [hF, h.card, ← pow_mul, mul_comm])
  exact ⟨ctuParamOfUnitary θ hθ P⟩

theorem spUnitaryParamCTInput_of_align (hA : CtuAlignInput 0 (Nat.zero_le 1))
    (h4 : SpUnitaryParamCTFourInput) : SpUnitaryParamCTInput :=
  spUnitaryParamCTInput_of_inputs spUnitaryEvenCtuParamInput_holds hA h4

end CFSG.SeitzReduction.SymplecticPilot
