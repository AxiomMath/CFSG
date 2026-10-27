module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PUf
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GH74.Orders.LieType

public section

namespace CFSG.ComponentClassification.GSThmB.P211

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ComponentClassification.CatFactsL4U4 UnitaryOut UnitaryConj HBlocks
  ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank CFSG.LinearGroups
  CFSG.ComponentClassification.CatalogueBAlternatingIsometry PSpL StabU

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

include h in
theorem exists_simple_of_alt_U4 (hp2 : p ≠ 2) {A : GL (Fin 4) K}
    (hAu : uStar h (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1)
    (hAA : (A : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K).map h.bar = -1)
    (ψ : unitarySU p f K 4 →* unitarySU p f K 4)
    (hψv : ∀ g, ((ψ g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (A : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar *
        (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) :
    IsSimpleGroup ((ψ.eqLocus (MonoidHom.id _)).map (QuotientGroup.mk' (scal p f K))) ∧
      Nat.card ((ψ.eqLocus (MonoidHom.id _)).map (QuotientGroup.mk' (scal p f K))) =
        Open.ordBC 2 (p ^ f) := by
  classical
  have : Finite K := h.finite
  obtain ⟨Rm, t, l, ht0, ht, hl0, hR1, hR2⟩ := exists_real_frame_alt h hp2 hAu hAA
  have hω : (omg : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    rw [Matrix.det_succ_row_zero]
    simp [omg, Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  have hRdet : Rm.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hR1
    rw [det_mul, h0, mul_zero, det_smul, Fintype.card_fin, hω, mul_one] at this
    exact pow_ne_zero 4 ht0 this.symm
  set R : GL (Fin 4) K := GeneralLinearGroup.mkOfDetNeZero Rm hRdet with hRdef
  have hRv : (R : Matrix (Fin 4) (Fin 4) K) = Rm := GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hRR : (R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hRiR : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hR1' : uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K) =
      t • omg := by rw [hRv]; exact hR1
  set ι₀ : StatedSp 2 h.fixedField →* GL (Fin 4) K :=
    (MulAut.conj R).toMonoidHom.comp ((glIncl h).comp (spGL h.fixedField)) with hι₀
  have hι₀v : ∀ M, ((ι₀ M : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) *
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun M => by
    rw [hι₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul,
      Units.val_mul, MonoidHom.comp_apply]
  have hmem : ∀ M, ι₀ M ∈ unitarySU p f K 4 := fun M => conj_glIncl_mem h hR1' M
  set ι : StatedSp 2 h.fixedField →* unitarySU p f K 4 := ι₀.codRestrict _ hmem with hι
  have hιv : ∀ M, (((ι M : unitarySU p f K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (R : Matrix (Fin 4) (Fin 4) K) *
        ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := fun M => hι₀v M
  set φ : StatedSp 2 h.fixedField →* StatedProj (StatedSU 4 (p ^ f) K) :=
    (QuotientGroup.mk' (scal p f K)).comp ι with hφ
  have hA1 : (A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar =
      l⁻¹ • (R : Matrix (Fin 4) (Fin 4) K) := by
    rw [hRv]
    conv_rhs => rw [← hR2]
    rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hAA' : (A : Matrix (Fin 4) (Fin 4) K) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hAiA : (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hRb : (R : Matrix (Fin 4) (Fin 4) K).map h.bar *
      (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar = 1 := by
    rw [← Matrix.map_mul, hRR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hB : (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
      l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
    calc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        (l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (l⁻¹ • (R : Matrix (Fin 4) (Fin 4) K)) *
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hRiR, smul_smul, mul_inv_cancel₀ hl0, one_smul,
            Matrix.one_mul]
      _ = (l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * ((A : Matrix (Fin 4) (Fin 4) K) *
          ((R : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar) *
            (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [← hA1]
          simp only [Matrix.mul_assoc]
      _ = l • (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) := by rw [hRb, Matrix.mul_one, hAA', Matrix.mul_one]
  have hle1 : ι.range ≤ ψ.eqLocus (MonoidHom.id _) := by
    rintro _ ⟨M, rfl⟩
    change ψ (ι M) = ι M
    apply ext_val
    rw [hψv, hιv, Matrix.map_mul, Matrix.map_mul, map_bar_glIncl]
    calc (A : Matrix (Fin 4) (Fin 4) K) * ((R : Matrix (Fin 4) (Fin 4) K).map h.bar *
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar) * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        ((A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar) *
          ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hA1, hB, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
            mul_inv_cancel₀ hl0, one_smul]
  have hle2 : ψ.eqLocus (MonoidHom.id _) ≤ ι.range := by
    intro g hg
    change ψ g = g at hg
    set G := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hGdef
    have hgG : (A : Matrix (Fin 4) (Fin 4) K) * G.map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        G := by
      rw [← hψv, hg]
    have hGb : G.map h.bar = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * A := by
      calc G.map h.bar = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((A : Matrix (Fin 4) (Fin 4) K) *
            G.map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) * A := by
            simp only [← Matrix.mul_assoc]
            rw [hAiA, Matrix.one_mul, Matrix.mul_assoc, hAiA, Matrix.mul_one]
        _ = (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * A := by rw [hgG]
    obtain ⟨hGdet, hGu⟩ := (mem_unitarySU_iff h).1 g.2
    set X := (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * R with hXdef
    have hXb : X.map h.bar = X := by
      rw [hXdef, Matrix.map_mul, Matrix.map_mul, hGb]
      calc (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar *
            ((↑A⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * A) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar =
          ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).map h.bar * (↑A⁻¹ : Matrix (Fin 4) (Fin 4) K)) * G *
            ((A : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K).map h.bar) := by
            simp only [Matrix.mul_assoc]
        _ = (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * R := by
            rw [hB, hA1, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
              inv_mul_cancel₀ hl0, one_smul]
    have hXmem : ∀ i j, X i j ∈ h.fixedField := fun i j =>
      (h.mem_fixedField).2 (by
        have := congrFun (congrFun hXb i) j
        rwa [Matrix.map_apply] at this)
    set X' : Matrix (Fin 4) (Fin 4) h.fixedField := Matrix.of fun i j => ⟨X i j, hXmem i j⟩
      with hX'def
    have hX'X : X'.map h.fixedField.subtype = X := by
      ext i j
      rfl
    have hXdet : X.det = 1 := by
      rw [hXdef, det_mul, det_mul, mul_comm ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K).det), mul_assoc,
        ← det_mul, hRiR, det_one, mul_one]
      exact hGdet
    have hX'det : X'.det = 1 := by
      apply h.fixedField.subtype.injective
      rw [map_one, RingHom.map_det,
        show h.fixedField.subtype.mapMatrix X' = X'.map h.fixedField.subtype from rfl, hX'X,
        hXdet]
    have hRi : uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * uStar h (R : Matrix (Fin 4) (Fin 4) K)
        = 1 := by rw [← uStar_mul, hRR, uStar_one]
    have hXu : uStar h X * (t • omg) * X = t • omg := by
      rw [← hR1', hXdef, uStar_mul, uStar_mul]
      calc uStar h (R : Matrix (Fin 4) (Fin 4) K) * (uStar h G *
            uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
            (uStar h (R : Matrix (Fin 4) (Fin 4) K) * (R : Matrix (Fin 4) (Fin 4) K)) *
            ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * R) =
          uStar h (R : Matrix (Fin 4) (Fin 4) K) * uStar h G *
            (uStar h (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) *
              uStar h (R : Matrix (Fin 4) (Fin 4) K)) *
            ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * G * R := by
            simp only [Matrix.mul_assoc]
        _ = uStar h (R : Matrix (Fin 4) (Fin 4) K) * R := by
            have hGu' : uStar h G * G = 1 := hGu
            rw [hRi, hRR, Matrix.mul_one, Matrix.mul_one]
            simp only [Matrix.mul_assoc] at hGu' ⊢
            rw [← Matrix.mul_assoc (uStar h G), hGu', Matrix.one_mul]
    have hXs : Xᵀ * omg * X = omg := by
      have hXt : uStar h X = Xᵀ := by rw [uStar, hXb]
      rw [Matrix.mul_smul, Matrix.smul_mul, hXt] at hXu
      exact smul_right_injective _ ht0 hXu
    have hX's : X'ᵀ * omg * X' = omg := by
      apply Matrix.map_injective h.fixedField.subtype.injective
      dsimp only
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, omg_map, hX'X]
      exact hXs
    set N := (reindex (finSumFinEquiv (m := 2) (n := 2))
      (finSumFinEquiv (m := 2) (n := 2))).symm X' with hN
    have hNX : reindex finSumFinEquiv finSumFinEquiv N = X' := Equiv.apply_symm_apply _ _
    have hr : ∀ Y Z : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField,
        reindex finSumFinEquiv finSumFinEquiv (Y * Z) =
          reindex finSumFinEquiv finSumFinEquiv Y * reindex finSumFinEquiv finSumFinEquiv Z :=
      fun Y Z => (Matrix.reindexAlgEquiv h.fixedField h.fixedField finSumFinEquiv).map_mul Y Z
    have hJ : Nᵀ * fromBlocks 0 1 (-1) 0 * N = fromBlocks 0 1 (-1) 0 := by
      apply (reindex finSumFinEquiv finSumFinEquiv).injective
      rw [hr, hr, ← transpose_reindex, hNX, reindex_gram, hX's]
    have hNdet : N.det ≠ 0 := by
      have h1 : N.det = X'.det := by rw [← hNX, det_reindex_self]
      rw [h1, hX'det]
      exact one_ne_zero
    set N' : GL (Fin 2 ⊕ Fin 2) h.fixedField := GeneralLinearGroup.mkOfDetNeZero N hNdet with hN'
    have hN'mem : N' ∈ StatedSp 2 h.fixedField := by
      refine Subgroup.subset_closure ?_
      show (N' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)ᵀ * fromBlocks 0 1 (-1) 0 *
        (N' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField) = fromBlocks 0 1 (-1) 0
      rw [hN', GeneralLinearGroup.val_mkOfDetNeZero]
      exact hJ
    refine ⟨⟨N', hN'mem⟩, ext_val ?_⟩
    rw [hιv, coe_glIncl, coe_spGL]
    change (R : Matrix (Fin 4) (Fin 4) K) * (reindex finSumFinEquiv finSumFinEquiv
      ((N' : GL (Fin 2 ⊕ Fin 2) h.fixedField) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) h.fixedField)).map h.fixedField.subtype *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) = G
    rw [hN', GeneralLinearGroup.val_mkOfDetNeZero N hNdet, hNX, hX'X, hXdef]
    calc (R : Matrix (Fin 4) (Fin 4) K) * ((↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * G * R) *
          (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) =
        ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * G *
          ((R : Matrix (Fin 4) (Fin 4) K) * (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          simp only [Matrix.mul_assoc]
      _ = G := by rw [hRR, Matrix.one_mul, Matrix.mul_one]
  have hfixeq : ψ.eqLocus (MonoidHom.id _) = ι.range := le_antisymm hle2 hle1
  have hSφ : (ψ.eqLocus (MonoidHom.id _)).map (QuotientGroup.mk' (scal p f K)) = φ.range := by
    rw [hfixeq, hφ, MonoidHom.range_comp]
  have hker : φ.ker = (StatedScalars (Fin 2 ⊕ Fin 2) h.fixedField).subgroupOf
      (StatedSp 2 h.fixedField) := by
    ext M
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    constructor
    · intro hM
      obtain ⟨c, hc⟩ := hM
      have hc' := congrArg (fun Y : GL (Fin 4) K => (Y : Matrix (Fin 4) (Fin 4) K)) hc
      simp only [GeneralLinearGroup.coe_scalar] at hc'
      change _ = ((ι M : unitarySU p f K 4) : GL (Fin 4) K).val at hc'
      rw [hιv] at hc'
      have hX : ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
          (c : K) • 1 := by
        calc ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
            (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K) * ((R : Matrix (Fin 4) (Fin 4) K) *
              ((glIncl h (spGL h.fixedField M) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
                (↑R⁻¹ : Matrix (Fin 4) (Fin 4) K)) * (R : Matrix (Fin 4) (Fin 4) K) := by
              simp only [← Matrix.mul_assoc]
              rw [hRiR, Matrix.one_mul, Matrix.mul_assoc, hRiR, Matrix.mul_one]
          _ = (c : K) • 1 := by
              rw [← hc', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
                Matrix.mul_one, Matrix.smul_mul, hRiR]
      set c' : h.fixedField := ((spGL h.fixedField M : GL (Fin 4) h.fixedField) :
        Matrix (Fin 4) (Fin 4) h.fixedField) 0 0 with hc'def
      apply mem_statedScalars_of_spGL (c := c')
      ext i j
      have e1 := congrFun (congrFun hX i) j
      have e0 := congrFun (congrFun hX 0) 0
      rw [coe_glIncl, Matrix.map_apply] at e1 e0
      simp only [Subfield.coe_subtype, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
        mul_one] at e1 e0
      rw [e1, Matrix.smul_apply, smul_eq_mul, Subfield.coe_mul, hc'def, e0]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    · intro hM
      obtain ⟨c, hc⟩ := spGL_of_mem_statedScalars hM
      refine ⟨Units.map h.fixedField.subtype.toMonoidHom c, ?_⟩
      apply Units.ext
      rw [GeneralLinearGroup.coe_scalar]
      change _ = ((ι M : unitarySU p f K 4) : GL (Fin 4) K).val
      rw [hιv, coe_glIncl, hc]
      have : ((c : h.fixedField) • (1 : Matrix (Fin 4) (Fin 4) h.fixedField)).map
          h.fixedField.subtype = ((c : h.fixedField) : K) • 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRR, Matrix.scalar_apply,
        Matrix.smul_one_eq_diagonal]
      rfl
  have hq2 : p ^ f ≠ 2 := by
    have := h.prime.two_le
    have h3 : 3 ≤ p := by omega
    have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
    omega
  rw [hSφ]
  refine ⟨?_, GH74.card_of_lieModel_PSp (by norm_num) hp2
    (lieModel_range_of_ker h.prime h.one_le h.card_fixedField hq2 φ hker)⟩
  have hcond : (Infinite h.fixedField ∨ 4 ≤ Nat.card h.fixedField) ∨
      (Nat.card h.fixedField = 3 ∧ 2 ≤ 2) ∨ (Nat.card h.fixedField = 2 ∧ 3 ≤ 2) := by
    rw [h.card_fixedField]
    rcases Nat.lt_or_ge (p ^ f) 4 with h4 | h4
    · have := h.prime.two_le
      have : p ≤ p ^ f := Nat.le_self_pow (by have := h.one_le; omega) p
      exact Or.inr (Or.inl ⟨by omega, le_rfl⟩)
    · exact Or.inl (Or.inr h4)
  have := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp h.fixedField 2
    (by norm_num) hcond
  exact ((QuotientGroup.quotientKerEquivRange φ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).isSimpleGroup

end CFSG.ComponentClassification.GSThmB.P211
