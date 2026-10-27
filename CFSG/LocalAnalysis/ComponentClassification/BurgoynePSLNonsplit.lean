module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLQuad

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag Module Polynomial
open scoped MatrixGroups

variable {K : Type} [Field K] {l : K} {m : ℕ}

@[expose] def blockGL (l : K) (m : ℕ) : GL (Fin m) (QuadExt l) →* GL (Fin (m * 2)) K :=
  Units.map (blockRep l m).toRingHom.toMonoidHom

theorem coe_blockGL (Y : GL (Fin m) (QuadExt l)) :
    ((blockGL l m Y : GL (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
      blockRep l m (Y : Matrix (Fin m) (Fin m) (QuadExt l)) :=
  rfl

@[expose] def blockDet (l : K) (m : ℕ) : Matrix.SpecialLinearGroup (Fin m) (QuadExt l) →* Kˣ :=
  GeneralLinearGroup.det.comp ((blockGL l m).comp Matrix.SpecialLinearGroup.toGL)

theorem isQuasisimple_SL_quadExt [Finite K] (hl : ¬ IsSquare l) (hm : 2 ≤ m) :
    @IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) (QuadExt l)) (by
      have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
      infer_instance) := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  have : Module.Finite K (QuadExt l) := (AdjoinRoot.powerBasis' (monic_X_pow_sub_C l
    two_ne_zero)).finite
  have : Finite (QuadExt l) := Module.finite_of_finite K
  have hcard : 4 ≤ Nat.card (QuadExt l) := by
    have := Fintype.ofFinite K
    have := Fintype.ofFinite (QuadExt l)
    have h1 := Module.card_eq_pow_finrank (K := K) (V := QuadExt l)
    have h2 : Module.finrank K (QuadExt l) = 2 := by
      rw [(AdjoinRoot.powerBasis' (monic_X_pow_sub_C l two_ne_zero)).finrank]
      exact natDegree_X_pow_sub_C
    have h3 : 2 ≤ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card]
      exact Finite.one_lt_card
    rw [Nat.card_eq_fintype_card, h1, h2]
    nlinarith
  exact CatalogueBGeneralLinear.specialLinear_quasisimple m _ hm (Or.inr (by omega))
    (Or.inr (by omega))

theorem blockDet_eq_one [Finite K] (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    (g : Matrix.SpecialLinearGroup (Fin m) (QuadExt l)) : blockDet l m g = 1 := by
  have hq := isQuasisimple_SL_quadExt hl hm
  have hperf : commutator (Matrix.SpecialLinearGroup (Fin m) (QuadExt l)) = ⊤ :=
    hq.1.commutator_eq_top
  have hle : commutator (Matrix.SpecialLinearGroup (Fin m) (QuadExt l)) ≤ (blockDet l m).ker :=
    Abelianization.commutator_subset_ker _
  exact hle (hperf ▸ mem_top g)

variable [Finite K]

@[expose] def blockSLE (hl : ¬ IsSquare l) (hm : 2 ≤ m) :
    Matrix.SpecialLinearGroup (Fin m) (QuadExt l) →* Matrix.SpecialLinearGroup (Fin (m * 2)) K where
  toFun g := ⟨blockRep l m g, by
    have h := blockDet_eq_one hl hm g
    rw [blockDet, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.ext_iff,
      GeneralLinearGroup.val_det_apply, Units.val_one] at h
    exact h⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := by
    apply Subtype.ext
    change blockRep l m ((g * h : Matrix.SpecialLinearGroup (Fin m) (QuadExt l)) :
      Matrix (Fin m) (Fin m) (QuadExt l)) = blockRep l m g * blockRep l m h
    rw [Matrix.SpecialLinearGroup.coe_mul, map_mul]

theorem coe_blockSLE (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    (g : Matrix.SpecialLinearGroup (Fin m) (QuadExt l)) :
    ((blockSLE hl hm g : Matrix.SpecialLinearGroup (Fin (m * 2)) K) :
      Matrix (Fin (m * 2)) (Fin (m * 2)) K) = blockRep l m g :=
  rfl

omit [Finite K] in
theorem quadMat_mul_self :
    quadMat l m * quadMat l m = l • (1 : Matrix (Fin (m * 2)) (Fin (m * 2)) K)
    := by
  rw [quadMat, ← map_mul, scalar_apply, diagonal_mul_diagonal, root_sq]
  have : (diagonal fun _ => algebraMap K (QuadExt l) l) =
      l • (1 : Matrix (Fin m) (Fin m) (QuadExt l)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Algebra.smul_def]
    · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
  rw [this, map_smul, map_one]

omit [Finite K] in
theorem l_ne_zero_of_not_isSquare (hl : ¬ IsSquare l) : l ≠ 0 := by
  rintro rfl
  exact hl ⟨0, by ring⟩

variable (l m) in
@[expose] def quadGL (hl : ¬ IsSquare l) : GL (Fin (m * 2)) K :=
  ⟨quadMat l m, l⁻¹ • quadMat l m,
    by rw [Matrix.mul_smul, quadMat_mul_self, smul_smul, inv_mul_cancel₀
      (l_ne_zero_of_not_isSquare hl), one_smul],
    by rw [Matrix.smul_mul, quadMat_mul_self, smul_smul, inv_mul_cancel₀
      (l_ne_zero_of_not_isSquare hl), one_smul]⟩

omit [Finite K] in
theorem coe_quadGL (hl : ¬ IsSquare l) :
    ((quadGL l m hl : GL (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K) = quadMat l m :=
  rfl

omit [Finite K] in
theorem quadGL_sq (hl : ¬ IsSquare l) :
    ∃ ν : Kˣ, quadGL l m hl * quadGL l m hl = GeneralLinearGroup.scalar (Fin (m * 2)) ν := by
  refine ⟨Units.mk0 l (l_ne_zero_of_not_isSquare hl), Units.ext ?_⟩
  rw [Units.val_mul, coe_quadGL, quadMat_mul_self]
  ext i j
  simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]

omit [Finite K] in
theorem blockRep_commute_quadMat (Y : Matrix (Fin m) (Fin m) (QuadExt l)) :
    blockRep l m Y * quadMat l m = quadMat l m * blockRep l m Y := by
  rw [quadMat, ← map_mul, ← map_mul, (Matrix.scalar_commute _ (fun _ => Commute.all _ _) Y).eq]

theorem range_blockSLE_le (hl : ¬ IsSquare l) (hm : 2 ≤ m) :
    (blockSLE hl hm).range ≤ slCentralizer (quadGL l m hl) := by
  rintro _ ⟨g, rfl⟩
  rw [mem_slCentralizer, coe_blockSLE, coe_quadGL]
  exact blockRep_commute_quadMat _

theorem normalizes_range_blockSLE (hl : ¬ IsSquare l) (hm : 2 ≤ m) :
    ∀ h ∈ slCentralizer (quadGL l m hl), ∀ g ∈ (blockSLE hl hm).range,
      h * g * h⁻¹ ∈ (blockSLE hl hm).range := by
  rintro h hh _ ⟨g, rfl⟩
  have hh' := mem_slCentralizer.1 hh
  rw [coe_quadGL] at hh'
  obtain ⟨Y, hY⟩ := exists_blockRep_of_commute hh'
  have hhi : ((h⁻¹ : Matrix.SpecialLinearGroup (Fin (m * 2)) K) : Matrix _ _ K) * quadMat l m =
      quadMat l m * ((h⁻¹ : Matrix.SpecialLinearGroup (Fin (m * 2)) K) : Matrix _ _ K) :=
    mem_slCentralizer.1 (inv_mem hh)
  obtain ⟨Y', hY'⟩ := exists_blockRep_of_commute hhi
  have hYY : Y * Y' = 1 := by
    apply blockRep_injective hl
    rw [map_mul, hY, hY', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, map_one]
  have hY'Y : Y' * Y = 1 := mul_eq_one_comm.1 hYY
  have hdet : (Y * (g : Matrix (Fin m) (Fin m) (QuadExt l)) * Y').det = 1 := by
    rw [det_mul, det_mul, g.2, mul_one, ← det_mul, hYY, det_one]
  refine ⟨⟨_, hdet⟩, Subtype.ext ?_⟩
  change blockRep l m (Y * (g : Matrix (Fin m) (Fin m) (QuadExt l)) * Y') =
    ((h * blockSLE hl hm g * h⁻¹ : Matrix.SpecialLinearGroup (Fin (m * 2)) K) :
      Matrix (Fin (m * 2)) (Fin (m * 2)) K)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSLE,
    map_mul, map_mul, hY, hY']

omit [Finite K] in
theorem blockRep_single_apply (i j : Fin m) (x y : Fin m × Fin 2) :
    blockRep l m (single i j (1 : QuadExt l)) (finProdFinEquiv x) (finProdFinEquiv y) =
      if x.1 = i ∧ y.1 = j ∧ x.2 = y.2 then 1 else 0 := by
  obtain ⟨i', a⟩ := x
  obtain ⟨j', b⟩ := y
  rw [blockRep_apply, single_apply]
  by_cases h : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := h
    simp [one_apply]
  · simp only [h, ↓reduceIte, map_zero, Matrix.zero_apply]
    have : ¬ (i' = i ∧ j' = j ∧ a = b) := fun h' => h ⟨h'.1.symm, h'.2.1.symm⟩
    simp only [this, ↓reduceIte]

omit [Finite K] in
theorem blockRep_single_map (i j : Fin m) (σ : K ≃+* K) :
    (blockRep l m (single i j (1 : QuadExt l))).map σ = blockRep l m (single i j 1) := by
  ext x y
  obtain ⟨x', rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨y', rfl⟩ := finProdFinEquiv.surjective y
  rw [Matrix.map_apply, blockRep_single_apply]
  split_ifs <;> simp

omit [Finite K] in
theorem blockRep_single_sq {i j : Fin m} (hij : i ≠ j) :
    blockRep l m (single i j (1 : QuadExt l)) * blockRep l m (single i j 1) = 0 := by
  have h0 : single i j (1 : QuadExt l) * single i j 1 = 0 := by
    ext a b
    simp only [Matrix.mul_apply, single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    split_ifs with h1 h2 <;> simp_all
  rw [← map_mul, h0, map_zero]

theorem coe_blockSLE_transvection (hl : ¬ IsSquare l) (hm : 2 ≤ m) {i j : Fin m} (hij : i ≠ j)
    (c : K) :
    ((blockSLE hl hm (Matrix.SpecialLinearGroup.transvection hij (algebraMap K (QuadExt l) c)) :
      Matrix.SpecialLinearGroup (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
      1 + c • blockRep l m (single i j 1) := by
  rw [coe_blockSLE, Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one]
  congr 1
  rw [← map_smul, smul_single, Algebra.smul_def, mul_one]

omit [Finite K] in
theorem eq_one_and_commute_of_fix_unipotents {n : ℕ} {p : ℕ} [Fact p.Prime] [CharP K p]
    {N : Matrix (Fin n) (Fin n) K} (hNmap : ∀ σ : K ≃+* K, N.map σ = N) (hNN : N * N = 0)
    {a b : Fin n} (hab : N a b = 1) (g : K → Matrix.SpecialLinearGroup (Fin n) K)
    (hg : ∀ c, (g c : Matrix (Fin n) (Fin n) K) = 1 + c • N) {D : GL (Fin n) K} {τ : K ≃+* K}
    (h : ∀ c : K, (conjAut n K D * fieldAut n K τ) (proj n K (g c)) = proj n K (g c)) :
    τ = 1 ∧ (D : Matrix (Fin n) (Fin n) K) * N = N * (D : Matrix (Fin n) (Fin n) K) := by
  set M : Matrix (Fin n) (Fin n) K := (D : Matrix (Fin n) (Fin n) K) with hM
  set Mi : Matrix (Fin n) (Fin n) K := ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hMi
  have h1M : M * Mi = 1 := by rw [hM, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2' : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpow : ∀ (c : K) (k : ℕ), ((1 + c • N) ^ k : Matrix (Fin n) (Fin n) K) =
      1 + ((k : K) * c) • N := by
    intro c k
    induction k with
    | zero => simp
    | succ k ih =>
      have hN1 : N * (1 + c • N) = N := by
        rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hNN, smul_zero, add_zero]
      rw [pow_succ, ih, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hN1, add_assoc,
        ← add_smul]
      congr 2
      push_cast
      ring
  have hgp : ∀ c, g c ^ p = 1 := by
    intro c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hg, hpow, CharP.cast_eq_zero, zero_mul, zero_smul,
      add_zero, Matrix.SpecialLinearGroup.coe_one]
  have hmap : ∀ c, Matrix.SpecialLinearGroup.map τ.toRingHom (g c) = g (τ c) := by
    intro c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, hg, hg, RingHom.mapMatrix_apply]
    ext x y
    have hxy := congrFun (congrFun (hNmap τ) x) y
    rw [Matrix.map_apply] at hxy
    have e : ∀ z, τ.toRingHom z = τ z := fun z => rfl
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply, e]
    rw [map_add, map_mul, hxy]
    split_ifs <;> simp
  have key : ∀ c : K, M * (τ c • N) * Mi = c • N := by
    intro c
    have h1 := h c
    rw [MulAut.mul_apply, fieldAut_proj, hmap, conjAut_proj] at h1
    have h3 := eq_of_proj_eq_of_pow_char (p := p)
      (by rw [← map_pow, hgp, map_one]) (hgp c) h1
    have h4 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin n) K =>
      (x : Matrix (Fin n) (Fin n) K)) h3
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix, hg] at h4
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1M] at h4
    exact add_left_cancel h4
  have e1 := key 1
  rw [map_one, one_smul] at e1
  have hτ : ∀ c, τ c = c := by
    intro c
    have e2 := key c
    rw [Matrix.mul_smul, Matrix.smul_mul, e1] at e2
    have := congrFun (congrFun e2 a) b
    simpa [hab] using this
  refine ⟨RingEquiv.ext hτ, ?_⟩
  calc M * N = M * N * Mi * M := by rw [Matrix.mul_assoc _ Mi, h2', Matrix.mul_one]
    _ = N * M := by rw [e1]

theorem blockSLE_injective (hl : ¬ IsSquare l) (hm : 2 ≤ m) : Function.Injective (blockSLE hl hm) :=
  fun _ _ e => Subtype.ext (blockRep_injective hl (congrArg Subtype.val e))

theorem isQuasisimple_blockImageE (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : projectiveSL (m * 2) K →*
      MulAut (projectiveSL (m * 2) K))) :
    IsQuasisimple ((blockSLE hl hm).range.map (conjProj (m * 2) K)) := by
  have hFq : IsQuasisimple (blockSLE hl hm).range :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (blockSLE_injective hl hm))
      (isQuasisimple_SL_quadExt hl hm)
  refine LocalCores.isQuasisimple_map hFq _ fun hle => ?_
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  set g := blockSLE hl hm (Matrix.SpecialLinearGroup.transvection h01
    (algebraMap K (QuadExt l) 1)) with hg
  have hker : conjProj (m * 2) K g = 1 := hle ⟨_, rfl⟩
  have hproj : proj (m * 2) K g = 1 := hinj (by rw [map_one]; exact hker)
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hproj
  have e := congrFun (congrFun hc (finProdFinEquiv (⟨0, by omega⟩, 0)))
    (finProdFinEquiv (⟨1, by omega⟩, 0))
  rw [hg, coe_blockSLE_transvection, Matrix.add_apply, Matrix.smul_apply, blockRep_single_apply,
    scalar_apply, diagonal_apply_ne] at e
  · simp at e
  · intro h
    have := finProdFinEquiv.injective h
    simp [Fin.ext_iff] at this

theorem nonsplit_oddCoreIn (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : projectiveSL (m * 2) K →*
      MulAut (projectiveSL (m * 2) K)))
    {B : Subgroup (MulAut (projectiveSL (m * 2) K))}
    (hB : (MulAut.conj : projectiveSL (m * 2) K →* MulAut (projectiveSL (m * 2) K)).range ≤ B)
    {y : MulAut (projectiveSL (m * 2) K)}
    (hy : y ∈ oddCoreIn B (conjAut (m * 2) K (quadGL l m hl))) :
    ∃ (D : GL (Fin (m * 2)) K) (x : QuadExt l), y = conjAut (m * 2) K D ∧
      (D : Matrix (Fin (m * 2)) (Fin (m * 2)) K) = blockRep l m (Matrix.scalar (Fin m) x) := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  have hn : 3 ≤ m * 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hyBC := mem_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hq := isQuasisimple_blockImageE hl hm hinj
  have hcomm : ∀ g ∈ (blockSLE hl hm).range,
      (conjAut (m * 2) K D * fieldAut (m * 2) K τ) (proj (m * 2) K g) = proj (m * 2) K g :=
    fun g hg => apply_proj_eq_of_commute hinj (commute_oddCoreIn_of_component hn hB _
      (range_blockSLE_le hl hm) (normalizes_range_blockSLE hl hm) hq
      (even_card_of_isQuasisimple hq) hy hg)
  have hfix : ∀ {i j : Fin m} (hij : i ≠ j), τ = 1 ∧
      (D : Matrix (Fin (m * 2)) (Fin (m * 2)) K) * blockRep l m (single i j 1) =
        blockRep l m (single i j 1) * (D : Matrix (Fin (m * 2)) (Fin (m * 2)) K) := by
    intro i j hij
    refine eq_one_and_commute_of_fix_unipotents (p := p) (blockRep_single_map i j)
      (blockRep_single_sq hij) (a := finProdFinEquiv (i, 0)) (b := finProdFinEquiv (j, 0))
      (by rw [blockRep_single_apply]; simp)
      (fun c => blockSLE hl hm (Matrix.SpecialLinearGroup.transvection hij
        (algebraMap K (QuadExt l) c)))
      (coe_blockSLE_transvection hl hm hij) fun c => hcomm _ ⟨_, rfl⟩
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hτ := (hfix h01).1
  subst hτ
  rw [map_one, mul_one] at hodd hyBC ⊢
  have hcD := commute_of_odd_conjAut hn (quadGL_sq hl) hodd
    (mem_centralizer_singleton_iff.1 hyBC.2)
  have hcD' := congrArg Units.val hcD
  rw [Units.val_mul, Units.val_mul, coe_quadGL] at hcD'
  obtain ⟨Y, hY⟩ := exists_blockRep_of_commute hcD'
  have hYc : ∀ {i j : Fin m}, i ≠ j → Y * single i j 1 = single i j 1 * Y := by
    intro i j hij
    apply blockRep_injective hl
    rw [map_mul, map_mul, hY]
    exact (hfix hij).2
  have hYs : Y = Matrix.scalar (Fin m) (Y ⟨0, by omega⟩ ⟨0, by omega⟩) := by
    ext a b
    rw [scalar_apply, diagonal_apply]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      by_cases ha : a = ⟨0, by omega⟩
      · rw [ha]
      · exact (commute_single_apply (hYc (Ne.symm ha))).1
    · simp only [hab, ↓reduceIte]
      exact (commute_single_apply (hYc (Ne.symm hab))).2.1 a hab
  exact ⟨D, _, rfl, by rw [← hY, ← hYs]⟩

omit [Finite K] in
theorem blockRep_scalar_apply (x : QuadExt l) (i j : Fin m) (a b : Fin 2) :
    blockRep l m (Matrix.scalar (Fin m) x) (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) =
      if i = j then quadRep l x a b else 0 := by
  rw [blockRep_apply, scalar_apply, diagonal_apply]
  split_ifs <;> simp

omit [Finite K] in
theorem compInd_commute_blockRep_scalar (hm : 1 ≤ m) (x : QuadExt l) :
    compInd K {finProdFinEquiv (⟨0, hm⟩, 0), finProdFinEquiv (⟨0, hm⟩, 1)} *
        blockRep l m (Matrix.scalar (Fin m) x) =
      blockRep l m (Matrix.scalar (Fin m) x) *
        compInd K {finProdFinEquiv (⟨0, hm⟩, 0), finProdFinEquiv (⟨0, hm⟩, 1)} := by
  rw [commute_compInd_iff]
  intro u v huv
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective u
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective v
  have hmem : ∀ k c, finProdFinEquiv (k, c) ∈ ({finProdFinEquiv (⟨0, hm⟩, 0),
      finProdFinEquiv (⟨0, hm⟩, 1)} : Finset (Fin (m * 2))) ↔ k = ⟨0, hm⟩ := by
    intro k c
    simp only [Finset.mem_insert, Finset.mem_singleton, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq]
    fin_cases c <;> simp
  rw [hmem, hmem] at huv
  have hij : i ≠ j := by
    rintro rfl
    tauto
  rw [blockRep_scalar_apply]
  simp [hij]

theorem nonsplit_propAConclusionIn (hK : ringChar K ≠ 2) (hl : ¬ IsSquare l) (hm : 2 ≤ m)
    (hinj : Function.Injective (MulAut.conj : projectiveSL (m * 2) K →*
      MulAut (projectiveSL (m * 2) K)))
    {B : Subgroup (MulAut (projectiveSL (m * 2) K))}
    (hB : (MulAut.conj : projectiveSL (m * 2) K →* MulAut (projectiveSL (m * 2) K)).range ≤ B)
    {Y : Subgroup (MulAut (projectiveSL (m * 2) K))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (conjAut (m * 2) K (quadGL l m hl))) :
    PropAConclusionIn B (conjAut (m * 2) K (quadGL l m hl)) Y := by
  have : Fact (Irreducible (quadPoly l)) := ⟨quadPoly_irreducible hl⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hn : 3 ≤ m * 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hm1 : 1 ≤ m := by omega
  set a := finProdFinEquiv ((⟨0, hm1⟩ : Fin m), (0 : Fin 2)) with ha
  set b := finProdFinEquiv ((⟨0, hm1⟩ : Fin m), (1 : Fin 2)) with hb
  have hab : a ≠ b := by
    intro h
    have := finProdFinEquiv.injective h
    simp at this
  set t := conjAut (m * 2) K (quadGL l m hl) with ht
  have hcore := fun {y} (hy : y ∈ oddCoreIn B t) => nonsplit_oddCoreIn hl hm hinj hB hy
  have h4 : 4 ≤ Nat.card K := by
    by_contra h4
    have h3 : Nat.card K = 3 := by
      have hodd' := FiniteField.odd_card_of_char_ne_two hK
      rw [← Nat.card_eq_fintype_card] at hodd'
      have h1 : 1 < Nat.card K := Finite.one_lt_card
      have h2' : Nat.card K ≠ 2 := fun h => by rw [h] at hodd'; norm_num at hodd'
      omega
    apply hY
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨D, x, rfl, hD⟩ := hcore (hYO hy)
    have : Module.Finite K (QuadExt l) := (AdjoinRoot.powerBasis' (monic_X_pow_sub_C l
      two_ne_zero)).finite
    have : Finite (QuadExt l) := Module.finite_of_finite K
    have : Fintype (QuadExt l) := Fintype.ofFinite _
    have hcardE : Fintype.card (QuadExt l) = 9 := by
      rw [Module.card_eq_pow_finrank (K := K) (V := QuadExt l),
        (AdjoinRoot.powerBasis' (monic_X_pow_sub_C l two_ne_zero)).finrank,
        ← Nat.card_eq_fintype_card, h3]
      change 3 ^ (quadPoly l).natDegree = 9
      rw [natDegree_X_pow_sub_C]
      norm_num
    have hx : x ≠ 0 := by
      rintro rfl
      have hdet := D.isUnit.map Matrix.detMonoidHom
      rw [Matrix.coe_detMonoidHom, hD, scalar_apply] at hdet
      simp only [diagonal_zero, map_zero] at hdet
      have : Nonempty (Fin (m * 2)) := ⟨⟨0, by omega⟩⟩
      rw [det_zero] at hdet
      exact not_isUnit_zero hdet
    have hx8 : x ^ 8 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one x hx
      rwa [hcardE] at this
    have hx4 : x ^ 4 = 1 ∨ x ^ 4 = -1 := by
      have : (x ^ 4 - 1) * (x ^ 4 + 1) = 0 := by linear_combination hx8
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have hD4 : ∃ c : Kˣ, D ^ 4 = GeneralLinearGroup.scalar (Fin (m * 2)) c := by
      have hpow : ((D ^ 4 : GL (Fin (m * 2)) K) : Matrix (Fin (m * 2)) (Fin (m * 2)) K) =
          blockRep l m (Matrix.scalar (Fin m) (x ^ 4)) := by
        rw [Units.val_pow_eq_pow_val, hD, ← map_pow, ← map_pow]
      rcases hx4 with h | h
      · refine ⟨1, Units.ext ?_⟩
        rw [hpow, h, map_one, map_one, map_one]
        rfl
      · refine ⟨-1, Units.ext ?_⟩
        rw [hpow, h, map_neg, map_one, map_neg, map_one]
        ext i j
        simp [GeneralLinearGroup.scalar, one_apply]
    obtain ⟨c, hc⟩ := hD4
    have h1 : conjAut (m * 2) K D ^ 4 = 1 := by rw [← map_pow, hc, conjAut_scalar]
    have hodd := odd_orderOf_of_mem_oddCoreIn (hYO hy)
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    have : orderOf (conjAut (m * 2) K D) = 1 := by
      have h4' : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4'] at hdvd
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      rw [hk] at hodd ⊢
      rcases k with _ | k
      · rfl
      · exact absurd hodd (by rw [pow_succ]; simp)
    exact orderOf_eq_one_iff.1 this
  have hSB : pairSlice K a b ≤ B := pairSlice_le_range.trans hB
  have hu := orderOf_pairInvolution hK hn hinj hab
  obtain ⟨p', f, hp', hp'2, hf, ⟨e⟩⟩ := exists_sl_galoisField (K := K) hK
  have hcA : compInd K {a, b} * quadMat l m = quadMat l m * compInd K {a, b} :=
    compInd_commute_blockRep_scalar hm1 _
  refine propAConclusionIn_of_core ?_ hY hYO (hB ⟨_, rfl⟩) hu hSB (pairSlice_le_centralizer hab)
    (pairSlice_isPComponent hK hn hinj h4 hB hab)
    ⟨p', f, hp', hp'2, hf, ⟨(pairSliceEquivSL hn hinj hab).trans e⟩⟩
    (center_pairSlice hn hinj hab)
    (conjAut_mem_normalizer_pairSlice (by rw [coe_quadGL]; exact hcA)) ?_ ?_ ?_
  ·
    apply orderOf_eq_prime
    · rw [ht, ← map_pow, pow_two]
      obtain ⟨ν, hν⟩ := quadGL_sq (m := m) hl
      rw [hν, conjAut_scalar]
    · intro h1
      obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn (quadGL l m hl) 1
        (by rw [map_one, mul_one]; exact h1)
      have e := congrArg (fun M : GL (Fin (m * 2)) K => (M : Matrix (Fin (m * 2)) (Fin (m * 2)) K)
        b a) hc
      simp only [coe_quadGL] at e
      rw [hb, ha, quadMat_apply] at e
      have hne : finProdFinEquiv ((⟨0, hm1⟩ : Fin m), (1 : Fin 2)) ≠
          finProdFinEquiv ((⟨0, hm1⟩ : Fin m), (0 : Fin 2)) := fun h => hab (by rw [ha, hb, h])
      simp [GeneralLinearGroup.scalar, compMat, hne] at e
  ·
    by_contra hall
    push Not at hall
    have := (pairBlock_of_commute (p := p) hinj hab fun x hx => (hall x hx)).2.2
    rw [coe_quadGL, hb, ha, quadMat_apply] at this
    simp [compMat] at this
  ·
    intro y hy
    obtain ⟨D, x, rfl, hD⟩ := hcore hy
    exact conjAut_mem_normalizer_pairSlice (by rw [hD]; exact compInd_commute_blockRep_scalar hm1 x)
  ·
    intro y hy hcomm
    obtain ⟨D, x, rfl, hD⟩ := hcore hy
    obtain ⟨e1, -, e3⟩ := pairBlock_of_commute (p := p) hinj hab hcomm
    simp only [hD, ha, hb, blockRep_scalar_apply, ↓reduceIte] at e1 e3
    have hcx : quadRep l x * compMat l = compMat l * quadRep l x := by
      rw [← quadRep_root, ← map_mul, ← map_mul, mul_comm]
    have e01 := congrFun (congrFun hcx 0) 0
    simp [compMat, Matrix.mul_apply, Fin.sum_univ_two] at e01
    set α := quadRep l x 0 0 with hα
    have hρ : quadRep l x = α • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [e01, e3, hα, ← e1]
    have hDs : (D : Matrix (Fin (m * 2)) (Fin (m * 2)) K) = α • 1 := by
      rw [hD]
      ext u v
      obtain ⟨⟨i, a'⟩, rfl⟩ := finProdFinEquiv.surjective u
      obtain ⟨⟨j, b'⟩, rfl⟩ := finProdFinEquiv.surjective v
      rw [blockRep_scalar_apply, hρ]
      by_cases hij : i = j
      · subst hij
        by_cases hab' : a' = b'
        · subst hab'
          simp
        · simp [hab']
      · simp [hij]
    have hα0 : α ≠ 0 := by
      intro h0
      have hdet := D.isUnit.map Matrix.detMonoidHom
      rw [Matrix.coe_detMonoidHom, hDs, h0, zero_smul] at hdet
      have : Nonempty (Fin (m * 2)) := ⟨⟨0, by omega⟩⟩
      rw [det_zero] at hdet
      exact not_isUnit_zero hdet
    have : D = GeneralLinearGroup.scalar (Fin (m * 2)) (Units.mk0 α hα0) := by
      apply Units.ext
      rw [hDs]
      ext i j
      simp [GeneralLinearGroup.scalar, Matrix.smul_apply, one_apply, diagonal_apply]
    rw [this, conjAut_scalar]

end CFSG.ComponentClassification.Burgoyne.PSL