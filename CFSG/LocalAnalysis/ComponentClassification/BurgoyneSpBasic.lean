module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjPair
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam coe_lam pairMat pairMat_mul
  pairMat_one sl2Diag coe_sl2Diag statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem projH_eq : projH (StatedSp r K) = proj r K := rfl

@[expose] def semiLift (D : gsp r K) (σ : K ≃+* K) : StatedSp r K →* StatedSp r K :=
  (conjSp r K D).toMonoidHom.comp (fieldSp r K σ).toMonoidHom

theorem semiLift_proj (D : gsp r K) (σ : K ≃+* K) (g : StatedSp r K) :
    (conjAut r K D * fieldAut r K σ) (proj r K g) = proj r K (semiLift D σ g) :=
  rfl

theorem coe_semiLift (D : gsp r K) (σ : K ≃+* K) (g : StatedSp r K) :
    (((semiLift D σ g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
        (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  change ((((D : GL (Fin r ⊕ Fin r) K) * (fieldSp r K σ g : GL (Fin r ⊕ Fin r) K) *
    (D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K)) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = _
  rw [Units.val_mul, Units.val_mul, coe_fieldSp]

theorem semilinear_eq_of_fix {D : gsp r K} {σ : K ≃+* K} {F : Subgroup (StatedSp r K)}
    (hF : ⁅F, F⁆ = F)
    (h : ∀ g ∈ F, (conjAut r K D * fieldAut r K σ) (proj r K g) = proj r K g)
    {g : StatedSp r K} (hg : g ∈ F) :
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ *
        (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have h1 := lift_eq_of_commutator_eq (H := StatedSp r K) (semiLift D σ) (semiLift_proj D σ) hF h
    hg
  have h2 := congrArg (fun x : StatedSp r K => ((x : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
  simpa only [coe_semiLift] using h2

theorem conjAut_eq_one_iff [Finite K] (hr : 1 ≤ r) (D : gsp r K) :
    conjAut r K D = 1 ↔ ∃ c : Kˣ,
      (D : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  have h := CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff hr D 1
  rw [map_one, mul_one] at h
  rw [h]
  exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

section Unip

variable {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

@[expose] def unipGL (h3 : N * N = 0) (c : K) : GL (Fin r ⊕ Fin r) K :=
  ⟨1 + c • N, 1 - c • N, by
    rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h3, smul_zero]
    abel, by
    rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h3, smul_zero]
    abel⟩

theorem coe_unipGL (h3 : N * N = 0) (c : K) :
    ((unipGL h3 c : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      1 + c • N :=
  rfl

theorem unipGL_mem (h1 : Nᵀ * formJ r K + formJ r K * N = 0)
    (h2 : Nᵀ * formJ r K * N = 0) (h3 : N * N = 0) (c : K) :
    unipGL h3 c ∈ StatedSp r K := by
  rw [mem_statedSp_iff, coe_unipGL]
  change (1 + c • N)ᵀ * formJ r K * (1 + c • N) = formJ r K
  have e : (1 + c • N)ᵀ * formJ r K * (1 + c • N) = formJ r K +
      c • (Nᵀ * formJ r K + formJ r K * N) + (c * c) • (Nᵀ * formJ r K * N) := by
    rw [transpose_add, transpose_one, transpose_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, smul_smul, Matrix.mul_assoc]
    abel
  rw [e, h1, h2, smul_zero, smul_zero, add_zero, add_zero]

@[expose] def unipSp (h1 : Nᵀ * formJ r K + formJ r K * N = 0) (h2 : Nᵀ * formJ r K * N = 0)
    (h3 : N * N = 0) (c : K) : StatedSp r K :=
  ⟨unipGL h3 c, unipGL_mem h1 h2 h3 c⟩

theorem coe_unipSp (h1 : Nᵀ * formJ r K + formJ r K * N = 0) (h2 : Nᵀ * formJ r K * N = 0)
    (h3 : N * N = 0) (c : K) :
    (((unipSp h1 h2 h3 c : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + c • N :=
  rfl

end Unip

section LongRoot

variable (K) in
abbrev longRoot (i₀ : Fin r) : Subgroup (StatedSp r K) := (lam (k := K) i₀).range

abbrev lrPair (i₀ : Fin r) : Finset (Fin r ⊕ Fin r) := {Sum.inl i₀, Sum.inr i₀}

theorem lam_injective (i₀ : Fin r) : Function.Injective (lam (k := K) i₀) := by
  intro g h hgh
  apply Subtype.ext
  have := congrArg (fun x : StatedSp r K => pairBlock (Sum.inl i₀) (Sum.inr i₀)
    ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hgh
  simpa only [coe_lam, pairBlock_pairMat Sum.inl_ne_inr] using this

variable (K) in
@[expose] def longRootEquiv (i₀ : Fin r) : longRoot K i₀ ≃* SL(2, K) :=
  (MonoidHom.ofInjective (lam_injective i₀)).symm

theorem lam_longRootEquiv (i₀ : Fin r) (g : longRoot K i₀) :
    lam i₀ (longRootEquiv K i₀ g) = g := by
  have := (MonoidHom.ofInjective (lam_injective (K := K) i₀)).apply_symm_apply g
  exact congrArg Subtype.val this

variable (K) in
abbrev lrInv (i₀ : Fin r) : StatedSp r K := lam i₀ (sl2Diag (-1))

theorem lrInv_mem (i₀ : Fin r) : lrInv K i₀ ∈ longRoot K i₀ := ⟨_, rfl⟩

theorem longRootEquiv_lrInv (i₀ : Fin r) :
    ((longRootEquiv K i₀ ⟨lrInv K i₀, lrInv_mem i₀⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      -1 := by
  have h : longRootEquiv K i₀ ⟨lrInv K i₀, lrInv_mem i₀⟩ = sl2Diag (-1) := by
    apply lam_injective i₀
    rw [lam_longRootEquiv]
  rw [h, coe_sl2Diag]
  ext s t
  fin_cases s <;> fin_cases t <;> simp

theorem coe_lrInv (i₀ : Fin r) :
    (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (2 : K) • offInd K (lrPair i₀) - 1 := by
  rw [coe_lam, coe_sl2Diag]
  ext x y
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x = Sum.inl i₀
    · subst hx
      simp [pairMat, offInd]
    · by_cases hx' : x = Sum.inr i₀
      · subst hx'
        simp [pairMat, offInd]
      · simp [pairMat, offInd, hx, hx']
        norm_num
  · simp only [Matrix.sub_apply, Matrix.smul_apply, offInd, diagonal_apply_ne _ hxy,
      smul_zero, one_apply_ne hxy, sub_zero]
    by_cases hx : x = Sum.inl i₀
    · subst hx
      by_cases hy : y = Sum.inr i₀
      · subst hy
        simp [pairMat]
      · simp [pairMat, Ne.symm hxy]
    · by_cases hx' : x = Sum.inr i₀
      · subst hx'
        by_cases hy : y = Sum.inl i₀
        · subst hy
          simp [pairMat]
        · simp [pairMat, Ne.symm hxy]
      · simp [pairMat, hx, hx', one_apply_ne hxy]

theorem blockDiag_of_commute_lrInv (h2 : (2 : K) ≠ 0) (i₀ : Fin r)
    {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h : M * (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (((lrInv K i₀ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * M) :
    BlockDiag (lrPair i₀) M := by
  rw [coe_lrInv, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_smul, Matrix.smul_mul] at h
  have h' : (2 : K) • (M * offInd K (lrPair i₀) - offInd K (lrPair i₀) * M) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.2 (sub_left_injective h)
  have := (smul_eq_zero.1 h').resolve_left h2
  exact (sub_eq_zero.1 this).symm

theorem det_pairBlock_of_mem (i₀ : Fin r) {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : PairSupp (lrPair i₀) M) (hJ : Mᵀ * formJ r K * M = formJ r K) :
    (pairBlock (Sum.inl i₀) (Sum.inr i₀) M).det = 1 := by
  have h0 := pairSupp_iff.1 hM
  have hab : (Sum.inl i₀ : Fin r ⊕ Fin r) ≠ Sum.inr i₀ := Sum.inl_ne_inr
  have hcol : ∀ y ∈ lrPair i₀, ∀ z, z ∉ lrPair i₀ → M z y = 0 := by
    intro y hy z hz
    rw [h0 z y (Or.inl hz)]
    have hzy : z ≠ y := by
      rintro rfl
      exact hz hy
    simp [hzy]
  have hrow : ∀ y, (Mᵀ * formJ r K) (Sum.inl i₀) y =
      M (Sum.inl i₀) (Sum.inl i₀) * formJ r K (Sum.inl i₀) y +
        M (Sum.inr i₀) (Sum.inl i₀) * formJ r K (Sum.inr i₀) y := by
    intro y
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_add _ _ hab (fun z _ hz => ?_) (by simp) (by simp)
    rw [transpose_apply, hcol _ (by simp) z (by simp [hz.1, hz.2]), zero_mul]
  have hJab := congrFun (congrFun hJ (Sum.inl i₀)) (Sum.inr i₀)
  rw [Matrix.mul_apply, Finset.sum_eq_add (Sum.inl i₀) (Sum.inr i₀) hab (fun w _ hw => by
      rw [hcol _ (by simp) w (by simp [hw.1, hw.2]), mul_zero]) (by simp) (by simp),
    hrow, hrow] at hJab
  simp [formJ, pairBlock, det_fin_two_of] at hJab ⊢
  linear_combination hJab

theorem mem_longRoot_of_pairSupp (i₀ : Fin r) {g : StatedSp r K}
    (hg : PairSupp (lrPair i₀)
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    g ∈ longRoot K i₀ := by
  have hdet := det_pairBlock_of_mem i₀ hg (mem_statedSp_iff.1 g.2)
  obtain ⟨X, hX⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) =
      pairBlock (Sum.inl i₀) (Sum.inr i₀)
        ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
    ⟨⟨_, hdet⟩, rfl⟩
  refine ⟨X, statedSp_ext ?_⟩
  rw [coe_lam, hX]
  exact pairMat_pairBlock Sum.inl_ne_inr hg

theorem pairSupp_of_mem_longRoot (i₀ : Fin r) {g : StatedSp r K} (hg : g ∈ longRoot K i₀) :
    PairSupp (lrPair i₀)
      ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  obtain ⟨X, rfl⟩ := hg
  rw [coe_lam]
  exact pairSupp_pairMat Sum.inl_ne_inr _

theorem longRoot_inf (hr : 2 ≤ r) (i₀ : Fin r) :
    ∀ g ∈ longRoot K i₀, g ∈ (StatedScalars (Fin r ⊕ Fin r) K).subgroupOf (StatedSp r K) →
      g = 1 := by
  intro g hg hz
  obtain ⟨c, hc⟩ := hz
  have hc' : (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) =
      (g : GL (Fin r ⊕ Fin r) K) := hc
  obtain ⟨j, hj⟩ : ∃ j : Fin r, j ≠ i₀ := by
    by_cases h : i₀ = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  have hS := pairSupp_iff.1 (pairSupp_of_mem_longRoot i₀ hg)
  have hjj := hS (Sum.inl j) (Sum.inl j) (Or.inl (by simp [hj]))
  rw [← hc'] at hjj
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, ↓reduceIte] at hjj
  have hc1 : c = 1 := Units.ext hjj
  apply statedSp_ext
  rw [← hc', hc1, map_one]
  rfl

theorem longRoot_commute (i₀ : Fin r) :
    ∀ g ∈ longRoot K i₀, g * lrInv K i₀ = lrInv K i₀ * g := by
  rintro _ ⟨X, rfl⟩
  rw [lrInv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag]
  ext s t
  fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem conj_mem_longRoot (i₀ : Fin r) {h g : StatedSp r K}
    (hh : BlockDiag (lrPair i₀)
      ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hg : g ∈ longRoot K i₀) : h * g * h⁻¹ ∈ longRoot K i₀ := by
  apply mem_longRoot_of_pairSupp
  have e : ((h * g * h⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) =
      (h : GL (Fin r ⊕ Fin r) K) * g * (h : GL (Fin r ⊕ Fin r) K)⁻¹ := rfl
  rw [e, Units.val_mul, Units.val_mul]
  exact pairSupp_conj (Units.mul_inv _) (Units.inv_mul _) hh (pairSupp_of_mem_longRoot i₀ hg)

theorem longRoot_normalized (h2 : (2 : K) ≠ 0) (i₀ : Fin r) :
    ∀ h : StatedSp r K, h * lrInv K i₀ = lrInv K i₀ * h →
      ∀ g ∈ longRoot K i₀, h * g * h⁻¹ ∈ longRoot K i₀ := by
  intro h hh g hg
  refine conj_mem_longRoot i₀ (blockDiag_of_commute_lrInv h2 i₀ ?_) hg
  have := congrArg (fun x : StatedSp r K => ((x : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hh
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem conjAut_mul_conjProjH (D : gsp r K) (g : StatedSp r K) :
    conjAut r K D * conjProjH (StatedSp r K) g * (conjAut r K D)⁻¹ =
      conjProjH (StatedSp r K) (conjSp r K D g) := by
  rw [MonoidHom.comp_apply, mul_conj_mul_inv]
  rfl

theorem blockDiag_inv {i₀ : Fin r} {D : gsp r K}
    (hD : BlockDiag (lrPair i₀)
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    BlockDiag (lrPair i₀)
      (((D⁻¹ : gsp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  blockDiag_of_mul_eq_one hD (Units.mul_inv _) (Units.inv_mul _)

theorem conjAut_mul_mem_slice {i₀ : Fin r} {D : gsp r K}
    (hD : BlockDiag (lrPair i₀)
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    {x : MulAut (StatedProj (StatedSp r K))} (hx : x ∈ slice (longRoot K i₀)) :
    conjAut r K D * x * (conjAut r K D)⁻¹ ∈ slice (longRoot K i₀) := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [conjAut_mul_conjProjH]
  refine ⟨_, mem_longRoot_of_pairSupp i₀ ?_, rfl⟩
  rw [coe_conjSp, Units.val_mul, Units.val_mul]
  exact pairSupp_conj (Units.mul_inv _) (Units.inv_mul _) hD (pairSupp_of_mem_longRoot i₀ hg)

theorem conjAut_mem_normalizer_slice {i₀ : Fin r} {D : gsp r K}
    (hD : BlockDiag (lrPair i₀)
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    conjAut r K D ∈
      normalizer (slice (longRoot K i₀) : Set (MulAut (StatedProj (StatedSp r K)))) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conjAut_mul_mem_slice hD hx, fun hx => ?_⟩
  have h := conjAut_mul_mem_slice (blockDiag_inv hD) hx
  have e : conjAut r K D⁻¹ * (conjAut r K D * x * (conjAut r K D)⁻¹) * (conjAut r K D⁻¹)⁻¹ =
      x := by
    rw [map_inv, inv_inv]
    group
  rwa [e] at h

theorem unip_pow_char {p : ℕ} [CharP K p] (c : K) :
    (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K) ^ p = 1 ∧
      (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
  have h1 : ∀ m : ℕ, (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) K) ^ m = !![1, m * c; 0, 1] := by
    intro m
    induction m with
    | zero => ext s t; fin_cases s <;> fin_cases t <;> simp
    | succ m ih =>
      rw [pow_succ, ih]
      ext s t
      fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
  have h2 : ∀ m : ℕ, (!![1, 0; c, 1] : Matrix (Fin 2) (Fin 2) K) ^ m = !![1, 0; m * c, 1] := by
    intro m
    induction m with
    | zero => ext s t; fin_cases s <;> fin_cases t <;> simp
    | succ m ih =>
      rw [pow_succ, ih]
      ext s t
      fin_cases s <;> fin_cases t <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring
  rw [h1, h2, CharP.cast_eq_zero, zero_mul]
  constructor <;> ext s t <;> fin_cases s <;> fin_cases t <;> simp

theorem pairBlock_scalar_of_commute_slice {p : ℕ} [Fact p.Prime] [CharP K p]
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {i₀ : Fin r} {D : gsp r K}
    (hD : BlockDiag (lrPair i₀)
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hc : ∀ x ∈ slice (longRoot K i₀), conjAut r K D * x = x * conjAut r K D) :
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl i₀) (Sum.inr i₀) = 0 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inr i₀) (Sum.inl i₀) = 0 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inl i₀) (Sum.inl i₀) =
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
        (Sum.inr i₀) (Sum.inr i₀) := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl i₀⟩
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  have hMiM : Mi * M = 1 := by rw [hM, hMi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ X : SL(2, K), X ^ p = 1 →
      M * pairMat (Sum.inl i₀) (Sum.inr i₀) (X : Matrix (Fin 2) (Fin 2) K) =
        pairMat (Sum.inl i₀) (Sum.inr i₀) (X : Matrix (Fin 2) (Fin 2) K) * M := by
    intro X hX
    set g := lam (k := K) i₀ X with hg
    have h1 := hc _ ⟨g, ⟨X, rfl⟩, rfl⟩
    have h2 : conjProjH (StatedSp r K) (conjSp r K D g) = conjProjH (StatedSp r K) g := by
      rw [← conjAut_mul_conjProjH, h1, mul_inv_cancel_right]
    have hgp : g ^ p = 1 := by rw [hg, ← map_pow, hX, map_one]
    have hcp : (conjSp r K D g) ^ p = 1 := by rw [← map_pow, hgp, map_one]
    have h3 := eq_of_projH_eq_of_pow_char hcp hgp (hinj h2)
    have h4 := congrArg (fun x : StatedSp r K => ((x : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h3
    simp only [coe_conjSp, Units.val_mul, hg, coe_lam] at h4
    calc M * pairMat (Sum.inl i₀) (Sum.inr i₀) (X : Matrix (Fin 2) (Fin 2) K)
        = M * pairMat (Sum.inl i₀) (Sum.inr i₀) (X : Matrix (Fin 2) (Fin 2) K) * (Mi * M) := by
          rw [hMiM, Matrix.mul_one]
      _ = pairMat (Sum.inl i₀) (Sum.inr i₀) (X : Matrix (Fin 2) (Fin 2) K) * M := by
          rw [← Matrix.mul_assoc, h4]
  obtain ⟨hu1, hu2⟩ := unip_pow_char (K := K) (p := p) 1
  obtain ⟨X₁, hX₁⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
    ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X : SL(2, K), (X : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] :=
    ⟨⟨_, by simp [det_fin_two_of]⟩, rfl⟩
  have e1 := key X₁ (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, hX₁]; exact hu1))
  have e2 := key X₂ (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, hX₂]; exact hu2))
  rw [hX₁] at e1
  rw [hX₂] at e2
  exact pairBlock_scalar_of_commute Sum.inl_ne_inr hD e1 e2

end LongRoot

end CFSG.ComponentClassification.Burgoyne.Sp
