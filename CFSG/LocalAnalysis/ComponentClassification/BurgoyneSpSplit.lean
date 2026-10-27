module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpNormal

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff
  leviSp coe_leviSp)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem stdSkew_mul_self : stdSkew r K * stdSkew r K = 1 := by
  rw [stdSkew, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext x
  rcases x with x | x <;> simp

theorem stdSkew_eq_fromBlocks : stdSkew r K = fromBlocks 1 0 0 (-1) := by
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [stdSkew, one_apply, hij]

theorem stdSkew_similitude : (stdSkew r K)ᵀ * formJ r K * stdSkew r K =
    ((-1 : Kˣ) : K) • formJ r K := by
  rw [stdSkew_eq_fromBlocks, fromBlocks_transpose, formJ, fromBlocks_multiply, fromBlocks_multiply]
  ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [one_apply, hij]

variable (r K) in
@[expose] def stdSkewGsp : gsp r K :=
  ⟨⟨stdSkew r K, stdSkew r K, stdSkew_mul_self, stdSkew_mul_self⟩, ⟨-1, stdSkew_similitude⟩⟩

theorem coe_stdSkewGsp : ((stdSkewGsp r K : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = stdSkew r K := rfl

theorem fromBlocks_of_commute_stdSkew (h2 : (2 : K) ≠ 0)
    {D : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (h : D * stdSkew r K = stdSkew r K * D) :
    D = fromBlocks D.toBlocks₁₁ 0 0 D.toBlocks₂₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks D]
  rw [stdSkew_eq_fromBlocks, ← fromBlocks_toBlocks D, fromBlocks_multiply,
    fromBlocks_multiply] at h
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul,
    zero_add, Matrix.mul_neg, Matrix.neg_mul] at h
  obtain ⟨-, h12, h21, -⟩ := Matrix.fromBlocks_inj.1 h
  have e12 : D.toBlocks₁₂ = 0 := by
    have : (2 : K) • D.toBlocks₁₂ = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h12]
      abel
    exact (smul_eq_zero.1 this).resolve_left h2
  have e21 : D.toBlocks₂₁ = 0 := by
    have : (2 : K) • D.toBlocks₂₁ = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h21]
      abel
    exact (smul_eq_zero.1 this).resolve_left h2
  rw [e12, e21]

variable (r K) in
@[expose] def leviSL : SL(r, K) →* StatedSp r K :=
  leviSp.comp Matrix.SpecialLinearGroup.toGL

theorem coe_leviSL (g : SL(r, K)) :
    (((leviSL r K g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks (g : Matrix (Fin r) (Fin r) K) 0 0
        ((g⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K)ᵀ := by
  rw [leviSL, MonoidHom.comp_apply, coe_leviSp, ← map_inv]
  rfl

theorem leviSL_injective : Function.Injective (leviSL r K) := by
  intro g h hgh
  have := congrArg (fun x : StatedSp r K => ((x : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hgh
  simp only [coe_leviSL, fromBlocks_inj] at this
  exact Subtype.ext this.1

theorem leviSL_mem_spCent (g : SL(r, K)) : leviSL r K g ∈ spCent r K (stdSkewGsp r K) := by
  rw [mem_spCent, coe_leviSL, coe_stdSkewGsp, stdSkew_eq_fromBlocks, fromBlocks_multiply,
    fromBlocks_multiply]
  simp

theorem eq_leviSL_of_blockDiag {g : StatedSp r K} {X Y : Matrix (Fin r) (Fin r) K}
    (hg : ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks X 0 0 Y) (hX : X.det = 1) :
    ∃ x : SL(r, K), g = leviSL r K x ∧ (x : Matrix (Fin r) (Fin r) K) = X := by
  obtain ⟨x, hx⟩ : ∃ x : SL(r, K), (x : Matrix (Fin r) (Fin r) K) = X := ⟨⟨X, hX⟩, rfl⟩
  refine ⟨x, statedSp_ext ?_, hx⟩
  have hJ := mem_statedSp_iff.1 g.2
  rw [hg, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply] at hJ
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, transpose_zero,
    Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at hJ
  obtain ⟨-, h12, -, -⟩ := Matrix.fromBlocks_inj.1 hJ
  rw [hg, coe_leviSL, hx]
  congr 1
  symm
  have h1 : ((x⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K) * X = 1 := by
    rw [← hx, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  calc ((x⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K)ᵀ =
      ((x⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K)ᵀ * (Xᵀ * Y) := by rw [h12, Matrix.mul_one]
    _ = (X * ((x⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K))ᵀ * Y := by
        rw [transpose_mul, Matrix.mul_assoc]
    _ = Y := by
        have h2 : X * ((x⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K) = 1 := by
          rw [← hx, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
            Matrix.SpecialLinearGroup.coe_one]
        rw [h2, transpose_one, Matrix.one_mul]

theorem conj_mem_leviSL_range (h2 : (2 : K) ≠ 0) {f : StatedSp r K}
    (hf : f ∈ spCent r K (stdSkewGsp r K)) {q : StatedSp r K} (hq : q ∈ (leviSL r K).range) :
    f * q * f⁻¹ ∈ (leviSL r K).range := by
  obtain ⟨x, rfl⟩ := hq
  set F := ((f : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hF
  set Fi := (((f⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hFi
  have hFc : F * stdSkew r K = stdSkew r K * F := (mem_spCent.1 hf).symm
  have hFic : Fi * stdSkew r K = stdSkew r K * Fi := (mem_spCent.1 (inv_mem hf)).symm
  have hFb := fromBlocks_of_commute_stdSkew h2 hFc
  have hFib := fromBlocks_of_commute_stdSkew h2 hFic
  have hFFi : F * Fi = 1 := by
    rw [hF, hFi, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      Units.val_one]
  have hmat : (((f * leviSL r K x * f⁻¹ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      fromBlocks (F.toBlocks₁₁ * (x : Matrix (Fin r) (Fin r) K) * Fi.toBlocks₁₁) 0 0
        (F.toBlocks₂₂ * ((x⁻¹ : SL(r, K)) : Matrix (Fin r) (Fin r) K)ᵀ * Fi.toBlocks₂₂) := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [← hF, ← hFi, coe_leviSL, hFb, hFib, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have h11 : F.toBlocks₁₁ * Fi.toBlocks₁₁ = 1 := by
    have := congrArg Matrix.toBlocks₁₁ hFFi
    have e : (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).toBlocks₁₁ = 1 := by
      rw [← fromBlocks_one, toBlocks_fromBlocks₁₁]
    rw [hFb, hFib, fromBlocks_multiply, e] at this
    simpa using this
  have hdet : (F.toBlocks₁₁ * (x : Matrix (Fin r) (Fin r) K) * Fi.toBlocks₁₁).det = 1 := by
    rw [det_mul, det_mul, x.2, mul_one, ← det_mul, h11, det_one]
  obtain ⟨z, hz, -⟩ := eq_leviSL_of_blockDiag hmat hdet
  exact ⟨z, hz.symm⟩

theorem isQuasisimple_leviSL_range [Finite K] (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 4 ≤ Nat.card K) :
    IsQuasisimple (leviSL r K).range :=
  LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective leviSL_injective)
    (CatalogueBGeneralLinear.specialLinear_quasisimple r K hr (by omega) (by omega))

abbrev levN (i j : Fin r) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  fromBlocks (single i j 1) 0 0 (-single j i 1)

theorem coe_leviSL_transvection {i j : Fin r} (hij : i ≠ j) (c : K) :
    (((leviSL r K (Matrix.SpecialLinearGroup.transvection hij c) : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + c • levN i j := by
  rw [coe_leviSL, Matrix.SpecialLinearGroup.transvection_inv,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    transpose_add, transpose_one, transpose_single, ← fromBlocks_one, levN, fromBlocks_smul,
    fromBlocks_add]
  simp only [smul_zero, add_zero, smul_single, smul_eq_mul, mul_one, smul_neg]
  congr 2
  ext a b
  simp only [single_apply, Matrix.neg_apply]
  split_ifs <;> simp

theorem blockDiag_diagonal {ι : Type} [Fintype ι] [DecidableEq ι] (J : Finset ι)
    (w : ι → K) : BlockDiag J (diagonal w) := by
  change offInd K J * diagonal w = diagonal w * offInd K J
  rw [offInd, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem skewSplit_oddCore [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (hrq : 3 ≤ r ∨ 4 ≤ Nat.card K)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {y : MulAut (StatedProj (StatedSp r K))}
    (hy : y ∈ oddCoreIn B (conjAut r K (stdSkewGsp r K))) :
    ∃ (D : gsp r K) (a b : K), y = conjAut r K D ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        diagonal (Sum.elim (fun _ => a) fun _ => b) := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  have hyt := commute_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hq := isQuasisimple_leviSL_range hr hrq (K := K)
  have hfix : ∀ g ∈ (leviSL r K).range,
      (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => commute_oddCoreIn_of_normal hinj hB (conjSp r K (stdSkewGsp r K)).toMonoidHom
      (conjAut_proj _) (by rintro _ ⟨x, rfl⟩; exact leviSL_mem_spCent x)
      (fun f hf q hq' => conj_mem_leviSL_range h2 hf hq') (isQuasisimple_map_conjProjH hinj hq)
      hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hq
  have key : ∀ i j : Fin r, i ≠ j → τ = 1 ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * levN i j =
        levN i j * ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    intro i j hij
    have hab : (levN i j : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (Sum.inl i) (Sum.inl j) ≠
        0 := by simp
    refine fix_unipotent_family_matrix hab fun c => ?_
    have h := semilinear_eq_of_fix hperf hfix ⟨Matrix.SpecialLinearGroup.transvection hij c, rfl⟩
    rwa [coe_leviSL_transvection, map_one_add_smul] at h
  have h01 : (⟨0, by omega⟩ : Fin r) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hτ := (key _ _ h01).1
  rw [hτ, map_one, mul_one] at hoddy hyt ⊢
  have hss : ((stdSkewGsp r K : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((stdSkewGsp r K : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (1 : K) • 1 := by rw [coe_stdSkewGsp, stdSkew_mul_self, one_smul]
  obtain ⟨D', ⟨m, hm⟩, hD'D, hD'A⟩ := exists_commute_of_odd (by omega) one_ne_zero hss hyt hoddy
  set M' := ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM'
  have hM'pow : M' = ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) ^ m :=
    by rw [hM', hm, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have hcomm : ∀ i j : Fin r, i ≠ j → M' * levN i j = levN i j * M' := by
    intro i j hij
    rw [hM'pow]
    exact (Commute.pow_left (key i j hij).2 m).eq
  have hblk := fromBlocks_of_commute_stdSkew h2 (show M' * stdSkew r K = stdSkew r K * M' by
    rw [← coe_stdSkewGsp]; exact hD'A)
  set P := M'.toBlocks₁₁ with hP
  set R := M'.toBlocks₂₂ with hR
  have hPc : ∀ i j : Fin r, i ≠ j → P * single i j 1 = single i j 1 * P := by
    intro i j hij
    have h := hcomm i j hij
    rw [hblk, levN, fromBlocks_multiply, fromBlocks_multiply] at h
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
    exact (Matrix.fromBlocks_inj.1 h).1
  have hRc : ∀ i j : Fin r, i ≠ j → R * single i j 1 = single i j 1 * R := by
    intro i j hij
    have h := hcomm j i (Ne.symm hij)
    rw [hblk, levN, fromBlocks_multiply, fromBlocks_multiply] at h
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul] at h
    exact neg_inj.1 (Matrix.fromBlocks_inj.1 h).2.2.2
  obtain ⟨a, ha⟩ : ∃ a, P = Matrix.scalar (Fin r) a :=
    ⟨_, eq_scalar_of_commute_single ⟨0, by omega⟩ hPc⟩
  obtain ⟨b, hb⟩ : ∃ b, R = Matrix.scalar (Fin r) b :=
    ⟨_, eq_scalar_of_commute_single ⟨0, by omega⟩ hRc⟩
  refine ⟨D', a, b, hD'D.symm, ?_⟩
  change M' = _
  rw [hblk, ha, hb, scalar_apply, scalar_apply, fromBlocks_diagonal]

theorem orderOf_conjAut_stdSkew [Finite K] (hK : ringChar K ≠ 2) (hr : 1 ≤ r) :
    orderOf (conjAut r K (stdSkewGsp r K)) = 2 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  apply orderOf_eq_prime
  · rw [pow_two, ← map_mul, conjAut_eq_one_iff hr]
    refine ⟨1, Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, coe_stdSkewGsp, stdSkew_mul_self, map_one,
      Units.val_one]
  · intro h1
    obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hr _).1 h1
    have e1 := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K) (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) hc
    have e2 := congrArg (fun g : GL (Fin r ⊕ Fin r) K => (g : Matrix (Fin r ⊕ Fin r)
      (Fin r ⊕ Fin r) K) (Sum.inr ⟨0, by omega⟩) (Sum.inr ⟨0, by omega⟩)) hc
    simp only [coe_stdSkewGsp, stdSkew, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr] at e1 e2
    exact h2 (by linear_combination e1 - e2)

theorem skewSplit_propAConclusionIn [Finite K] (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (h4 : 4 ≤ Nat.card K)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    {Y : Subgroup (MulAut (StatedProj (StatedSp r K)))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (conjAut r K (stdSkewGsp r K))) :
    PropAConclusionIn B (conjAut r K (stdSkewGsp r K)) Y := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set i₀ : Fin r := ⟨0, by omega⟩ with hi₀
  have hcore := fun {y} (hy : y ∈ oddCoreIn B (conjAut r K (stdSkewGsp r K))) =>
    skewSplit_oddCore hK hr (Or.inr h4) hinj hB hy
  refine slice_propAConclusionIn hinj hB (longRoot_inf hr i₀) hK h4 (lrInv_mem i₀)
    (longRootEquiv K i₀) (longRootEquiv_lrInv i₀) (longRoot_commute i₀)
    (longRoot_normalized h2 i₀) (orderOf_conjAut_stdSkew hK (by omega)) hY hYO
    (conjAut_mem_normalizer_slice (blockDiag_diagonal _ _)) ?_ ?_ ?_
  · by_contra h
    push Not at h
    obtain ⟨-, -, h3⟩ := pairBlock_scalar_of_commute_slice (p := p) hinj
      (blockDiag_diagonal (lrPair i₀) (Sum.elim (fun _ => (1 : K)) fun _ => -1)) h
    simp only [coe_stdSkewGsp, stdSkew, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr] at h3
    exact h2 (by linear_combination h3)
  · intro y hy
    obtain ⟨D, a, b, rfl, hD⟩ := hcore hy
    exact conjAut_mem_normalizer_slice (by rw [hD]; exact blockDiag_diagonal _ _)
  · intro y hy hc
    obtain ⟨D, a, b, rfl, hD⟩ := hcore hy
    obtain ⟨-, -, h3⟩ := pairBlock_scalar_of_commute_slice (p := p) hinj
      (by rw [hD]; exact blockDiag_diagonal _ _) hc
    simp only [hD, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr] at h3
    have ha0 : a ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun (Units.mul_inv (D : GL (Fin r ⊕ Fin r) K)) (Sum.inl i₀))
        (Sum.inl i₀)
      rw [hD, diagonal_mul, Sum.elim_inl, h0, zero_mul, one_apply_eq] at h1
      exact zero_ne_one h1
    rw [conjAut_eq_one_iff (by omega)]
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, hD, ← h3, scalar_apply]
    congr 1
    funext x
    rcases x with x | x <;> rfl

end CFSG.ComponentClassification.Burgoyne.Sp
