module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieClSpField
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSplit

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.ClSp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff
  leviSp coe_leviSp)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (eigenPlus eigenMinus invSMulOp
  similitudeCentralizer exists_bilin_split_equiv eigen_ne_bot isCompl_ker_sub_one_ker_add_one
  invSMulOp_mul_self bilin_eq_zero_swap)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.Sp
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K] [Finite K]
  {R : Subgroup (MulAut (StatedProj (StatedSp r K)))}

omit [Finite K] in
theorem conjAut_commute {D D' : gsp r K}
    (h : ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) :
    conjAut r K D * conjAut r K D' = conjAut r K D' * conjAut r K D := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Units.ext h)

omit [Finite K] in
theorem eigen_of_fix {Q : Subgroup (StatedSp r K)} (hQq : IsQuasisimple Q)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hTQ : ∀ v ∈ W, ∀ c, transvSp v c ∈ Q)
    {D : gsp r K} {τ : K ≃+* K}
    (hfix : ∀ g ∈ Q, (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g) :
    (W ≠ ⊥ → τ = 1) ∧ ∀ v ∈ W, ∃ μ : K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = μ • v := by
  have hperf := commutator_eq_self_of_isQuasisimple hQq
  have key : ∀ v ∈ W, v ≠ 0 → τ = 1 ∧ ∃ μ : K,
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v = μ • v := by
    intro v hv hv0
    obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    obtain ⟨b, hb⟩ : ∃ b, (v ᵥ* formJ r K) b ≠ 0 := by
      by_contra h
      push Not at h
      exact vecMul_formJ_ne_zero hv0 (funext h)
    have hab : transvN v a b ≠ 0 := by
      simp only [transvN, vecMulVec_apply]
      exact mul_ne_zero ha hb
    have hfam : ∀ c : K, ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (1 + τ c • (transvN v).map τ) * (((D : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + c • transvN v := by
      intro c
      have h := semilinear_eq_of_fix hperf hfix (hTQ v hv c)
      rwa [coe_transvSp, map_one_add_smul] at h
    obtain ⟨hτ, hcomm⟩ := fix_unipotent_family_matrix hab hfam
    exact ⟨hτ, exists_eigen_of_commute_vecMulVec' hb hcomm⟩
  refine ⟨fun hW => ?_, fun v hv => ?_⟩
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact (key v hv hv0).1
  · by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, mulVec_zero, smul_zero]⟩
    · exact (key v hv hv0).2

theorem eq_one_splitSelf (hK : ringChar K ≠ 2) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {A : gsp r K} {l : K}
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    (hl0 : l ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (l ^ 2) • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (l ^ 2) • formJ r K)
    (hPx : Module.finrank K (VPl A l) ≠ 2 ∨ Nat.card K ≠ 3)
    (hMx : Module.finrank K (VMl A l) ≠ 2 ∨ Nat.card K ≠ 3) (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut r K A = conjAut r K A * y)
    (hRc : ∀ s, conjAut r K A s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {y} (hy : y ∈ R) : y = 1 := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have : NeZero r := ⟨by omega⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hd0 : l ^ 2 ≠ 0 := pow_ne_zero 2 hl0
  have hJA : Mᵀ * formJ r K = formJ r K * M := transpose_mul_formJ hd0 hJ hAA
  have hAA' := linA_mul_self hAA
  have hTB : ∀ v w, pairedSympForm K r (invSMulOp l ((linA A :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (invSMulOp l ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = pairedSympForm K r v w := by
    intro v w
    simp only [invSMulOp, LinearMap.smul_apply, linA_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [form_similitude hJ]
    field_simp
  have hAns' : ∀ c : K, ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  obtain ⟨hPne, hMne⟩ := eigen_ne_bot h2 hl0 hAA' hAns'
  obtain ⟨horth, haltP, haltM, hndP, hndM, e, he⟩ :=
    exists_bilin_split_equiv h2 pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      hl0 hAA' hTB
  set Ψ := (spCentEquiv A).trans e with hΨ
  have hres : ∀ g : spCent r K A, (Ψ g).2 = 1 ↔ ∀ v ∈ VMl A l,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv A g)).2 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A g)).2]
    simp only [spCentEquiv_apply]
  have hres' : ∀ g : spCent r K A, ((Ψ.trans (MulEquiv.prodComm)) g).2 = 1 ↔ ∀ v ∈ VPl A l,
      (((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ
        v = v := by
    intro g
    change (e (spCentEquiv A g)).1 = 1 ↔ _
    rw [← OneMemClass.coe_eq_one, glW_eq_one_iff (he (spCentEquiv A g)).1]
    simp only [spCentEquiv_apply]
  have hqP : IsQuasisimple (fixSub r K A (VMl A l)) :=
    isQuasisimple_fixSub_of_equiv Ψ hres
      (LocalCores.isQuasisimple_of_mulEquiv (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
        (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltP hndP
          (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hPne _ haltP hndP) hodd hPx))
  have hqM : IsQuasisimple (fixSub r K A (VPl A l)) :=
    isQuasisimple_fixSub_of_equiv (Ψ.trans (MulEquiv.prodComm)) hres'
      (LocalCores.isQuasisimple_of_mulEquiv (CatalogueBSymplecticB.sesqUnitaryIsometryEquiv _).symm
        (CatalogueBAlternatingIsometry.isometry_quasisimple _ haltM hndM
          (CatalogueBSymplecticB.two_le_finrank_of_ne_bot hMne _ haltM hndM) hodd hMx))
  have hTP : ∀ v ∈ VPl A l, ∀ c, transvSp v c ∈ fixSub r K A (VMl A l) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenPlus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec, horth v hv w hw,
      zero_smul, smul_zero, add_zero]
  have hTM : ∀ v ∈ VMl A l, ∀ c, transvSp v c ∈ fixSub r K A (VPl A l) := by
    intro v hv c
    refine ⟨transvSp_mem_spCent hJA ((mem_eigenMinus hl0).1 hv) c, fun w hw => ?_⟩
    rw [coe_transvSp, add_mulVec, one_mulVec, smul_mulVec, transvN_mulVec,
      bilin_eq_zero_swap (B := pairedSympForm K r) pairedSympForm_isAlt (horth w hw v hv),
      zero_smul, smul_zero, add_zero]
  have hoddy := odd_orderOf_of_mem hRodd hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  obtain ⟨hτ, hPe⟩ := eigen_of_fix hqP hTP fun g hg => fix_of_spCent hinj hRodd hRi hRc rfl
    (fixSub_le A _)
    (fun f hf q hq => conj_mem_fixSub (fun g hg v hv => mulVec_mem_VMl hl0 hg hv) hf hq) hqP hy hg
  obtain ⟨-, hMe⟩ := eigen_of_fix hqM hTM fun g hg => fix_of_spCent hinj hRodd hRi hRc rfl
    (fixSub_le A _)
    (fun f hf q hq => conj_mem_fixSub (fun g hg v hv => mulVec_mem_VPl hl0 hg hv) hf hq) hqM hy hg
  rw [hτ hPne, map_one, mul_one] at hoddy ⊢
  exact splitSelf_conclude hK hr hAns hl0 hAA hJ hoddy hPe hMe

theorem skewSplit_core (hK : ringChar K ≠ 2) (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 4 ≤ Nat.card K)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut r K (stdSkewGsp r K) = conjAut r K (stdSkewGsp r K) * y)
    (hRc : ∀ s, conjAut r K (stdSkewGsp r K) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) {y} (hy : y ∈ R) :
    ∃ (D : gsp r K) (a b : K), y = conjAut r K D ∧
      ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        diagonal (Sum.elim (fun _ => a) fun _ => b) := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hoddy := odd_orderOf_of_mem hRodd hy
  have hyt := hRi y hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hq := isQuasisimple_leviSL_range hr hrq (K := K)
  have hfix : ∀ g ∈ (leviSL r K).range,
      (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => fix_of_spCent hinj hRodd hRi hRc rfl
      (by rintro _ ⟨x, rfl⟩; exact leviSL_mem_spCent x)
      (fun f hf q hq' => conj_mem_leviSL_range h2 hf hq') hq hy hg
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

theorem commute_skewSplit (hK : ringChar K ≠ 2) (hr : 2 ≤ r) (hrq : 3 ≤ r ∨ 4 ≤ Nat.card K)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    (hRodd : Odd (Nat.card R))
    (hRi : ∀ y ∈ R, y * conjAut r K (stdSkewGsp r K) = conjAut r K (stdSkewGsp r K) * y)
    (hRc : ∀ s, conjAut r K (stdSkewGsp r K) s = s → Odd (orderOf s) → ∀ y ∈ R,
      MulAut.conj s * y * (MulAut.conj s)⁻¹ ∈ R) :
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
  intro r₁ h₁ r₂ h₂
  obtain ⟨D, a, b, rfl, hD⟩ := skewSplit_core hK hr hrq hinj hRodd hRi hRc h₁
  obtain ⟨D', a', b', rfl, hD'⟩ := skewSplit_core hK hr hrq hinj hRodd hRi hRc h₂
  refine conjAut_commute ?_
  rw [hD, hD', diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  rcases x with x | x <;> simp [mul_comm]

end CFSG.ComponentClassification.Foote5.OddLieCore.ClSp
