module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpMinor
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpField

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedCatalog

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher CatalogueBSymplecticB
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

namespace SpChain

variable {K : Type} [Field K]

abbrev stdIdx : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv

@[expose] def antiIdx : Fin 2 ⊕ Fin 2 ≃ Fin 4 := stdIdx.trans (Equiv.swap 2 3)

theorem antiIdx_inl_zero : antiIdx (Sum.inl 0) = 0 := rfl
theorem antiIdx_inl_one : antiIdx (Sum.inl 1) = 1 := rfl
theorem antiIdx_inr_zero : antiIdx (Sum.inr 0) = 3 := rfl
theorem antiIdx_inr_one : antiIdx (Sum.inr 1) = 2 := rfl
theorem antiIdx_symm_zero : antiIdx.symm 0 = Sum.inl 0 := rfl
theorem antiIdx_symm_one : antiIdx.symm 1 = Sum.inl 1 := rfl
theorem antiIdx_symm_two : antiIdx.symm 2 = Sum.inr 1 := rfl
theorem antiIdx_symm_three : antiIdx.symm 3 = Sum.inr 0 := rfl

variable (K) in
@[expose] def swapC : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => if Equiv.swap (2 : Fin 4) 3 i = j then 1 else 0

theorem swapC_mul_apply (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (swapC K * M) i j = M (Equiv.swap 2 3 i) j := by
  simp [mul_apply, swapC]

theorem mul_swapC_apply (M : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (M * swapC K) i j = M i (Equiv.swap 2 3 j) := by
  simp only [mul_apply, swapC, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (Equiv.swap 2 3 j)]
  · simp
  · intro b _ hb
    have hb' : Equiv.swap (2 : Fin 4) 3 b ≠ j := fun h => hb (by rw [← h, Equiv.swap_apply_self])
    simp [hb']
  · simp

theorem swapC_mul_swapC : swapC K * swapC K = 1 := by
  ext i j
  rw [swapC_mul_apply]
  simp only [swapC, of_apply, Equiv.swap_apply_self, one_apply]

theorem swapC_inv : (swapC K)⁻¹ = swapC K :=
  Matrix.inv_eq_left_inv swapC_mul_swapC

theorem reindex_swapC_conj (M : Matrix (Fin 4) (Fin 4) K) :
    Matrix.reindex stdIdx.symm stdIdx.symm (swapC K * M * (swapC K)⁻¹) =
      M.submatrix antiIdx antiIdx := by
  ext p q
  rw [swapC_inv, reindex_apply, submatrix_apply, submatrix_apply, mul_swapC_apply,
    swapC_mul_apply]
  rfl

theorem swapC_conj_reindex (N : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    (swapC K)⁻¹ * Matrix.reindex stdIdx stdIdx N * swapC K =
      N.submatrix antiIdx.symm antiIdx.symm := by
  ext x y
  rw [swapC_inv, mul_swapC_apply, swapC_mul_apply, reindex_apply, submatrix_apply,
    submatrix_apply]
  rfl

theorem minorJ_submatrix [CharP K 2] :
    (minorJ K).submatrix antiIdx antiIdx = fromBlocks 0 1 (-1) 0 := by
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [minorJ_apply, h1, antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one]

@[expose] def antiToStd : GL (Fin 4) K ≃* GL (Fin 2 ⊕ Fin 2) K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K antiIdx.symm).toMulEquiv

theorem coe_antiToStd (g : GL (Fin 4) K) :
    ((antiToStd g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (glMat g).submatrix antiIdx antiIdx :=
  rfl

theorem coe_antiToStd_symm (g : GL (Fin 2 ⊕ Fin 2) K) :
    glMat (antiToStd.symm g) =
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K).submatrix antiIdx.symm antiIdx.symm :=
  rfl

theorem mem_antiSp_iff_antiToStd [CharP K 2] (g : GL (Fin 4) K) :
    g ∈ antiSp K ↔ antiToStd g ∈ StatedSp 2 K := by
  rw [mem_antiSp, SymplecticTorusWeyl.mem_statedSp_iff, coe_antiToStd, ← minorJ_submatrix,
    transpose_submatrix, submatrix_mul_equiv _ _ _ antiIdx _,
    submatrix_mul_equiv _ _ _ antiIdx _]
  constructor
  · intro h
    rw [h]
  · intro h
    have h1 := congrArg (fun M => Matrix.submatrix M antiIdx.symm antiIdx.symm) h
    simpa [Matrix.submatrix_submatrix] using h1

theorem map_antiToStd_antiSp [CharP K 2] :
    (antiSp K).map (antiToStd : GL (Fin 4) K ≃* GL (Fin 2 ⊕ Fin 2) K).toMonoidHom =
      StatedSp 2 K := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_antiSp_iff_antiToStd, MulEquiv.apply_symm_apply]

variable (K) in
@[expose] def antiSpEquiv [CharP K 2] : antiSp K ≃* StatedSp 2 K :=
  ((antiToStd : GL (Fin 4) K ≃* GL (Fin 2 ⊕ Fin 2) K).subgroupMap (antiSp K)).trans
    (MulEquiv.subgroupCongr map_antiToStd_antiSp)

theorem spMat_antiSpEquiv [CharP K 2] (g : antiSp K) :
    spMat (antiSpEquiv K g) = (glMat g).submatrix antiIdx antiIdx :=
  rfl

theorem spMat_antiSpEquiv_eq_conj [CharP K 2] (g : antiSp K) :
    spMat (antiSpEquiv K g) =
      Matrix.reindex stdIdx.symm stdIdx.symm (swapC K * glMat g * (swapC K)⁻¹) := by
  rw [spMat_antiSpEquiv, reindex_swapC_conj]

theorem glMat_antiSpEquiv_symm [CharP K 2] (g : StatedSp 2 K) :
    glMat ((antiSpEquiv K).symm g : GL (Fin 4) K) =
      (spMat g).submatrix antiIdx.symm antiIdx.symm := by
  have h1 := congrArg spMat ((antiSpEquiv K).apply_symm_apply g)
  rw [spMat_antiSpEquiv] at h1
  rw [← h1, Matrix.submatrix_submatrix]
  simp

variable (K) in
@[expose] def exceptionalSpAut [CharP K 2] [Finite K] : MulAut (StatedSp 2 K) :=
  ((antiSpEquiv K).symm.trans (minorAut K)).trans (antiSpEquiv K)

theorem spMat_exceptionalSpAut' [CharP K 2] [Finite K] (g : StatedSp 2 K) :
    spMat (exceptionalSpAut K g) =
      (minorMap ((spMat g).submatrix antiIdx.symm antiIdx.symm)).submatrix antiIdx antiIdx := by
  change spMat (antiSpEquiv K (minorAut K ((antiSpEquiv K).symm g))) = _
  rw [spMat_antiSpEquiv, glMat_minorAut, glMat_antiSpEquiv_symm]

theorem spMat_exceptionalSpAut [CharP K 2] [Finite K] (g : StatedSp 2 K) :
    spMat (exceptionalSpAut K g) = Matrix.reindex stdIdx.symm stdIdx.symm (swapC K *
      minorMap ((swapC K)⁻¹ * Matrix.reindex stdIdx stdIdx (spMat g) * swapC K) *
        (swapC K)⁻¹) := by
  rw [reindex_swapC_conj, swapC_conj_reindex, spMat_exceptionalSpAut']

theorem antiSpEquiv_frobHom [CharP K 2] {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2)
    (h : antiSp K) : antiSpEquiv K (frobHom K h) = fieldSp 2 K Fr (antiSpEquiv K h) := by
  refine Subtype.ext (Units.ext ?_)
  change spMat (antiSpEquiv K (frobHom K h)) = (spMat (antiSpEquiv K h)).map Fr
  rw [spMat_antiSpEquiv, glMat_frobHom, spMat_antiSpEquiv]
  ext p q
  simp [hFr]

theorem exceptionalSpAut_sq [CharP K 2] [Finite K] {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2)
    (g : StatedSp 2 K) : exceptionalSpAut K (exceptionalSpAut K g) = fieldSp 2 K Fr g := by
  change antiSpEquiv K (minorAut K ((antiSpEquiv K).symm (antiSpEquiv K
    (minorAut K ((antiSpEquiv K).symm g))))) = _
  rw [MulEquiv.symm_apply_apply]
  change antiSpEquiv K (minorHom K (minorHom K _)) = _
  rw [minorHom_minorHom, antiSpEquiv_frobHom hFr, MulEquiv.apply_symm_apply]

variable (K) in
@[expose] def projSpEquiv [CharP K 2] : StatedSp 2 K ≃* StatedProj (StatedSp 2 K) :=
  MulEquiv.ofBijective (proj 2 K) UnitaryHigher.proj_bijective_of_charTwo

variable (K) in
@[expose] def exceptionalAut [CharP K 2] [Finite K] : MulAut (StatedProj (StatedSp 2 K)) :=
  MulAut.congr (projSpEquiv K) (exceptionalSpAut K)

theorem exceptionalAut_proj [CharP K 2] [Finite K] (g : StatedSp 2 K) :
    exceptionalAut K (proj 2 K g) = proj 2 K (exceptionalSpAut K g) := by
  change projSpEquiv K (exceptionalSpAut K ((projSpEquiv K).symm (projSpEquiv K g))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem eq_exceptionalAut [CharP K 2] [Finite K] {γ : MulAut (StatedProj (StatedSp 2 K))}
    (hγ : ∀ g : StatedSp 2 K, γ (proj 2 K g) = proj 2 K (exceptionalSpAut K g)) :
    γ = exceptionalAut K := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [hγ, exceptionalAut_proj]

theorem exceptionalAut_sq [CharP K 2] [Finite K] {Fr : K ≃+* K} (hFr : ∀ x, Fr x = x ^ 2) :
    exceptionalAut K ^ 2 = fieldAut 2 K Fr := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [sq, MulAut.mul_apply, exceptionalAut_proj, exceptionalAut_proj, exceptionalSpAut_sq hFr,
    fieldAut_proj]

theorem exceptionalAut_mul_spInner [CharP K 2] [Finite K] (g : StatedSp 2 K) :
    exceptionalAut K * spInner 2 K g = spInner 2 K (exceptionalSpAut K g) * exceptionalAut K := by
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, spInner_eq_conj, spInner_eq_conj, MulAut.conj_apply,
    MulAut.conj_apply, map_mul, map_mul, map_inv, exceptionalAut_proj]

@[expose] def DisplacementInLine {n : Type*} [Fintype n] (M : Matrix n n K) : Prop :=
  ∃ u : n → K, ∀ v, M *ᵥ v - v ∈ K ∙ u

theorem displacementInLine_conj {r : ℕ} (g s : StatedSp r K) (φ : K ≃+* K)
    (h : DisplacementInLine (spMat s)) :
    DisplacementInLine (spMat (g * fieldSp r K φ s * g⁻¹)) := by
  obtain ⟨u, hu⟩ := h
  set T := semilinearCoordMap (g : GL (Fin r ⊕ Fin r) K) φ with hTdef
  refine ⟨T u, fun v => ?_⟩
  rw [spMat_conj_mulVec]
  have h1 : T (spMat s *ᵥ T.symm v) - v = T (spMat s *ᵥ T.symm v - T.symm v) := by
    rw [map_sub, AddEquiv.apply_symm_apply]
  rw [h1]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hu (T.symm v))
  rw [← hc, hTdef, semilinearCoordMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem spInner_mul_fieldAut_proj {r : ℕ} (g s : StatedSp r K) (φ : K ≃+* K) :
    (spInner r K g * fieldAut r K φ) (proj r K s) = proj r K (g * fieldSp r K φ s * g⁻¹) := by
  rw [MulAut.mul_apply, fieldAut_proj, spInner_apply, conjAut_proj]
  rfl

theorem transpose_single_zero_zero :
    (single (0 : Fin 2) (0 : Fin 2) (1 : K))ᵀ = single 0 0 1 := by
  rw [transpose_single]

theorem transpose_single_swap :
    (single (0 : Fin 2) (1 : Fin 2) (1 : K) + single 1 0 1)ᵀ = single 0 1 1 + single 1 0 1 := by
  rw [transpose_add, transpose_single, transpose_single, add_comm]

theorem upperUnipotentSp_mulVec_sub {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C)
    (v : Fin 2 ⊕ Fin 2 → K) :
    spMat (upperUnipotentSp 2 K hC) *ᵥ v - v = Sum.elim (C *ᵥ (v ∘ Sum.inr)) 0 := by
  rw [spMat, coe_upperUnipotentSp, fromBlocks_mulVec, one_mulVec, one_mulVec, zero_mulVec,
    zero_add]
  funext x
  rcases x with i | i
  · simp only [Pi.sub_apply, Sum.elim_inl, Pi.add_apply, Function.comp_apply,
      add_sub_cancel_left]
  · simp only [Pi.sub_apply, Sum.elim_inr, Function.comp_apply, sub_self, Pi.zero_apply]

theorem displacementInLine_upperUnipotent :
    DisplacementInLine (spMat (upperUnipotentSp 2 K (transpose_single_zero_zero (K := K)))) := by
  refine ⟨Pi.single (Sum.inl 0) 1, fun v => Submodule.mem_span_singleton.mpr
    ⟨v (Sum.inr 0), ?_⟩⟩
  rw [upperUnipotentSp_mulVec_sub, single_mulVec]
  funext x
  rcases x with i | i <;> fin_cases i <;> simp

theorem exceptionalSpAut_upperUnipotent [CharP K 2] [Finite K] :
    exceptionalSpAut K (upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))) =
      upperUnipotentSp 2 K (transpose_single_swap (K := K)) := by
  have h1 : (-1 : K) = 1 := CharTwo.neg_eq 1
  refine Subtype.ext (Units.ext ?_)
  change spMat (exceptionalSpAut K _) = spMat (upperUnipotentSp 2 K _)
  rw [spMat_exceptionalSpAut']
  ext p q
  rcases p with p | p <;> rcases q with q | q <;> fin_cases p <;> fin_cases q <;>
    simp [spMat, coe_upperUnipotentSp, minorMap_apply, minorIdx_zero, minorIdx_one, minorIdx_two,
      minorIdx_three, antiIdx_inl_zero, antiIdx_inl_one, antiIdx_inr_zero, antiIdx_inr_one,
      antiIdx_symm_zero, antiIdx_symm_one, antiIdx_symm_two, antiIdx_symm_three, h1]

theorem not_displacementInLine_upperUnipotent_swap :
    ¬ DisplacementInLine (spMat (upperUnipotentSp 2 K (transpose_single_swap (K := K)))) := by
  rintro ⟨u, hu⟩
  have hd : ∀ v : Fin 2 ⊕ Fin 2 → K,
      spMat (upperUnipotentSp 2 K (transpose_single_swap (K := K))) *ᵥ v - v =
        v (Sum.inr 1) • Pi.single (Sum.inl 0) 1 + v (Sum.inr 0) • Pi.single (Sum.inl 1) 1 := by
    intro v
    rw [upperUnipotentSp_mulVec_sub, add_mulVec, single_mulVec, single_mulVec]
    funext x
    rcases x with i | i <;> fin_cases i <;> simp
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hu (Pi.single (Sum.inr 1) 1))
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hu (Pi.single (Sum.inr 0) 1))
  rw [hd] at ha hb
  have ha0 : a * u (Sum.inl 0) = 1 := by
    have h1 := congrFun ha (Sum.inl 0)
    simpa using h1
  have hb0 : b * u (Sum.inl 0) = 0 := by
    have h1 := congrFun hb (Sum.inl 0)
    simpa using h1
  have hb1 : b * u (Sum.inl 1) = 1 := by
    have h1 := congrFun hb (Sum.inl 1)
    simpa using h1
  have hu0 : u (Sum.inl 0) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at ha0
    exact zero_ne_one ha0
  have hb' : b = 0 := (mul_eq_zero.mp hb0).resolve_right hu0
  rw [hb', zero_mul] at hb1
  exact zero_ne_one hb1

theorem exceptionalAut_not_mem [CharP K 2] [Finite K] :
    exceptionalAut K ∉ spSemilinearAutGroup 2 K := by
  intro hγ
  obtain ⟨g, φ, hgφ⟩ := exists_eq_spInner_mul_fieldAut hγ
  set t₀ := upperUnipotentSp 2 K (transpose_single_zero_zero (K := K))
  have h1 := exceptionalAut_proj (K := K) t₀
  rw [hgφ, spInner_mul_fieldAut_proj] at h1
  have h2 := UnitaryHigher.proj_bijective_of_charTwo.1 h1
  have h3 := displacementInLine_conj g t₀ φ displacementInLine_upperUnipotent
  rw [h2, exceptionalSpAut_upperUnipotent] at h3
  exact not_displacementInLine_upperUnipotent_swap h3

theorem exceptionalAut_structure [CharP K 2] [Finite K] {f : ℕ} (hf : 1 ≤ f) {Fr : K ≃+* K}
    (hFr : ∀ x, Fr x = x ^ 2) (hord : orderOf Fr = f) (hzp : Subgroup.zpowers Fr = ⊤) :
    orderOf (exceptionalAut K) = 2 * f ∧
    (∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃! p : StatedSp 2 K × Fin (2 * f),
      α = spInner 2 K p.1 * exceptionalAut K ^ (p.2 : ℕ)) ∧
    inner (StatedProj (StatedSp 2 K)) ⊓ Subgroup.zpowers (exceptionalAut K) = ⊥ ∧
    inner (StatedProj (StatedSp 2 K)) ⊔ Subgroup.zpowers (exceptionalAut K) = ⊤ ∧
    IsCyclic (Outer (StatedProj (StatedSp 2 K))) ∧
    Nat.card (Outer (StatedProj (StatedSp 2 K))) = 2 * f ∧
    spSemilinearAutGroup 2 K =
      inner (StatedProj (StatedSp 2 K)) ⊔ Subgroup.zpowers (exceptionalAut K ^ 2) ∧
    inner (StatedProj (StatedSp 2 K)) ⊓ Subgroup.zpowers (exceptionalAut K ^ 2) = ⊥ ∧
    (∀ n : ℕ, exceptionalAut K ^ n ∈ inner (StatedProj (StatedSp 2 K)) ↔ 2 * f ∣ n) ∧
    ∀ α : MulAut (StatedProj (StatedSp 2 K)), orderOf α = 2 →
      ∃ (g : StatedSp 2 K) (j : ℕ), (j = 0 ∨ j = f) ∧ α = spInner 2 K g * exceptionalAut K ^ j := by
  set γ := exceptionalAut K with hγdef
  set E := spSemilinearAutGroup 2 K with hEdef
  set I := inner (StatedProj (StatedSp 2 K)) with hIdef
  have hγ2 : γ ^ 2 = fieldAut 2 K Fr := exceptionalAut_sq hFr
  have hγ2m : ∀ m : ℕ, γ ^ (2 * m) = fieldAut 2 K (Fr ^ m) := fun m => by
    rw [pow_mul, hγ2, map_pow]
  have hγE : γ ∉ E := exceptionalAut_not_mem
  have hIE : I ≤ E := inner_le_spSemilinearAutGroup
  have hFrfin : IsOfFinOrder Fr := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hEform : ∀ α ∈ E, ∃ (g : StatedSp 2 K) (m : ℕ), m < f ∧
      α = spInner 2 K g * γ ^ (2 * m) := by
    intro α hα
    obtain ⟨g, φ, rfl⟩ := exists_eq_spInner_mul_fieldAut hα
    obtain ⟨m', hm'⟩ := (Submonoid.mem_powers_iff _ _).mp
      (hFrfin.mem_powers_iff_mem_zpowers.mpr (hzp ▸ Subgroup.mem_top φ))
    refine ⟨g, m' % f, Nat.mod_lt _ (by omega), ?_⟩
    rw [hγ2m, ← hord, pow_mod_orderOf, hm']
  obtain ⟨-, -, -, hEi⟩ :=
    CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := K)
  have hEidx : E.index = 2 := by
    have hEi' : E.index ≤ 2 := hEi
    have h0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : E.index ≠ 1 := by
      intro h
      apply hγE
      rw [Subgroup.index_eq_one.mp h]
      exact Subgroup.mem_top γ
    omega
  have hall : ∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃ (g : StatedSp 2 K) (j : ℕ),
      j < 2 * f ∧ α = spInner 2 K g * γ ^ j := by
    intro α
    by_cases hα : α ∈ E
    · obtain ⟨g, m, hm, rfl⟩ := hEform α hα
      exact ⟨g, 2 * m, by omega, rfl⟩
    · have h1 : γ⁻¹ * α ∈ E := (Subgroup.mul_mem_iff_of_index_two hEidx).mpr
        ⟨fun h => absurd (by simpa using inv_mem h) hγE, fun h => absurd h hα⟩
      obtain ⟨g, m, hm, hgm⟩ := hEform _ h1
      refine ⟨exceptionalSpAut K g, 2 * m + 1, by omega, ?_⟩
      calc α = γ * (γ⁻¹ * α) := by group
        _ = γ * (spInner 2 K g * γ ^ (2 * m)) := by rw [hgm]
        _ = spInner 2 K (exceptionalSpAut K g) * γ ^ (2 * m + 1) := by
          rw [← mul_assoc, hγdef, exceptionalAut_mul_spInner, mul_assoc, pow_succ']
  have hpowI : ∀ n : ℕ, γ ^ n ∈ I ↔ 2 * f ∣ n := by
    intro n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [hγ2m]
      have h1 := spInner_mul_fieldAut_not_mem_inner_iff (1 : StatedSp 2 K) (Fr ^ m)
      rw [map_one, one_mul] at h1
      constructor
      · intro hI
        have h2 : Fr ^ m = 1 := by
          by_contra h
          exact h1.mpr h hI
        have h3 := orderOf_dvd_of_pow_eq_one h2
        rw [hord] at h3
        exact Nat.mul_dvd_mul_left 2 h3
      · intro hdvd
        have h3 : f ∣ m := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
        rw [← hord] at h3
        rw [orderOf_dvd_iff_pow_eq_one.mp h3, map_one]
        exact one_mem _
    · constructor
      · intro hI
        exfalso
        apply hγE
        have h1 : γ = γ ^ (2 * m + 1) * (γ ^ (2 * m))⁻¹ := by group
        rw [h1]
        exact mul_mem (hIE hI) (inv_mem (by rw [hγ2m]; exact fieldAut_mem_spSemilinearAutGroup _))
      · intro hdvd
        exfalso
        have h2 : 2 ∣ 2 * m + 1 := (Dvd.intro f rfl).trans hdvd
        omega
  have hγord : orderOf γ = 2 * f := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨?_, fun m hm hm0 h1 => ?_⟩
    · rw [hγ2m, ← hord, pow_orderOf_eq_one, map_one]
    · have h2 := (hpowI m).mp (h1 ▸ one_mem I)
      exact absurd (Nat.le_of_dvd hm0 h2) (by omega)
  have huniq : ∀ (g h : StatedSp 2 K) (j k : ℕ), j < 2 * f → k < 2 * f →
      spInner 2 K g * γ ^ j = spInner 2 K h * γ ^ k → g = h ∧ j = k := by
    have key : ∀ (g h : StatedSp 2 K) (j k : ℕ), k ≤ j → j < 2 * f →
        spInner 2 K g * γ ^ j = spInner 2 K h * γ ^ k → j = k := by
      intro g h j k hkj hj he
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
      have h1 : γ ^ d = spInner 2 K (g⁻¹ * h) := by
        rw [map_mul, map_inv]
        calc γ ^ d = (spInner 2 K g)⁻¹ * (spInner 2 K g * γ ^ (k + d)) * (γ ^ k)⁻¹ := by group
          _ = (spInner 2 K g)⁻¹ * (spInner 2 K h * γ ^ k) * (γ ^ k)⁻¹ := by rw [he]
          _ = (spInner 2 K g)⁻¹ * spInner 2 K h := by group
      have h2 := (hpowI d).mp (h1 ▸ spInner_mem_inner _)
      rcases Nat.eq_zero_or_pos d with hd | hd
      · omega
      · exact absurd (Nat.le_of_dvd hd h2) (by omega)
    intro g h j k hj hk he
    have hjk : j = k := by
      rcases le_total k j with hkj | hjk
      · exact key g h j k hkj hj he
      · exact (key h g k j hjk hk he.symm).symm
    subst hjk
    exact ⟨(spInner_injective (r := 2) (K := K)) (mul_right_cancel he), rfl⟩
  have hinf : I ⊓ Subgroup.zpowers γ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxI, hxz⟩
    have hγfin : IsOfFinOrder γ := orderOf_pos_iff.mp (by rw [hγord]; omega)
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
      (hγfin.mem_powers_iff_mem_zpowers.mpr hxz)
    rw [Subgroup.mem_bot]
    have h1 := (hpowI n).mp hxI
    rw [← hγord] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hsup : I ⊔ Subgroup.zpowers γ = ⊤ := by
    rw [eq_top_iff]
    intro α _
    obtain ⟨g, j, -, rfl⟩ := hall α
    exact mul_mem (Subgroup.mem_sup_left (spInner_mem_inner g))
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers γ) j))
  set γbar : Outer (StatedProj (StatedSp 2 K)) := QuotientGroup.mk γ with hγbar
  have hmk : ∀ (g : StatedSp 2 K) (j : ℕ),
      (QuotientGroup.mk (spInner 2 K g * γ ^ j) : Outer (StatedProj (StatedSp 2 K))) =
        γbar ^ j := by
    intro g j
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (spInner_mem_inner g), one_mul,
      QuotientGroup.mk_pow]
  have hzpOut : Subgroup.zpowers γbar = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, j, -, rfl⟩ := hall α
    rw [hmk]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j
  have hγbar_pow : ∀ n : ℕ, γbar ^ n = 1 ↔ 2 * f ∣ n := by
    intro n
    rw [hγbar, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hpowI]
  have hordbar : orderOf γbar = 2 * f := by
    rw [orderOf_eq_iff (by omega)]
    refine ⟨(hγbar_pow _).mpr dvd_rfl, fun m hm hm0 h1 => ?_⟩
    exact absurd (Nat.le_of_dvd hm0 ((hγbar_pow m).mp h1)) (by omega)
  have hcardOut : Nat.card (Outer (StatedProj (StatedSp 2 K))) = 2 * f := by
    rw [← Subgroup.card_top (G := Outer (StatedProj (StatedSp 2 K))), ← hzpOut,
      Nat.card_zpowers, hordbar]
  have hEsup : E = I ⊔ Subgroup.zpowers (γ ^ 2) := by
    apply le_antisymm
    · intro α hα
      obtain ⟨g, m, -, rfl⟩ := hEform α hα
      rw [pow_mul]
      exact mul_mem (Subgroup.mem_sup_left (spInner_mem_inner g))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) m))
    · refine sup_le hIE ?_
      rw [Subgroup.zpowers_le, hγ2]
      exact fieldAut_mem_spSemilinearAutGroup Fr
  have hinf2 : I ⊓ Subgroup.zpowers (γ ^ 2) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    exact inf_le_inf_left _ (Subgroup.zpowers_le.mpr
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers γ) 2))
  have hinvol : ∀ α : MulAut (StatedProj (StatedSp 2 K)), orderOf α = 2 →
      ∃ (g : StatedSp 2 K) (j : ℕ), (j = 0 ∨ j = f) ∧ α = spInner 2 K g * γ ^ j := by
    intro α hα
    obtain ⟨g, j, hj, rfl⟩ := hall α
    have hsq := pow_orderOf_eq_one (spInner 2 K g * γ ^ j)
    rw [hα] at hsq
    have h1 : (QuotientGroup.mk (spInner 2 K g * γ ^ j) :
        Outer (StatedProj (StatedSp 2 K))) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]
    rw [hmk, ← pow_mul, hγbar_pow] at h1
    obtain ⟨c, hc⟩ := h1
    have hj' : j = f * c := by linarith
    refine ⟨g, j, ?_, rfl⟩
    rcases c with _ | _ | c
    · left
      simpa using hj'
    · right
      simpa using hj'
    · exfalso
      nlinarith
  refine ⟨hγord, fun α => ?_, hinf, hsup, isCyclic_iff_exists_zpowers_eq_top.mpr ⟨γbar, hzpOut⟩,
    hcardOut, hEsup, hinf2, hpowI, hinvol⟩
  obtain ⟨g, j, hj, hα⟩ := hall α
  refine ⟨(g, ⟨j, hj⟩), hα, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := huniq g p.1 j p.2 hj p.2.2 (hα.symm.trans hp)
  exact Prod.ext h1.symm (Fin.ext h2.symm)

end SpChain

open SpChain

theorem even_symplectic_two_exterior_square_automorphism {f : ℕ} (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) :
    (∀ g ∈ antiSp K, CFSG.LinearAlgebra.exteriorSquareMinor
      (CFSG.LinearAlgebra.exteriorSquareMinor (glMat g)) = (glMat g).map fun x => x ^ 2) ∧
    (∃ α : MulAut (antiSp K), ∀ g, glMat (α g : GL (Fin 4) K) =
      CFSG.LinearAlgebra.exteriorSquareMinor (glMat g)) ∧
    (∃ ψ : antiSp K ≃* StatedSp 2 K, ∀ g, spMat (ψ g) =
      Matrix.reindex stdIdx.symm stdIdx.symm (swapC K * glMat g * (swapC K)⁻¹)) ∧
    (∀ g : StatedSp 2 K, spMat (exceptionalSpAut K g) =
      Matrix.reindex stdIdx.symm stdIdx.symm (swapC K *
        CFSG.LinearAlgebra.exteriorSquareMinor
          ((swapC K)⁻¹ * Matrix.reindex stdIdx stdIdx (spMat g) * swapC K) *
          (swapC K)⁻¹)) ∧
    (∃ γ : MulAut (StatedProj (StatedSp 2 K)), ∀ g : StatedSp 2 K,
      γ (proj 2 K g) = proj 2 K (exceptionalSpAut K g)) ∧
    ∀ γ : MulAut (StatedProj (StatedSp 2 K)), (∀ g : StatedSp 2 K,
        γ (proj 2 K g) = proj 2 K (exceptionalSpAut K g)) →
      (∀ Fr : K ≃+* K, (∀ x, Fr x = x ^ 2) → γ ^ 2 = fieldAut 2 K Fr) ∧
      orderOf γ = 2 * f ∧ γ ∉ spSemilinearAutGroup 2 K ∧
      (∀ α : MulAut (StatedProj (StatedSp 2 K)), ∃! p : StatedSp 2 K × Fin (2 * f),
        α = spInner 2 K p.1 * γ ^ (p.2 : ℕ)) ∧
      OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊓ Subgroup.zpowers γ = ⊥ ∧
      OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊔ Subgroup.zpowers γ = ⊤ ∧
      IsCyclic (Outer (StatedProj (StatedSp 2 K))) ∧
      Nat.card (Outer (StatedProj (StatedSp 2 K))) = 2 * f ∧
      spSemilinearAutGroup 2 K =
        OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊔ Subgroup.zpowers (γ ^ 2) ∧
      OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) ⊓ Subgroup.zpowers (γ ^ 2) = ⊥ ∧
      (Even f → ∀ α : MulAut (StatedProj (StatedSp 2 K)), orderOf α = 2 →
        α ∈ spSemilinearAutGroup 2 K) ∧
      (Odd f → ∀ α : MulAut (StatedProj (StatedSp 2 K)), orderOf α = 2 →
        α ∉ OuterAutomorphisms.inner (StatedProj (StatedSp 2 K)) →
          ∃ g : StatedSp 2 K, α = spInner 2 K g * γ ^ f) := by
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  refine ⟨fun g hg => ?_, ⟨minorAut K, fun _ => rfl⟩, ⟨antiSpEquiv K, spMat_antiSpEquiv_eq_conj⟩,
    spMat_exceptionalSpAut, ⟨exceptionalAut K, exceptionalAut_proj⟩, fun γ hγ => ?_⟩
  · have h1 := congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K))
      (minorHom_minorHom (⟨g, hg⟩ : antiSp K))
    simpa only [glMat_minorHom, glMat_frobHom] using h1
  obtain rfl := eq_exceptionalAut hγ
  obtain ⟨hγord, huniq, hinf, hsup, hcyc, hcard, hEsup, hinf2, -, hinvol⟩ :=
    exceptionalAut_structure hf hFr hord hzp
  refine ⟨fun Fr' hFr' => exceptionalAut_sq hFr', hγord, exceptionalAut_not_mem, huniq, hinf,
    hsup, hcyc, hcard, hEsup, hinf2, fun hfe α hα => ?_, fun hfo α hα hαI => ?_⟩
  · obtain ⟨g, j, hj, rfl⟩ := hinvol α hα
    obtain ⟨m, hm⟩ := hfe
    have hj2 : ∃ k, j = 2 * k := by
      rcases hj with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨m, by omega⟩
    obtain ⟨k, rfl⟩ := hj2
    rw [pow_mul, exceptionalAut_sq hFr, ← map_pow]
    exact mul_mem (spInner_mem_spSemilinearAutGroup g) (fieldAut_mem_spSemilinearAutGroup _)
  · obtain ⟨g, j, hj, rfl⟩ := hinvol α hα
    rcases hj with rfl | rfl
    · exact absurd (by rw [pow_zero, mul_one]; exact spInner_mem_inner g) hαI
    · exact ⟨g, rfl⟩

end CFSG.ComponentClassification.UnbalancedCatalog
