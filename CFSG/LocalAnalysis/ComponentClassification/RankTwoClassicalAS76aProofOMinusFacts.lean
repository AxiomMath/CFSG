module

public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOChoice

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Forms

variable {K : Type} [Field K]

theorem statedQuadMinus_smul (n : ℕ) (b c : K) (d : K) (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    StatedQuadMinus n K b c (d • w) = d * d * StatedQuadMinus n K b c w := by
  rw [← coe_quadMinus, QuadraticMap.map_smul, smul_eq_mul]

@[expose] def minusVec (n : ℕ) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K :=
  Pi.single (.inr (.inr 0)) 1

theorem statedQuadMinus_minusVec (n : ℕ) (b c : K) :
    StatedQuadMinus n K b c (minusVec n) = 1 := by
  simp [StatedQuadMinus, minusVec]

theorem oProj_injective_minus [CharP K 2] (n : ℕ) (b c : K) :
    Function.Injective (oProj (StatedQuadMinus n K b c)) :=
  oProj_injective (v₀ := minusVec n) (by rw [statedQuadMinus_minusVec]; exact one_ne_zero)
    fun c' => statedQuadMinus_smul n b c c' _

theorem commutant_statedOmega_quadMinus [Finite K] (hK : 2 < Nat.card K) {n : ℕ} (hn : 2 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (Y : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K)
    (hY : ∀ Z ∈ StatedOmega (StatedQuadMinus n K b c),
      Y * (Z : Matrix _ _ K) = (Z : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
        (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K) * Y) :
    ∃ d : K, Y = d • 1 :=
  eq_smul_one_of_commute_statedOmega hK (quadMinus n K b c)
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) (by simp; omega)
    (by rw [coe_quadMinus]; exact hY)

theorem odd_card_center_statedOmega_quadMinus [Finite K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Odd (Nat.card (center (StatedOmega (StatedQuadMinus n K b c)))) := by
  rw [card_center_statedOmega_eq_one (center_statedOmega_quadMinus hn hirr)
    (oProj_injective_minus n b c)]
  exact odd_one

end Forms

section Derived

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def statedOmegaEquivCommutator (Q : QuadraticForm K (ι → K))
    {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) :
    StatedOmega Q₀ ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap hQ₀]
      exact map_comap_eq_self_of_surjective
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _))

theorem commutator_eq_top_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : commutator H = ⊤) : commutator G = ⊤ := by
  have h2 : commutator G = (commutator H).map e.symm.toMonoidHom := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  rw [h2, h, Subgroup.map_top_of_surjective _ e.symm.surjective]

theorem isQuasisimple_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hna : ¬ ∀ x y : G, x * y = y * x) : CFSG.IsQuasisimple G ∧ center G = ⊥ := by
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exact (hna fun x y => (mem_center_iff.mp (h ▸ mem_top y) x)).elim
  have hperf : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · refine (hna fun x y => ?_).elim
      have h1 : ⁅x, y⁆ = 1 := by
        rw [← mem_bot, ← h]
        exact commutator_mem_commutator (mem_top x) (mem_top y)
      rwa [commutatorElement_eq_one_iff_mul_comm] at h1
    · exact h
  have e : G ⧸ center G ≃* G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨⟨hperf⟩, e.isSimpleGroup, ?_⟩, hZ⟩
  push Not at hna
  obtain ⟨x, y, hxy⟩ := hna
  refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
  have := congrArg e h
  simpa using this

variable [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_ne_zero_of_finrank_eq_quadMinus {n : ℕ} (hn : 1 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Submodule K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))
    (hU : Module.finrank K U = Module.finrank K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) / 2) :
    ∃ u ∈ U, quadMinus n K b c u ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hn hirr ⟨U, ?_, hcon⟩
  rw [hU, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem isSimpleGroup_statedOmega_quadMinus_small {n : ℕ} (hn : n = 2 ∨ n = 3) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup (StatedOmega (StatedQuadMinus n K b c)) ∧
      commutator (StatedOmega (StatedQuadMinus n K b c)) = ⊤ ∧
      ¬ ∀ x y : StatedOmega (StatedQuadMinus n K b c), x * y = y * x := by
  obtain ⟨hs, hp, hna, -⟩ := CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
    (quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (by rw [Module.finrank_fintype_fun_eq_card]; simp; omega)
    (exists_ne_zero_of_finrank_eq_quadMinus (by omega) hirr)
  set e := statedOmegaEquivCommutator (quadMinus n K b c) (coe_quadMinus n K b c)
  have := hs
  refine ⟨e.isSimpleGroup, commutator_eq_top_of_mulEquiv e hp.commutator_eq_top,
    fun h => hna fun x y => e.symm.injective ?_⟩
  rw [map_mul, map_mul, h]

theorem nonempty_statedOmega_quadMinus_three_equiv {m : ℕ} (hK : Nat.card K = 2 ^ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ (E : Type) (_ : Field E) (_ : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 m E),
      Nonempty (StatedOmega (StatedQuadMinus 3 K b c) ≃* StatedSU 4 (2 ^ m) E) := by
  obtain ⟨-, -, -, -, -, -, h6⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (quadMinus 3 K b c) (nondegenerate_polarBilin_quadMinus_of_finite 3 K hirr)
      (by rw [Module.finrank_fintype_fun_eq_card]; simp)
      (exists_ne_zero_of_finrank_eq_quadMinus (by omega) hirr)
  obtain ⟨E, _, _, D, -, ρ, -, -, hinj, hrange, -⟩ :=
    h6 (by rw [Module.finrank_fintype_fun_eq_card]; simp)
  obtain ⟨f, h, hKf, hbar⟩ := D.exists_unitaryFieldData
  have hfm : f = m := Nat.pow_right_injective (le_refl 2) (hKf.symm.trans hK)
  subst hfm
  obtain ⟨θ⟩ := D.nonempty_sixSU_mulEquiv h hbar
  exact ⟨E, inferInstance, h, ⟨((statedOmegaEquivCommutator (quadMinus 3 K b c)
    (coe_quadMinus 3 K b c)).trans ((MulEquiv.subgroupCongr hrange.symm).trans
      (MonoidHom.ofInjective hinj).symm)).trans θ⟩⟩

theorem statedClassicalModel_psu_four {L : Type} [Group L] {m : ℕ} (hm : 2 ≤ m)
    (hK : Nat.card K = 2 ^ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ⧸ center L ≃* StatedOmega (StatedQuadMinus 3 K b c) ⧸
      center (StatedOmega (StatedQuadMinus 3 K b c))) :
    StatedClassicalModel (L ⧸ center L) .PSU 4 2 m := by
  obtain ⟨E, _, h, ⟨eSU⟩⟩ := nonempty_statedOmega_quadMinus_three_equiv hK hirr
  have hE := h.card_eq_sq
  have := h.finite
  have hnq : ((4 : ℕ), 2 ^ m) ≠ (3, 2) := by
    intro hc
    have := congrArg Prod.fst hc
    simp at this
  refine ⟨⟨Nat.prime_two, by omega, by norm_num, hnq⟩, E, inferInstance, h.finite, hE,
    ⟨(e.trans (QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq _))).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hE (by norm_num)
          hnq).2)⟩⟩

end Derived

section Swap

variable {K : Type} [Field K] [CharP K 2]

@[expose] def swapMinusMat : Matrix (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K :=
  (Equiv.swap (.inl 0) (.inr (.inl 0))).permMatrix K

omit [CharP K 2] in
theorem swapMinusMat_mul_self :
    (swapMinusMat : Matrix (Fin 1 ⊕ Fin 1 ⊕ Fin 2) (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K) * swapMinusMat =
      1 := by
  rw [swapMinusMat, ← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]

@[expose] def swapMinusGL : GL (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K :=
  ⟨swapMinusMat, swapMinusMat, swapMinusMat_mul_self, swapMinusMat_mul_self⟩

omit [CharP K 2] in
theorem swapMinusGL_mul_self :
    (swapMinusGL : GL (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K) * swapMinusGL = 1 :=
  Units.ext swapMinusMat_mul_self

omit [CharP K 2] in
theorem swapMinusMat_mulVec (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K) :
    swapMinusMat *ᵥ w = w ∘ Equiv.swap (.inl 0) (.inr (.inl 0)) := by
  rw [swapMinusMat, Matrix.permMatrix_mulVec]

omit [CharP K 2] in
theorem statedQuadMinus_swapMinusMat (b c : K) (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K) :
    StatedQuadMinus 2 K b c (((swapMinusGL : GL _ K) : Matrix _ _ K) *ᵥ w) =
      StatedQuadMinus 2 K b c w := by
  change StatedQuadMinus 2 K b c (swapMinusMat *ᵥ w) = _
  rw [swapMinusMat_mulVec]
  simp [StatedQuadMinus, Equiv.swap_apply_of_ne_of_ne, mul_comm]

theorem swapMinusGL_sub_one_mulVec (w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K) :
    (((swapMinusGL : GL (Fin 1 ⊕ Fin 1 ⊕ Fin 2) K) : Matrix _ _ K) - 1) *ᵥ w =
      (fun w : Fin 1 ⊕ Fin 1 ⊕ Fin 2 → K => w (.inl 0) + w (.inr (.inl 0))) w •
        (Pi.single (Sum.inl 0 : Fin 1 ⊕ Fin 1 ⊕ Fin 2) (1 : K) + Pi.single (.inr (.inl 0)) 1) := by
  change (swapMinusMat - 1) *ᵥ w = _
  rw [sub_mulVec, swapMinusMat_mulVec, one_mulVec]
  funext i
  rcases i with i | i | i <;> fin_cases i <;>
    simp [Equiv.swap_apply_of_ne_of_ne, CharTwo.sub_eq_add, add_comm]

end Swap

end CFSG.ComponentClassification.RankTwoClassical
