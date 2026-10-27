module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTAbs
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLinear
public import CFSG.ClassicalInvolution.ModelFacts.Models
public import CFSG.ClassicalInvolution.RouteD.TypeABridge
public import CFSG.ClassicalInvolution.WeakCT.Center
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.CGT.PushingUpLit.SolK.Inputs
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieRanges
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieTable3
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.AscThmABasic
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3CPSix67
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.ModelFacts (negBlockK negBlockK_eq_diagonal commute_longRootGroup_neg
  range_blockSL_eq_longRootGroupK)

namespace LTSL

section Matrices

variable {F : Type} [Field F]

theorem rootInv_mul_self {n : ℕ} (hn : 2 ≤ n) : rootInv F hn * rootInv F hn = 1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv, negBlock_mul_self,
      Matrix.SpecialLinearGroup.coe_one])

theorem rootInv_ne_one (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 2 ≤ n) : rootInv F hn ≠ 1 := fun h => by
  have := (isClassicalSL2_rootSL2 h2 hn).orderOf_eq_two
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem negBlock_zero_eq_diagonal (n : ℕ) :
    negBlock F n 0 = Matrix.diagonal (fun a : Fin n => if a.val < 2 then (-1 : F) else 1) := by
  rw [negBlock_eq_diagonal]
  congr 1
  funext a
  simp

@[expose] def swap4 : SL(4, F) :=
  ⟨!![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0], by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]⟩

theorem coe_swap4 : ((swap4 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] := rfl

theorem swap4_mul_self : swap4 * swap4 = (1 : SL(4, F)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_swap4, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_four] <;> simp

theorem swap4_inv : (swap4 : SL(4, F))⁻¹ = swap4 := inv_eq_of_mul_eq_one_right swap4_mul_self

theorem swap4_conj_negBlock :
    ((swap4 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * negBlock F 4 0 *
      ((swap4 : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = -negBlock F 4 0 := by
  rw [negBlock_zero_eq_diagonal, coe_swap4]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_four] <;> simp

theorem swap4_comm (h2 : (2 : F) ≠ 0) (hn : 2 ≤ 4) :
    ∀ a ∈ rootSL2 F hn, ∀ b ∈ rootSL2 F hn, Commute (swap4 * a * swap4⁻¹) b := by
  intro a ha b hb
  rw [rootSL2_eq_longRootGroup h2 hn] at ha hb
  have h1 := conj_mem_longRootGroup_conj (swap4 : SL(4, F)) ha
  rw [swap4_inv, swap4_conj_negBlock] at h1
  rw [swap4_inv]
  exact (commute_longRootGroup_neg h2 (negBlock_mul_self 4 0) hb h1).symm

theorem swap4_center (hn : 2 ≤ 4) :
    swap4 * rootInv F hn * swap4⁻¹ * (rootInv F hn)⁻¹ ∈ Subgroup.center SL(4, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  have hinv : (rootInv F hn)⁻¹ = rootInv F hn := inv_eq_of_mul_eq_one_right (rootInv_mul_self hn)
  rw [hinv, swap4_inv]
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv]
  rw [swap4_conj_negBlock, Matrix.neg_mul, negBlock_mul_self, map_neg, map_one]

theorem negBlockK_two_eq_neg {n : ℕ} (hn : 2 ≤ n) :
    negBlockK F n 2 (n - 2) = -negBlock F n 0 := by
  rw [negBlockK_eq_diagonal, negBlock_zero_eq_diagonal, Matrix.diagonal_neg]
  congr 1
  funext x
  have hx := x.isLt
  by_cases h : x.val < 2
  · have h1 : ¬ (2 ≤ x.val) := by omega
    simp [h, h1]
  · have h1 : 2 ≤ x.val ∧ x.val < 2 + (n - 2) := ⟨by omega, by omega⟩
    simp [h, h1]

theorem rank_negBlock_sub_one (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (negBlock F n 0 - 1).rank = 2 := by
  classical
  rw [negBlock_zero_eq_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.rank_diagonal]
  have hc : Fintype.card {j : Fin n // j.val < 2} = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fin_val_lt hn
  refine Eq.trans ?_ hc
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  by_cases h : i.val < 2
  · simp only [h, ↓reduceIte, iff_true, ne_eq]
    intro h0
    exact h2 (by linear_combination -h0)
  · simp only [h, ↓reduceIte, sub_self, ne_eq, not_true_eq_false]

theorem rank_neg_negBlock_sub_one (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    (-negBlock F n 0 - 1).rank = n - 2 := by
  classical
  rw [negBlock_zero_eq_diagonal, Matrix.diagonal_neg, ← Matrix.diagonal_one, Matrix.diagonal_sub,
    Matrix.rank_diagonal]
  have hc : Fintype.card {j : Fin n // 2 ≤ j.val} = n - 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_fin_val_ge hn
  refine Eq.trans ?_ hc
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun i => ?_)
  by_cases h : i.val < 2
  · have h' : ¬ 2 ≤ i.val := by omega
    simp only [h, h', ↓reduceIte, neg_neg, sub_self, ne_eq, not_true_eq_false]
  · have h' : 2 ≤ i.val := by omega
    simp only [h, h', ↓reduceIte, ne_eq, iff_true]
    intro h0
    exact h2 (by linear_combination -h0)

theorem false_of_conj_eq_neg (h2 : (2 : F) ≠ 0) {n : ℕ} (hn : 5 ≤ n) (a : SL(n, F))
    (h : (a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 *
      ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = -negBlock F n 0) : False := by
  have hdet : IsUnit (a : Matrix (Fin n) (Fin n) F).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have hdet' : IsUnit ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F).det := by
    rw [Matrix.SpecialLinearGroup.det_coe]; exact isUnit_one
  have key : (a : Matrix (Fin n) (Fin n) F) * (negBlock F n 0 - 1) *
      ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = -negBlock F n 0 - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, h, Matrix.mul_one, coe_mul_coe_inv]
  have hr : (-negBlock F n 0 - 1).rank = (negBlock F n 0 - 1).rank := by
    rw [← key, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hdet',
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]
  rw [rank_neg_negBlock_sub_one h2 (by omega), rank_negBlock_sub_one h2 (by omega)] at hr
  omega

theorem conj_rootInv_eq_smul {n : ℕ} (hn : 2 ≤ n) {a : SL(n, F)}
    (ha : a * rootInv F hn * a⁻¹ * (rootInv F hn)⁻¹ ∈ Subgroup.center SL(n, F)) :
    ∃ r : F, r * r = 1 ∧ (a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 *
      ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = r • negBlock F n 0 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp ha
  have hinv : (rootInv F hn)⁻¹ = rootInv F hn := inv_eq_of_mul_eq_one_right (rootInv_mul_self hn)
  rw [hinv] at hr
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv] at hr
  have hD := negBlock_mul_self (K := F) n 0
  have h1 : (a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 *
      ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) = r • negBlock F n 0 := by
    calc (a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 * ((a⁻¹ : SL(n, F)) :
          Matrix (Fin n) (Fin n) F)
        = (a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 * ((a⁻¹ : SL(n, F)) :
          Matrix (Fin n) (Fin n) F) * (negBlock F n 0 * negBlock F n 0) := by
          rw [hD, Matrix.mul_one]
      _ = ((a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 * ((a⁻¹ : SL(n, F)) :
          Matrix (Fin n) (Fin n) F) * negBlock F n 0) * negBlock F n 0 := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.scalar (Fin n) r * negBlock F n 0 := by rw [hr]
      _ = r • negBlock F n 0 := by
          rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  refine ⟨r, ?_, h1⟩
  have h2 : ((a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 * ((a⁻¹ : SL(n, F)) :
      Matrix (Fin n) (Fin n) F)) * ((a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 *
        ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F)) = 1 := by
    calc _ = (a : Matrix (Fin n) (Fin n) F) * negBlock F n 0 * (((a⁻¹ : SL(n, F)) :
          Matrix (Fin n) (Fin n) F) * (a : Matrix (Fin n) (Fin n) F)) * negBlock F n 0 *
            ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by simp only [Matrix.mul_assoc]
      _ = (a : Matrix (Fin n) (Fin n) F) * (negBlock F n 0 * negBlock F n 0) *
            ((a⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) := by
          rw [coe_inv_mul_coe, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hD, Matrix.mul_one, coe_mul_coe_inv]
  rw [h1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hD] at h2
  have h3 := congrFun (congrFun h2 ⟨0, by omega⟩) ⟨0, by omega⟩
  simpa using h3

end Matrices

section Families

local notation "F₃" => GaloisField 3 1

open CFSG.ClassicalInvolution.ModelFacts (two_ne_zero_galoisField)

theorem twin_four {X : Type} [Group X] (ψ : SL(4, F₃) →* X)
    (hker : ψ.ker = Subgroup.center SL(4, F₃)) {R : Subgroup SL(4, F₃)}
    (hR : R ∈ longRootSet (K := F₃) (by norm_num : 2 ≤ 4))
    (hsl2 : Nonempty (R ≃* SL(2, F₃)))
    (hnc : ∀ r ∈ R, (∀ y : SL(4, F₃), r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center SL(4, F₃)) → r = 1) :
    ∀ t : X, t ∈ R.map ψ → orderOf t = 2 →
      ∃ w ∈ Subgroup.centralizer ({t} : Set X), ∀ a ∈ R.map ψ, ∀ b ∈ R.map ψ,
        a * (w * b * w⁻¹) = (w * b * w⁻¹) * a := by
  have h2 : (2 : F₃) ≠ 0 := two_ne_zero_galoisField 1 (by norm_num)
  have hn : 2 ≤ 4 := by norm_num
  obtain ⟨g, hg⟩ := (mem_longRootSet_iff hn).mp hR
  intro t ht ht2
  exact LTTwin.twin_of_family ψ hker {R}
    (fun R' h => by rw [Set.mem_singleton_iff.mp h]; exact hsl2)
    (fun R' h => by rw [Set.mem_singleton_iff.mp h]; exact hnc)
    (R₀ := rootSL2 F₃ hn) (fun R' h => ⟨g, (Set.mem_singleton_iff.mp h).trans hg⟩)
    (rootInv_mem_rootSL2 hn) (rootInv_mul_self hn) (rootInv_ne_one h2 hn) (w₀ := swap4)
    (swap4_center hn) (swap4_comm h2 hn) R (Set.mem_singleton R) t ht ht2

theorem component_ge5 {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 5 ≤ n)
    (ψ : SL(n, F₃) →* X) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = Subgroup.center SL(n, F₃)) {R : Subgroup SL(n, F₃)}
    (hR : R ∈ longRootSet (K := F₃) (by omega : 2 ≤ n))
    (hsl2 : Nonempty (R ≃* SL(2, F₃)))
    (hnc : ∀ r ∈ R, (∀ y : SL(n, F₃), r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center SL(n, F₃)) → r = 1) :
    ∀ t : X, t ∈ R.map ψ → orderOf t = 2 →
      ∃ E : Subgroup X, CFSG.Open.IsSubnormal E (Subgroup.centralizer ({t} : Set X)) ∧
        CFSG.Open.IsQuasisimple (E ⧸ CFSG.Open.classicalInvolutionOddCore E) := by
  have hn2 : 2 ≤ n := by omega
  have h2 : (2 : F₃) ≠ 0 := two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨g, hg⟩ := (mem_longRootSet_iff hn2).mp hR
  have hjk : 2 + (n - 2) ≤ n := by omega
  have hE₀ : (blockSL F₃ n (n - 2) 2 hjk).range =
      longRootGroup (negBlockK F₃ n 2 (n - 2)) := range_blockSL_eq_longRootGroupK h2 hjk
  have hC : ∀ y ∈ (blockSL F₃ n (n - 2) 2 hjk).range,
      y * rootInv F₃ hn2 = rootInv F₃ hn2 * y := by
    rintro _ ⟨A, rfl⟩
    exact blockSL_comm hjk (by omega) (Or.inr (by norm_num)) A (-1)
  have hN : ∀ a : SL(n, F₃), a * rootInv F₃ hn2 * a⁻¹ * (rootInv F₃ hn2)⁻¹ ∈
      Subgroup.center SL(n, F₃) → ∀ y ∈ (blockSL F₃ n (n - 2) 2 hjk).range,
        a * y * a⁻¹ ∈ (blockSL F₃ n (n - 2) 2 hjk).range := by
    intro a ha y hy
    obtain ⟨r, hr2, hr⟩ := conj_rootInv_eq_smul hn2 ha
    rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
    · have hcomm : (a : Matrix (Fin n) (Fin n) F₃) * negBlockK F₃ n 2 (n - 2) =
          negBlockK F₃ n 2 (n - 2) * a := by
        rw [negBlockK_two_eq_neg hn2, Matrix.mul_neg, Matrix.neg_mul, one_smul] at *
        congr 1
        calc (a : Matrix (Fin n) (Fin n) F₃) * negBlock F₃ n 0
            = (a : Matrix (Fin n) (Fin n) F₃) * negBlock F₃ n 0 *
              ((a⁻¹ : SL(n, F₃)) : Matrix (Fin n) (Fin n) F₃) *
                (a : Matrix (Fin n) (Fin n) F₃) := by
              rw [Matrix.mul_assoc _ ((a⁻¹ : SL(n, F₃)) : Matrix (Fin n) (Fin n) F₃),
                coe_inv_mul_coe, Matrix.mul_one]
          _ = negBlock F₃ n 0 * a := by rw [hr]
      rw [hE₀] at hy ⊢
      exact conj_mem_longRootGroup_of_commute hcomm hy
    · exact (false_of_conj_eq_neg h2 hn a (by rw [hr, neg_one_smul])).elim
  have hq : CFSG.IsQuasisimple ↥(blockSL F₃ n (n - 2) 2 hjk).range :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MonoidHom.ofInjective (blockSL_injective (K := F₃) hjk))
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by omega))
  have hE : ∀ y ∈ (blockSL F₃ n (n - 2) 2 hjk).range, y ∈ Subgroup.center SL(n, F₃) → y = 1 :=
    fun y hy hyc => by
      have h : y ∈ Subgroup.center SL(n, F₃) ⊓ (blockSL F₃ n (n - 2) 2 hjk).range := ⟨hyc, hy⟩
      rw [center_inf_range_blockSL hjk (by omega)] at h
      exact Subgroup.mem_bot.mp h
  intro t ht ht2
  exact LTAbs.component_of_family ψ hψ hker {R}
    (fun R' h => by rw [Set.mem_singleton_iff.mp h]; exact hsl2)
    (fun R' h => by rw [Set.mem_singleton_iff.mp h]; exact hnc)
    (R₀ := rootSL2 F₃ hn2) (fun R' h => ⟨g, (Set.mem_singleton_iff.mp h).trans hg⟩)
    (rootInv_mem_rootSL2 hn2) (rootInv_mul_self hn2) (rootInv_ne_one h2 hn2)
    (E₀ := (blockSL F₃ n (n - 2) 2 hjk).range) hC hN hq hE R (Set.mem_singleton R) t ht ht2

end Families

end LTSL

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts (nonempty_equiv_sl2_of_mem_fundamentalSubgroups
  fundNoncentral_generic)
open CFSG.ClassicalInvolution.RouteD (fundamentalSubgroups_psl_subset)


theorem kill3At_PSL_four : Kill3At .PSL 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : IsFundTag .PSL := trivial
  have ha : StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide, by decide⟩
  have hne : ¬ (StatedLieTag.PSL = .PSL ∧ 4 = 2) := fun h => absurd h.2 (by norm_num)
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  refine Or.inl (LTSL.twin_four ψ hker (fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hR)
    ?_ ?_ t ht ht2)
  · exact nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (e := 1) (by norm_num) hf ha
      (by decide) (by decide) hR
  · exact fun r hr hc => fundNoncentral_generic 3 .PSL 4 1 hf ha hne R hR r hr hc

theorem kill3At_PSL_ge5 (n : ℕ) (hn : 5 ≤ n) : Kill3At .PSL n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : IsFundTag .PSL := trivial
  have ha : StatedLieAdmissible .PSL n 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, fun h => by have := congrArg Prod.snd h; simp at this,
      fun h => by have := congrArg Prod.fst h; simp at this; omega⟩
  have hne : ¬ (StatedLieTag.PSL = .PSL ∧ n = 2) := fun h => absurd h.2 (by omega)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  refine Or.inr (LTSL.component_ge5 hn ψ hψ hker
    (fundamentalSubgroups_psl_subset (m := m) (by omega) hR) ?_ ?_ t ht ht2)
  · exact nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (e := 1) (by norm_num) hf ha
      (by decide) (by decide) hR
  · exact fun r hr hc => fundNoncentral_generic 3 .PSL (m + 1) 1 hf ha hne R hR r hr hc

theorem lie3At_PSL (n : ℕ) : Lie3At .PSL n := by
  by_cases h3 : n = 3
  · subst h3
    exact lie3At_of_survivor (Or.inl ⟨rfl, rfl⟩)
  by_cases h4 : n = 4
  · subst h4
    exact lie3At_of_kill (by decide) (by decide) kill3At_PSL_four
  by_cases h5 : 5 ≤ n
  · exact lie3At_of_kill (by decide) (by decide) (kill3At_PSL_ge5 n h5)
  intro _ ha
  exfalso
  have h2n : 2 ≤ n := ha.2.2.1
  have h23 : (n, 3 ^ 1) ≠ (2, 3) := ha.2.2.2.2
  have hn2 : n = 2 := by omega
  subst hn2
  exact h23 (by norm_num)

end CFSG.CGT.PushingUpLit.SolKNA
