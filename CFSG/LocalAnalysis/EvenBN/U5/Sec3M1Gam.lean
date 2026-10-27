module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Model
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3One4
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem lmat_col_ne_zero (x : Gam h) (b : HypIndex 2 1) : ∃ a, lmat x a b ≠ 0 := by
  by_contra hc
  push Not at hc
  have e := congrFun (congrFun (lmat_mul_inv x).2 b) b
  rw [Matrix.mul_apply] at e
  simp [hc] at e

theorem lmat_blocks_of_fixed {x : Gam h} {t : hypSU h 2 1} (ht : t ∈ hypTorus h 2 1)
    (hx : actΓ h x t = t) {β : K} (hβ : β ≠ β⁻¹) (h1 : mat t ιe₁ ιe₁ = β)
    (h2 : mat t ιe₂ ιe₂ = β) (h3 : mat t ιz ιz = 1) (h4 : mat t ιf₁ ιf₁ = β⁻¹)
    (h5 : mat t ιf₂ ιf₂ = β⁻¹) :
    (∀ i : Fin 2, lmat x (.inl i) ιz = 0 ∧ lmat x (.inr (.inr i)) ιz = 0 ∧
        lmat x ιz (.inl i) = 0 ∧ lmat x ιz (.inr (.inr i)) = 0) ∧
      ((x.1.right β = β ∧ ∀ i j : Fin 2, lmat x (.inl i) (.inr (.inr j)) = 0 ∧
          lmat x (.inr (.inr i)) (.inl j) = 0) ∨
        (x.1.right β = β⁻¹ ∧ ∀ i j : Fin 2, lmat x (.inl i) (.inl j) = 0 ∧
          lmat x (.inr (.inr i)) (.inr (.inr j)) = 0)) := by
  set σ := x.1.right with hσ
  have hβ1 : β ≠ 1 := fun e => hβ (by rw [e, inv_one])
  have hβ1' : β⁻¹ ≠ 1 := fun e => hβ1 (inv_eq_one.1 e)
  have hE : ∀ i : Fin 2, mat t (.inl i) (.inl i) = β := fun i => by
    fin_cases i
    · exact h1
    · exact h2
  have hF : ∀ i : Fin 2, mat t (.inr (.inr i)) (.inr (.inr i)) = β⁻¹ := fun i => by
    fin_cases i
    · exact h4
    · exact h5
  have hk := lmat_entry_of_act_torus ht hx
  have hz : ∀ {a b : HypIndex 2 1} {u v : K}, mat t a a = u → mat t b b = v → σ v ≠ u →
      lmat x a b = 0 := by
    intro a b u v ha hb huv
    have e := hk a b
    rw [ha, hb] at e
    have : lmat x a b * (σ v - u) = 0 := by linear_combination e
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 huv)
  have hσne : ∀ {u : K}, u ≠ 1 → σ u ≠ 1 := fun {u} hu e =>
    hu ((map_eq_one_iff σ σ.injective).1 e)
  have hzz : ∀ i : Fin 2, lmat x (.inl i) ιz = 0 ∧ lmat x (.inr (.inr i)) ιz = 0 ∧
      lmat x ιz (.inl i) = 0 ∧ lmat x ιz (.inr (.inr i)) = 0 := fun i =>
    ⟨hz (hE i) h3 (by rw [map_one]; exact hβ1.symm),
      hz (hF i) h3 (by rw [map_one]; exact hβ1'.symm),
      hz h3 (hE i) (hσne hβ1), hz h3 (hF i) (hσne hβ1')⟩
  refine ⟨hzz, ?_⟩
  by_cases hσβ : σ β = β
  · have hσβ' : σ β⁻¹ = β⁻¹ := by rw [map_inv₀, hσβ]
    exact Or.inl ⟨hσβ, fun i j => ⟨hz (hE i) (hF j) (by rw [hσβ']; exact hβ.symm),
      hz (hF i) (hE j) (by rw [hσβ]; exact hβ)⟩⟩
  by_cases hσβ₂ : σ β = β⁻¹
  · have hσβ' : σ β⁻¹ = β := by rw [map_inv₀, hσβ₂, inv_inv]
    exact Or.inr ⟨hσβ₂, fun i j => ⟨hz (hE i) (hE j) (by rw [hσβ₂]; exact hβ.symm),
      hz (hF i) (hF j) (by rw [hσβ']; exact hβ)⟩⟩
  exfalso
  obtain ⟨a, ha⟩ := lmat_col_ne_zero x (.inl 0)
  apply ha
  rcases a with i | k | i
  · exact hz (hE i) (hE 0) hσβ
  · fin_cases k
    exact (hzz 0).2.2.1
  · exact hz (hF i) (hE 0) hσβ₂

theorem root_relations {x : Gam h}
    (hU : ∀ u ∈ patSub h sI₁ isPattern_sI₁, actΓ h x u = u) :
    (∀ c : K, x.1.right c * lmat x ιe₁ ιe₁ = c * lmat x ιe₂ ιe₂) ∧
      (∀ c : K, x.1.right c * lmat x ιf₂ ιe₁ = h.bar c * lmat x ιf₁ ιe₂) ∧
      (∀ c : K, x.1.right (h.bar c) * lmat x ιf₂ ιf₂ = h.bar c * lmat x ιf₁ ιf₁) ∧
      lmat x ιe₂ ιe₁ = 0 ∧ lmat x ιf₁ ιe₁ = 0 ∧ lmat x ιf₁ ιf₂ = 0 := by
  have key : ∀ c : K, ∃ u : hypSU h 2 1,
      (∀ a b, (lmat x * (mat u).map x.1.right) a b = (mat u * lmat x) a b) ∧
      mat u ιe₁ ιe₂ = c ∧ mat u ιf₂ ιf₁ = h.bar c ∧
      (mat u ιe₁ ιe₁ = 1 ∧ mat u ιe₂ ιe₂ = 1 ∧ mat u ιz ιz = 1 ∧ mat u ιf₁ ιf₁ = 1 ∧
        mat u ιf₂ ιf₂ = 1) ∧
      (mat u ιe₂ ιe₁ = 0 ∧ mat u ιz ιe₁ = 0 ∧ mat u ιf₂ ιe₁ = 0 ∧ mat u ιf₁ ιe₁ = 0 ∧
        mat u ιz ιe₂ = 0 ∧ mat u ιf₂ ιe₂ = 0 ∧ mat u ιf₁ ιe₂ = 0 ∧ mat u ιf₂ ιz = 0 ∧
        mat u ιf₁ ιz = 0 ∧ mat u ιf₁ ιf₂ = 0) ∧
      (mat u ιe₁ ιz = 0 ∧ mat u ιz ιf₁ = 0 ∧ mat u ιe₂ ιz = 0 ∧ mat u ιz ιf₂ = 0 ∧
        mat u ιe₁ ιf₂ = 0 ∧ mat u ιe₂ ιf₁ = 0 ∧ mat u ιe₂ ιf₂ = 0 ∧ mat u ιe₁ ιf₁ = 0) := by
    intro c
    obtain ⟨u, hu, huc⟩ := exists_rootI₁ h c
    obtain ⟨huU, a1⟩ := mem_patSub_sI₁.1 hu
    refine ⟨u, fun a b => by rw [lmat_mul_map, hU u hu], huc, ?_, U_entries huU |>.1,
      U_entries huU |>.2, a1⟩
    rw [(U_rel huU).1, huc]
  have hσ1 := map_one x.1.right
  have hσ0 := map_zero x.1.right
  refine ⟨fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, e, hc, -, ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := key c
    have k := e ιe₁ ιe₂
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, hc, d1, d2,
      l5, l6, l7, a1, a5, a8, hσ1, hσ0,
      mul_zero, mul_one, zero_mul, one_mul, add_zero] at k
    linear_combination k
  · obtain ⟨u, e, hc, hc', ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := key c
    have k := e ιf₂ ιe₂
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, hc, hc', d2,
      d5, l3, l5, l6, l7, l8, hσ1, hσ0,
      mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at k
    linear_combination k
  · obtain ⟨u, e, hc, hc', ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := key c
    have k := e ιf₂ ιf₁
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, hc', d4,
      d5, l3, l6, l8, a2, a6, a8, hσ1, hσ0,
      mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at k
    linear_combination k
  · obtain ⟨u, e, hc, -, ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := key 1
    have k := e ιe₂ ιe₂
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, hc, d2,
      l1, l5, l6, l7, a3, a6, a7, hσ1, hσ0,
      mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at k
    linear_combination k
  · obtain ⟨u, e, hc, -, ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := key 1
    have k := e ιf₁ ιe₂
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, hc, d2, d4,
      l4, l5, l6, l7, l9, l10, hσ1, hσ0,
      mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at k
    linear_combination k
  · obtain ⟨u, e, hc, hc', ⟨d1, d2, d3, d4, d5⟩, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
      ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩⟩ := key 1
    have k := e ιf₁ ιf₁
    simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, hc', d4,
      l4, l7, l9, l10, a2, a6, a8, hσ1, hσ0,
      map_one, mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add] at k
    linear_combination k

theorem map_mat_rSU (σ : K ≃+* K) : (mat (rSU h)).map σ = mat (rSU h) := by
  ext a b
  rw [Matrix.map_apply, mat_rSU]
  split_ifs <;> simp

theorem rSU_comm_core {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hA : A * mat (rSU h) = mat (rSU h) * A) (a b : HypIndex 2 1) :
    A a b = A (σr a) (σr b) := by
  have k := congrFun (congrFun hA a) (σr b)
  rw [Matrix.mul_apply, Matrix.mul_apply] at k
  simp only [mat_rSU, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at k
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), Finset.sum_eq_single b] at k
  · rwa [ite_eq_left rfl] at k
  · intro l _ hl
    refine ite_eq_right fun hlb => ?_
    exact hl (by rw [← σr_σr l, hlb, σr_σr])
  · simp

end Model

end CFSG.LocalAnalysis.EvenBN.U5
