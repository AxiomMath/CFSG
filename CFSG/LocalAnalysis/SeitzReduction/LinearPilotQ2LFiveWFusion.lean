module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2Fusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCores
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Model

variable {n : ℕ} {K : Type*} [Field K]

theorem rank_vecMulVec_eq_one {u w : Fin n → K} (hu : u ≠ 0) (hw : w ≠ 0) :
    (vecMulVec u w).rank = 1 := by
  apply le_antisymm (rank_vecMulVec_le u w)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  have hcol : (vecMulVec u w).col j ∈ Submodule.span K (Set.range (vecMulVec u w).col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [h0, Submodule.mem_bot] at hcol
  apply hu
  have h1 : w j • u = 0 := by
    rw [← hcol]
    ext i
    simp [vecMulVec_apply, mul_comm]
  exact (smul_eq_zero.1 h1).resolve_left hj

theorem isInvolutionClass_one_of_mem_pointRadOn [CharP K 2] {c : Fin n} {S : Finset (Fin n)}
    {v : projectiveSL n K} (hv : v ∈ pointRadOn c S) (hv1 : v ≠ 1) : IsInvolutionClass 1 v := by
  obtain ⟨_, ⟨r, -, rfl⟩, rfl⟩ := hv
  refine ⟨pointRadElem c r, rfl, ?_, ?_⟩
  · rw [pointRadElem_mul, show r + r = 0 from by
      ext j
      simp only [Pi.add_apply, Pi.zero_apply]
      rw [← two_mul, CharTwo.two_eq_zero, zero_mul], pointRadElem_zero]
  · have hne : Function.update r c 0 ≠ 0 := by
      intro h0
      apply hv1
      have h1 : pointRadElem c r = 1 := by
        apply Subtype.ext
        rw [coe_pointRadElem, pointRadMat, h0, vecMulVec_zero, add_zero]
        rfl
      rw [h1, map_one]
    have hu : (Pi.single c (1 : K) : Fin n → K) ≠ 0 := by
      intro h
      have := congrFun h c
      simp at this
    rw [coe_pointRadElem, pointRadMat, add_sub_cancel_left]
    exact rank_vecMulVec_eq_one hu hne

theorem isInvolutionClass_one_of_mem_pointRadical [CharP K 2] {c : Fin n}
    {v : projectiveSL n K} (hv : v ∈ pointRadical c) (hv1 : v ≠ 1) : IsInvolutionClass 1 v :=
  isInvolutionClass_one_of_mem_pointRadOn hv hv1

end Model

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_conj_eq_mul_of_mem_pointRadical (hset : SeitzSetting G L) {n : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (c : Fin n) {v : G}
    (hv : v ∈ modelToG e (pointRadical c)) : ∃ g : G, g⁻¹ * t * g = t * v := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hv
  by_cases hy1 : y = 1
  · subst hy1
    exact ⟨1, by simp⟩
  have hyc := isInvolutionClass_one_of_mem_pointRadical hy hy1
  obtain ⟨x, z, hxz, hz, -, -, -⟩ := exists_conj_eq_mul_transvection_twoSided_two hset hn hK e htC ht
  have hab : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨c₁, hc₁⟩ := exists_conj_eq_xab hab hz
  obtain ⟨c₂, hc₂⟩ := exists_conj_eq_xab hab hyc
  set m : L := e.symm (c₂⁻¹ * c₁) with hm
  have hmz : m * z * m⁻¹ = e.symm y := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    calc c₂⁻¹ * c₁ * e z * (c₂⁻¹ * c₁)⁻¹ = c₂⁻¹ * (c₁ * e z * c₁⁻¹) * c₂ := by group
      _ = c₂⁻¹ * (c₂ * y * c₂⁻¹) * c₂ := by rw [hc₁, hc₂]
      _ = y := by group
  have hmt : (m : G) * t = t * m := (mem_centralizer_iff.1 htC) m m.2
  refine ⟨x * (m : G)⁻¹, ?_⟩
  have hmz' : (m : G) * z * (m : G)⁻¹ = ((e.symm y : L) : G) := by
    rw [← hmz]
    rfl
  calc (x * (m : G)⁻¹)⁻¹ * t * (x * (m : G)⁻¹) = m * (x⁻¹ * t * x) * (m : G)⁻¹ := by group
    _ = (m * t) * z * (m : G)⁻¹ := by rw [hxz]; group
    _ = t * ((m : G) * z * (m : G)⁻¹) := by rw [hmt]; group
    _ = t * ((e.symm y : L) : G) := by rw [hmz']

theorem conj_ne_of_mem_pointRadical (hset : SeitzSetting G L) {n : ℕ} (hn : 4 ≤ n)
    {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 2) (e : L ≃* projectiveSL n K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) (c : Fin n) {v : G}
    (hv : v ∈ modelToG e (pointRadical c)) (g : G) : g⁻¹ * t * g ≠ v := by
  intro hgv
  obtain ⟨y, hy, rfl⟩ := (mem_modelToG e).1 hv
  by_cases hy1 : y = 1
  · subst hy1
    have h1 : t = 1 := by
      have : g⁻¹ * t * g = 1 := by rw [hgv, map_one, Subgroup.coe_one]
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = 1 := by rw [this]; group
    rw [h1, orderOf_one] at ht
    exact absurd ht (by decide)
  have hyc := isInvolutionClass_one_of_mem_pointRadical hy hy1
  have hgL : g⁻¹ * t * g ∈ L := by rw [hgv]; exact (e.symm y).2
  have hK' : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  apply not_isInvolutionClass_one_conj hset hn hK' e htC ht g hgL
  have heq : (⟨g⁻¹ * t * g, hgL⟩ : L) = e.symm y := Subtype.ext hgv
  rw [heq, MulEquiv.apply_symm_apply]
  exact hyc

end Setting

end CFSG.SeitzReduction.LinearPilot
