module

public import CFSG.ClassicalInvolution.RouteD.TwinYSetup

public section

namespace CFSG.ClassicalInvolution.RouteD.TWD

open CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Sl2

variable {F : Type} [Field F]

@[expose] def wMat : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem wMat_mul_self : (wMat : SL(2, F)) * wMat = -1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagConj2_wMat : diagConj2 (-1 : Fˣ) 1 (wMat : SL(2, F)) = (wMat : SL(2, F))⁻¹ := by
  apply Subtype.ext
  rw [coe_diagConj2, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.adjugate_fin_two]

end Sl2

variable {F : Type} [Field F]

theorem exists_sq_inverted_of_standardPair (h2 : (2 : F) ≠ 0) {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) {zU tV : X} (hzU : zU ∈ U)
    (hzU2 : orderOf zU = 2) (htV : tV ∈ V) (htV2 : orderOf tV = 2) :
    ∃ a ∈ U, a * a = zU ∧ tV * a * tV = a⁻¹ := by
  obtain ⟨θ, -, hker, hU, hV⟩ := pair_normalize h
  have hzU' : zU ∈ (blockSL F 3 2 0 (by omega)).range.map θ := by
    rw [show (blockSL F 3 2 0 (by omega)).range = B12 F from rfl, hU]; exact hzU
  have htV' : tV ∈ (blockSL F 3 2 1 (by omega)).range.map θ := by
    rw [show (blockSL F 3 2 1 (by omega)).range = B23 F from rfl, hV]; exact htV
  have ez := Gaps.eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) hzU' hzU2
  have et := Gaps.eq_block_neg_one h2 hker (by omega : 1 + 2 ≤ 3) htV' htV2
  set n : SL(3, F) := blockSL F 3 2 1 (by omega) (-1) with hn
  have hnn : n * n = 1 := by
    rw [hn, ← map_mul]
    have : (-1 : SL(2, F)) * (-1) = 1 := by simp
    rw [this, map_one]
  have e1 : n * blockSL F 3 2 0 (by omega) (wMat : SL(2, F)) =
      blockSL F 3 2 0 (by omega) (diagConj2 (-1 : Fˣ) 1 (wMat : SL(2, F))) * n := by
    rw [hn, Gaps.blockSL_neg_one_mul, diagConj3_blockSL_zero]
  refine ⟨θ (blockSL F 3 2 0 (by omega) (wMat : SL(2, F))), ?_, ?_, ?_⟩
  · rw [← hU]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · rw [ez, ← map_mul, ← map_mul, wMat_mul_self]
  · rw [et, ← map_mul, ← map_mul, e1, diagConj2_wMat, mul_assoc, hnn, mul_one]
    simp only [map_inv]

section Comm

open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem exists_twinElt_comm {K T β : Subgroup G} {z t : G}
    (h2 : (2 : GaloisField p f) ≠ 0) (hz : IsClassicalMember p f K z)
    (hzT : IsClassicalMember p f T z) (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β)
    (hTβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W T β) :
    ∃ e : TwinElt K T z, t * e.u = e.u * t := by
  obtain ⟨W, hW⟩ := hKβ
  obtain ⟨W', hW'⟩ := hTβ
  obtain ⟨a, ha, haa, hta⟩ := exists_sq_inverted_of_standardPair h2 hW hz.mem hz.orderOf_eq_two
    ht.mem ht.orderOf_eq_two
  obtain ⟨a', ha', haa', hta'⟩ := exists_sq_inverted_of_standardPair h2 hW' hzT.mem
    hzT.orderOf_eq_two ht.mem ht.orderOf_eq_two
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.orderOf_eq_two, pow_two] at this
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hzK : ∀ x ∈ K, z * x = x * z := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (le_centralizer_of_isClassicalMember hz hx) z
      (Set.mem_singleton z)
  have hzT' : ∀ x ∈ T, z * x = x * z := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (le_centralizer_of_isClassicalMember hzT hx) z
      (Set.mem_singleton z)
  refine ⟨⟨a, a', ha, ha', haa, haa'⟩, ?_⟩
  have hinv : ∀ {b : G}, b * b = z → b⁻¹ = b * z := fun {b} hb =>
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, hb, hzz])
  have h1 : t * (a * a') * t = a⁻¹ * a'⁻¹ := by
    rw [← hta, ← hta']
    calc t * (a * a') * t = t * a * (t * t) * a' * t := by rw [htt]; simp only [mul_one, mul_assoc]
      _ = t * a * t * (t * a' * t) := by simp only [mul_assoc]
  have h2' : a⁻¹ * a'⁻¹ = a * a' := by
    rw [hinv haa, hinv haa']
    calc a * z * (a' * z) = a * (z * a') * z := by simp only [mul_assoc]
      _ = a * (a' * z) * z := by rw [hzT' a' ha']
      _ = a * a' * (z * z) := by simp only [mul_assoc]
      _ = a * a' := by rw [hzz, mul_one]
  have h3 : t * (a * a') * t = a * a' := h1.trans h2'
  show t * (a * a') = (a * a') * t
  calc t * (a * a') = t * (a * a') * (t * t) := by rw [htt, mul_one]
    _ = (t * (a * a') * t) * t := by simp only [mul_assoc]
    _ = a * a' * t := by rw [h3]

end Comm

end CFSG.ClassicalInvolution.RouteD.TWD
