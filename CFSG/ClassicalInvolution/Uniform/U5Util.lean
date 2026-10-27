module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameData

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open
open scoped MatrixGroups commutatorElement

section EightGroup

variable {G : Type} [Group G]

theorem isElemAbelian_closure_involutions {S : Set G} (hS2 : ∀ s ∈ S, s * s = 1)
    (hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) : IsElemAbelian 2 (Subgroup.closure S) := by
  have hcomm : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure (fun x hx y hy _ => hSc x hx y hy)
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy => rw [sq]; exact hS2 y hy
  | one => simp
  | mul y z hy' hz' hy hz =>
    have hc : y * z = z * y := by
      have h := hcomm.is_comm.comm (⟨y, hy'⟩ : Subgroup.closure S) ⟨z, hz'⟩
      exact congrArg Subtype.val h
    rw [(Commute.mul_pow (show Commute y z from hc)), hy, hz, one_mul]
  | inv y _ hy => rw [inv_pow, hy, inv_one]

variable [Finite G]

theorem exists_isElemAbelian_card_eight {x y w : G} (hx : x * x = 1) (hy : y * y = 1)
    (hw : w * w = 1) (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hw1 : w ≠ 1) (hyx : y ≠ x) (hwx : w ≠ x) (hwy : w ≠ y)
    (hwxy : w ≠ x * y) : ∃ E : Subgroup G, IsElemAbelian 2 E ∧ Nat.card E = 8 := by
  classical
  set V : Subgroup G := Subgroup.closure ({x, y} : Set G) with hV
  have hV4 : Nat.card V = 4 :=
    CFSG.ClassicalInvolution.Balance.Bootstrap.card_closure_pair_eq_four hx hy hx1 hy1 hyx.symm
      hxy
  set W : Subgroup G := Subgroup.zpowers w with hW
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw) hw1
  have hW2 : Nat.card W = 2 := by rw [hW, Nat.card_zpowers, hw2]
  have hwC : w ∈ Subgroup.centralizer (V : Set G) := by
    have hle : V ≤ Subgroup.centralizer ({w} : Set G) := by
      refine (Subgroup.closure_le _).2 ?_
      intro u hu
      rcases hu with rfl | hu
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hxw
      · rw [Set.mem_singleton_iff] at hu
        subst hu
        exact Subgroup.mem_centralizer_singleton_iff.mpr hyw
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hv)
  have hWN : W ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.zpowers_le.mpr hwC).trans (Subgroup.centralizer_le_normalizer _)
  have hwV : w ∉ V := by
    intro h
    rcases CFSG.ClassicalInvolution.Asc77.ChainFrame.mem_closure_four hx hy hxy h with
      h | h | h | h
    exacts [hw1 h, hwx h, hwy h, hwxy h]
  have hVW : Nat.card ↥(V ⊓ W) = 1 := by
    have : V ⊓ W = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
      rcases CFSG.ClassicalInvolution.Asc77.ChainFrame.eq_one_or_eq_of_mem_zpowers hw2 hg.2 with
        h | h
      · exact h
      · exact absurd (h ▸ hg.1) hwV
    rw [this]
    exact Subgroup.card_bot
  have hprod := CFSG.ClassicalInvolution.Asc77.ChainFrame.card_sup_mul_card_inf' hWN
  rw [hVW, hV4, hW2] at hprod
  refine ⟨W ⊔ V, ?_, by omega⟩
  have hset : W ⊔ V = Subgroup.closure ({x, y, w} : Set G) := by
    rw [hV, hW, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
    ext u
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
    tauto
  rw [hset]
  refine isElemAbelian_closure_involutions ?_ ?_
  · intro s hs
    rcases hs with rfl | rfl | hs
    · exact hx
    · exact hy
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hw
  · intro s hs t ht
    rcases hs with rfl | rfl | hs <;> rcases ht with rfl | rfl | ht
    all_goals first
      | rfl
      | assumption
      | exact (by assumption : _ = _).symm
      | (rw [Set.mem_singleton_iff] at *
         subst_vars
         first | rfl | assumption | exact (by assumption : _ = _).symm)

theorem three_le_twoRank_of_card_eight (E : Subgroup G) (hE : IsElemAbelian 2 E)
    (hc : Nat.card E = 8) : 3 ≤ CFSG.Open.twoRank G := by
  unfold CFSG.Open.twoRank CFSG.Open.pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, le_top, hE, by rw [hc]; norm_num⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

end EightGroup

section SL2

theorem exists_quaternion_sl2_three {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) :
    ∃ A B : SL(2, F), A * A = -1 ∧ B * B = -1 ∧ ⁅A, B⁆ = (-1 : SL(2, F)) := by
  have h3 : (3 : F) = 0 := by
    have h : Nat.card F • (1 : F) = 0 := card_nsmul_eq_zero'
    rw [hF] at h
    simpa using h
  obtain ⟨A, hA⟩ : ∃ A : SL(2, F), (A : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, 0] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]⟩, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : SL(2, F), (B : Matrix (Fin 2) (Fin 2) F) = !![1, 1; 1, -1] :=
    ⟨⟨_, by simp [Matrix.det_fin_two]; linear_combination (-1 : F) * h3⟩, rfl⟩
  have hAi : ((A⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hA, Matrix.adjugate_fin_two]
    simp
  have hBi : ((B⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![-1, -1; -1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hB, Matrix.adjugate_fin_two]
    simp
  refine ⟨A, B, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hA, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, hB, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination (1 : F) * h3
  · apply Subtype.ext
    rw [commutatorElement_def]
    simp only [Matrix.SpecialLinearGroup.coe_mul, hA, hB, hAi, hBi,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linear_combination (1 : F) * h3

end SL2

end CFSG.ClassicalInvolution.Uniform
