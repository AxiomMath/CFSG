module

public import CFSG.GH74.GLS.Classes
public import CFSG.Walter.ReeOrder.Ward.Quaternion
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Matrix CFSG.PSL2Table CFSG.Walter.Ward.Quaternion CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem exists_quat_SL2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ a b w : SL(2, F), a * a = -1 ∧ b * b = -1 ∧ b * a = -1 * (a * b) ∧
      w * a * w⁻¹ = b ∧ w * b * w⁻¹ = a * b := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := by
    intro hc
    have he := FiniteField.even_card_of_char_two hc
    have h1 : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
    rw [h1] at he
    have := Nat.odd_iff.1 hodd
    omega
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hchar
  obtain ⟨a, b, hab⟩ := exists_normForm_eq hchar (ν := -1) (by norm_num) (-1)
  have h : a ^ 2 + b ^ 2 = -1 := by linear_combination hab
  refine ⟨qi, qj a b h, qw a b h2 h, qi_mul_qi, qj_mul_qj h, ?_, ?_, ?_⟩
  · rw [qj_mul_qi h]
    apply Subtype.ext
    simp [Matrix.SpecialLinearGroup.coe_neg]
  · rw [qw_mul_qi h2 h, mul_inv_cancel_right]
  · rw [qw_mul_qj h2 h, mul_inv_cancel_right]

theorem eq_neg_one_of_mem_center_SL2 {F : Type} [Field F] {g : SL(2, F)}
    (hg : g ∈ Subgroup.center SL(2, F)) (hg1 : g ≠ 1) : g = -1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hg
  have hr2 : r * r = 1 := by simpa [sq] using hr
  rcases mul_self_eq_one_iff.1 hr2 with h | h
  · exfalso
    apply hg1
    apply Subtype.ext
    rw [← hrg, h]
    simp
  · apply Subtype.ext
    rw [← hrg, h, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]

theorem exists_quat_of_hasSL2Model {K : Type} [Group K] (hK : HasSL2Model K Odd) {c : K}
    (hc : c ∈ Subgroup.center K) (hc1 : c ≠ 1) :
    ∃ a b w : K, a * a = c ∧ b * b = c ∧ b * a = c * (a * b) ∧
      w * a * w⁻¹ = b ∧ w * b * w⁻¹ = a * b := by
  obtain ⟨F, iF, fF, hodd, ⟨e⟩⟩ := hK
  let E : SL(2, F) ≃* K := (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  obtain ⟨a, b, w, ha, hb, hba, hwa, hwb⟩ := exists_quat_SL2 hodd
  have hcE : E.symm c ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 hc (E g)
    apply E.injective
    simpa using this
  have hc1E : E.symm c ≠ 1 := fun h => hc1 (by simpa using congrArg E h)
  have hcneg : E.symm c = -1 := eq_neg_one_of_mem_center_SL2 hcE hc1E
  have hc' : c = E (-1) := by
    rw [← hcneg]; simp
  refine ⟨E a, E b, E w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, ha, hc']
  · rw [← map_mul, hb, hc']
  · rw [← map_mul, hba, map_mul, map_mul, hc']
  · rw [← map_inv, ← map_mul, ← map_mul, hwa]
  · rw [← map_inv, ← map_mul, ← map_mul, hwb, map_mul]

theorem hasSL2Model_mono {K : Type} [Group K] {P Q : ℕ → Prop} (h : HasSL2Model K P)
    (hPQ : ∀ n, P n → Q n) : HasSL2Model K Q := by
  obtain ⟨F, iF, fF, hP, e⟩ := h
  exact ⟨F, iF, fF, hPQ _ hP, e⟩

end CFSG.GH74.GLS.Stage2.Local
