module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFixedVector
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

universe u

open scoped MatrixGroups

variable {F : Type u} [Field F]

def upperUnipotent : Multiplicative F →* SL(2, F) where
  toFun c := ⟨!![1, Multiplicative.toAdd c; 0, 1], by simp [Matrix.det_fin_two]⟩
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' c d := by
    ext i j
    change (!![1, Multiplicative.toAdd (c * d); 0, 1] : Matrix (Fin 2) (Fin 2) F) i j =
      (!![1, Multiplicative.toAdd c; 0, 1] * !![1, Multiplicative.toAdd d; 0, 1]) i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upperUnipotent_injective : Function.Injective (upperUnipotent (F := F)) := by
  intro c d h
  have hentry := congrFun (congrFun (congrArg
    (fun a : SL(2, F) => (a : Matrix (Fin 2) (Fin 2) F)) h) 0) 1
  exact Multiplicative.toAdd.injective hentry

theorem upperUnipotent_card [Finite F] :
    Nat.card (upperUnipotent (F := F)).range = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective upperUnipotent_injective).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem sl2_fixes_first_iff (h : SL(2, F)) :
    h • (Pi.single 0 1 : Fin 2 → F) = Pi.single 0 1 ↔
      h ∈ (upperUnipotent (F := F)).range := by
  constructor
  · intro hh
    change Matrix.mulVec (h : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) = Pi.single 0 1 at hh
    rw [Matrix.mulVec_single_one] at hh
    have h00 : h 0 0 = 1 := by simpa using congrFun hh 0
    have h10 : h 1 0 = 0 := by simpa using congrFun hh 1
    have h11 : h 1 1 = 1 := by
      have hd := h.2
      simpa only [Matrix.det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using hd
    refine ⟨Multiplicative.ofAdd (h 0 1), ?_⟩
    ext i j
    change (!![1, h 0 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j = h i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]
  · rintro ⟨c, rfl⟩
    change Matrix.mulVec (upperUnipotent c : Matrix (Fin 2) (Fin 2) F) (Pi.single 0 1) = _
    rw [Matrix.mulVec_single_one]
    ext i
    change (!![1, Multiplicative.toAdd c; 0, 1] : Matrix (Fin 2) (Fin 2) F) i 0 =
      (Pi.single 0 1 : Fin 2 → F) i
    fin_cases i <;> simp

theorem pgroup_sl2_conjugate_unipotent [Finite F] [CharP F 2]
    (A : Subgroup SL(2, F)) (hA : IsPGroup 2 A) :
    ∃ x : SL(2, F), A.map (MulAut.conj x⁻¹).toMonoidHom ≤
      (upperUnipotent (F := F)).range := by
  obtain ⟨v, hv, hfix⟩ := pgroup_sl2_common_fixed_vector A hA
  obtain ⟨x, hx⟩ := exists_sl2_first_column v hv
  refine ⟨x, ?_⟩
  rintro y ⟨a, ha, rfl⟩
  apply (sl2_fixes_first_iff _).mp
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [mul_smul, mul_smul, hx, hfix a ha, ← hx, inv_smul_smul]

theorem pgroup_sl2_card_le [Finite F] [CharP F 2]
    (A : Subgroup SL(2, F)) (hA : IsPGroup 2 A) : Nat.card A ≤ Nat.card F := by
  obtain ⟨x, hx⟩ := pgroup_sl2_conjugate_unipotent A hA
  calc
    Nat.card A = Nat.card (A.map (MulAut.conj x⁻¹).toMonoidHom) :=
      Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv
    _ ≤ Nat.card (upperUnipotent (F := F)).range :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hx) (Subgroup.inclusion_injective hx)
    _ = Nat.card F := upperUnipotent_card

theorem elementary_sl2_card_le [Finite F] [CharP F 2]
    (A : Subgroup SL(2, F)) [CFSG.IsElementaryAbelian 2 A] : Nat.card A ≤ Nat.card F :=
  pgroup_sl2_card_le A (CFSG.IsElementaryAbelian.isPGroup 2 A)

end CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
