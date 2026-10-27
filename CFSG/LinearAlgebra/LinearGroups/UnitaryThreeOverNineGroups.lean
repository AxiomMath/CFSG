module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryPerfectFamily
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem unitaryFieldData_of_card (hF : Nat.card F = 9) : UnitaryFieldData 3 1 F :=
  ⟨Nat.prime_three, le_rfl, hF.trans (by norm_num)⟩

theorem bar_eq_cube (h : UnitaryFieldData 3 1 F) (c : F) : h.bar c = c ^ 3 := by
  rw [UnitaryFieldData.bar_apply, pow_one]

theorem map_bar_eq_cube (h : UnitaryFieldData 3 1 F) {d : ℕ} (A : Matrix (Fin d) (Fin d) F) :
    A.map h.bar = A.map (· ^ 3) := by
  ext a b
  simp [bar_eq_cube h]

theorem ncard_normOne_eq (h : UnitaryFieldData 3 1 F) (d : ℕ) :
    {v : Fin d → F | ∑ j, v j ^ 3 * v j = 1}.ncard = normSumCount h d 1 := by
  rw [← Nat.card_coe_set_eq]
  unfold normSumCount
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  have hsum : ∑ j, v j ^ 3 * v j = ∑ j, h.norm (v j) :=
    Finset.sum_congr rfl fun j _ => by rw [UnitaryFieldData.norm, bar_eq_cube h, mul_comm]
  rw [Set.mem_ofPred_eq, hsum]

theorem ncard_normOne_one (hF : Nat.card F = 9) :
    {v : Fin 1 → F | ∑ j, v j ^ 3 * v j = 1}.ncard = 4 := by
  have h := unitaryFieldData_of_card hF
  have h0 := (normSumCount_closed h 0).1
  norm_num at h0
  rw [ncard_normOne_eq h]
  exact_mod_cast h0

theorem ncard_normOne_two (hF : Nat.card F = 9) :
    {v : Fin 2 → F | ∑ j, v j ^ 3 * v j = 1}.ncard = 24 := by
  have h := unitaryFieldData_of_card hF
  have h1 := (normSumCount_closed h 1).1
  norm_num at h1
  rw [ncard_normOne_eq h]
  exact_mod_cast h1

theorem ncard_normOne_three (hF : Nat.card F = 9) :
    {v : Fin 3 → F | ∑ j, v j ^ 3 * v j = 1}.ncard = 252 := by
  have h := unitaryFieldData_of_card hF
  have h2 := (normSumCount_closed h 2).1
  norm_num at h2
  rw [ncard_normOne_eq h]
  exact_mod_cast h2

theorem gramForm_one_isSymm (h : UnitaryFieldData 3 1 F) (d : ℕ) :
    (gramForm h (1 : Matrix (Fin d) (Fin d) F)).IsSymm :=
  gramForm_isSymm h (by simp [Matrix.map_one])

theorem gramForm_one_separatingLeft (h : UnitaryFieldData 3 1 F) (d : ℕ) :
    (gramForm h (1 : Matrix (Fin d) (Fin d) F)).SeparatingLeft :=
  gramForm_separatingLeft h (by simp)

theorem card_unitarySet_eq (h : UnitaryFieldData 3 1 F) (d : ℕ) :
    Nat.card {A : GL (Fin d) F // ((A : Matrix (Fin d) (Fin d) F).map (· ^ 3))ᵀ * A = 1} =
      Nat.card (sesqUnitaryGroup (gramForm h (1 : Matrix (Fin d) (Fin d) F))) := by
  refine Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun A => ?_)
  change _ ↔ Matrix.GeneralLinearGroup.toLin A ∈ sesqUnitaryGroup _
  rw [mem_sesqUnitaryGroup, Matrix.GeneralLinearGroup.coe_toLin]
  simp only [Matrix.mulVecLin_apply]
  rw [gramForm_isometry_iff, Matrix.mul_one, map_bar_eq_cube h]

theorem card_unitary_two (hF : Nat.card F = 9) :
    Nat.card {A : GL (Fin 2) F // ((A : Matrix (Fin 2) (Fin 2) F).map (· ^ 3))ᵀ * A = 1} =
      96 := by
  have h := unitaryFieldData_of_card hF
  have := h.finite
  have := Fintype.ofFinite F
  have hU := (unitary_full_group_order h (gramForm_one_isSymm h 2)
    (gramForm_one_separatingLeft h 2) (Module.finrank_fin_fun F) (by norm_num)).1
  rw [card_unitarySet_eq h]
  have hprod : ∏ i ∈ Finset.Icc 1 2, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 32 := by decide
  rw [hprod] at hU
  norm_num at hU
  exact_mod_cast hU

theorem card_unitary_three (hF : Nat.card F = 9) :
    Nat.card {A : GL (Fin 3) F // ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * A = 1} =
      24192 := by
  have h := unitaryFieldData_of_card hF
  have := h.finite
  have := Fintype.ofFinite F
  have hU := (unitary_full_group_order h (gramForm_one_isSymm h 3)
    (gramForm_one_separatingLeft h 3) (Module.finrank_fin_fun F) (by norm_num)).1
  rw [card_unitarySet_eq h]
  have hprod : ∏ i ∈ Finset.Icc 1 3, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 896 := by decide
  rw [hprod] at hU
  norm_num at hU
  exact_mod_cast hU

omit [Field F] in
theorem card_eq_sq_pow (hF : Nat.card F = 9) : Nat.card F = (3 ^ 1) ^ 2 :=
  hF.trans (by norm_num)

theorem coe_statedSU (hF : Nat.card F = 9) :
    (StatedSU 3 3 F : Set (GL (Fin 3) F)) = {A : GL (Fin 3) F |
      ((A : Matrix (Fin 3) (Fin 3) F).map (· ^ 3))ᵀ * A = 1 ∧
        (A : Matrix (Fin 3) (Fin 3) F).det = 1} := by
  have hset := (unitary_scalar_kernel (p := 3) (f := 1) Nat.prime_three (card_eq_sq_pow hF)
    (n := 3) (by norm_num)).1
  ext A
  have hA := Set.ext_iff.mp hset A
  simp only [pow_one] at hA
  rw [hA, Set.mem_ofPred_eq, Set.mem_ofPred_eq, and_comm]

theorem statedSU_eq_gramSU (hF : Nat.card F = 9) (h : UnitaryFieldData 3 1 F) :
    StatedSU 3 3 F = gramSU h 1 := by
  ext A
  rw [← SetLike.mem_coe, coe_statedSU hF, Set.mem_ofPred_eq, mem_gramSU, Matrix.mul_one,
    map_bar_eq_cube h]

theorem card_statedSU (hF : Nat.card F = 9) : Nat.card (StatedSU 3 3 F) = 6048 := by
  have h := unitaryFieldData_of_card hF
  have := h.finite
  have := Fintype.ofFinite F
  have hSU := (unitary_full_group_order h (gramForm_one_isSymm h 3)
    (gramForm_one_separatingLeft h 3) (Module.finrank_fin_fun F) (by norm_num)).2.1
  rw [statedSU_eq_gramSU hF h, card_gramSU]
  have hprod : ∏ i ∈ Finset.Icc 2 3, (((3 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i) = 224 := by decide
  rw [hprod] at hSU
  norm_num at hSU
  exact_mod_cast hSU

theorem statedScalars_subgroupOf_statedSU_eq_bot (hF : Nat.card F = 9) :
    (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 3 F) = ⊥ := by
  have h := (unitary_scalar_kernel (p := 3) (f := 1) Nat.prime_three (card_eq_sq_pow hF)
    (n := 3) (by norm_num)).2.2
  rw [← Subgroup.card_eq_one]
  exact h.trans (by norm_num)

theorem isPerfect_statedSU_three_three (hF : Nat.card F = 9) :
    Group.IsPerfect (StatedSU 3 3 F) := by
  have h := unitaryFieldData_of_card hF
  have hP := unitary_perfect h (gramForm_one_isSymm h 3) (gramForm_one_separatingLeft h 3)
    (by rw [Module.finrank_fin_fun]) (by rw [Module.finrank_fin_fun]; decide)
  have hmap : (gramSU h (1 : Matrix (Fin 3) (Fin 3) F)).map
      (Matrix.GeneralLinearGroup.toLin : GL (Fin 3) F ≃* _).toMonoidHom =
      sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 3) (Fin 3) F)) := by
    ext g
    rw [Subgroup.mem_map_equiv, ← toLin_mem_sesqSpecialUnitaryGroup_iff h 1,
      MulEquiv.apply_symm_apply]
  let e : gramSU h (1 : Matrix (Fin 3) (Fin 3) F) ≃*
      sesqSpecialUnitaryGroup (gramForm h (1 : Matrix (Fin 3) (Fin 3) F)) :=
    (Matrix.GeneralLinearGroup.toLin.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  rw [statedSU_eq_gramSU hF h]
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem classicalModel_statedSU (hF : Nat.card F = 9) :
    StatedClassicalModel (StatedSU 3 3 F) .PSU 3 3 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  refine ⟨⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩, ?_⟩
  exact ⟨F, inferInstance, inferInstance, card_eq_sq_pow hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSU_eq_bot hF)).trans
      QuotientGroup.quotientBot).symm⟩⟩

end CFSG.LinearGroups.UnitaryThreeOverNine
