module

public import CFSG.Monster.Existence.Co2Bridge
import all CFSG.Monster.Existence.Co2Bridge
public import CFSG.Monster.Existence.BabyW3Count
public import CFSG.Sporadic.Co2Inv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.Existence.Co2Bridge Matrix

theorem rank_mul_mul_sub_one {m : ℕ} {A P B : Matrix (Fin m) (Fin m) (ZMod 2)}
    (hAB : A * B = 1) : (A * P * B - 1).rank = (P - 1).rank := by
  have e : A * P * B - 1 = A * (P - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse hAB),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hAB)]

theorem rank_sub_one_eq_of_isConj {P z : CFSG.Blueprint.NativeSporadic.Co2} (h : IsConj P z) :
    (z.val.val - 1).rank = (P.val.val - 1).rank := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h1 : c.val.val * (c⁻¹).val.val = 1 := by
    rw [← CFSG.Sporadic.Co2Inv.val_val_mul, mul_inv_cancel]
    rfl
  rw [← hc, CFSG.Sporadic.Co2Inv.val_val_mul, CFSG.Sporadic.Co2Inv.val_val_mul]
  exact rank_mul_mul_sub_one h1

private theorem co2EquivJ22_eq :
    co2EquivJ22 = (Units.mapEquiv (MulEquiv.submonoidCongr seedMonoid_eq) :
      CFSG.Blueprint.NativeSporadic.Co2 ≃* (Submonoid.closure
      ({(gA22 : Matrix (Fin 22) (Fin 22) (ZMod 2)),
        (gB22 : Matrix (Fin 22) (Fin 22) (ZMod 2))} :
        Set (Matrix (Fin 22) (Fin 22) (ZMod 2))))ˣ).trans
      (CFSG.Blueprint.NativeSporadic.unitSeedEquiv gA22 gB22) := rfl

theorem co2EquivJ22_val (r : CFSG.Blueprint.NativeSporadic.Co2) :
    (((co2EquivJ22 r : J22) : GL (Fin 22) (ZMod 2)) : Matrix (Fin 22) (Fin 22) (ZMod 2)) =
      r.val.val := by
  rw [co2EquivJ22_eq, MulEquiv.trans_apply]
  exact (CFSG.Blueprint.NativeSporadic.unitSeedEquiv_val _ _ _).trans
    (CFSG.Monster.Existence.val_mapEquiv_submonoidCongr seedMonoid_eq r)

theorem exists_co2_involution_of_wAct
    {k : Kstab v0} (hk2 : k * k = 1) (hk1 : k ≠ 1) :
    ∃ P : CFSG.Blueprint.NativeSporadic.Co2, P * P = 1 ∧ P ≠ 1 ∧
      ∀ w, wAct v0 k w = theta (P.val.val *ᵥ theta.symm w) := by
  have hmem : wActHom k ∈ J22.map conjHom := by
    rw [map_J22_eq_range]
    exact MonoidHom.mem_range.2 ⟨k, rfl⟩
  obtain ⟨g, hg, hgk⟩ := Subgroup.mem_map.1 hmem
  have hkinv : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
  have hgg : g * g = 1 := by
    apply conjHom_injective
    rw [map_mul, hgk, map_one, ← map_mul, hk2, map_one]
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply hk1
    apply wActHom_injective
    rw [← hgk, map_one, map_one]
  refine ⟨co2EquivJ22.symm ⟨g, hg⟩, ?_, ?_, fun w => ?_⟩
  · rw [← map_mul]
    have h : (⟨g, hg⟩ * ⟨g, hg⟩ : J22) = 1 := Subtype.ext hgg
    rw [h, map_one]
  · intro h
    have h' := congrArg co2EquivJ22 h
    rw [MulEquiv.apply_symm_apply, map_one] at h'
    exact hg1 (congrArg Subtype.val h')
  · have hv := co2EquivJ22_val (co2EquivJ22.symm ⟨g, hg⟩)
    rw [MulEquiv.apply_symm_apply] at hv
    rw [← hv, ← hkinv, ← wActHom_apply, ← hgk, conjHom_apply]

theorem finrank_range_sub_one_of_apply_eq
    (f : Module.End (ZMod 2) (Wv v0)) (M : Matrix (Fin 22) (Fin 22) (ZMod 2))
    (hf : ∀ w, f w = theta (M *ᵥ theta.symm w)) :
    Module.finrank (ZMod 2) (LinearMap.range (f - 1)) = (M - 1).rank := by
  have h : f - 1 = theta.toLinearMap ∘ₗ Matrix.mulVecLin (M - 1) ∘ₗ theta.symm.toLinearMap := by
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    rw [hf w, Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, LinearEquiv.apply_symm_apply]
  rw [h, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearEquiv.finrank_map_eq]
  rfl

theorem six_le_finrank_range_wAct_sub_one
    (k : Kstab v0) (hk2 : k * k = 1) (hk1 : k ≠ 1) :
    6 ≤ Module.finrank (ZMod 2) (LinearMap.range (wAct v0 k - 1)) := by
  obtain ⟨P, hP2, hP1, hPk⟩ := exists_co2_involution_of_wAct hk2 hk1
  rw [finrank_range_sub_one_of_apply_eq _ _ hPk]
  obtain ⟨z, t, u, -, -, -, -, -, -, hz, ht, hu, hconj⟩ :=
    CFSG.Sporadic.Co2Inv.co2_involution_input
  rcases hconj P hP2 hP1 with h | h | h
  · rw [← rank_sub_one_eq_of_isConj h, hz]
  · rw [← rank_sub_one_eq_of_isConj h, ht]
    norm_num
  · rw [← rank_sub_one_eq_of_isConj h, hu]
    norm_num

end CFSG.EvenSporadicStandard.HypOne.BabyHyp
