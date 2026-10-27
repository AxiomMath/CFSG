module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2PocketAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [FiniteDimensional (ZMod 3) U]
  {R : QuadraticForm (ZMod 3) U}

theorem normal_map_orthogonalGroupCongr (hR : R.Nondegenerate) (e : detForm.IsometryEquiv R)
    {K : Subgroup (OGroup detForm)} (hKle : K ≤ omegaGroup detForm_nondegenerate)
    (hKn : (K.subgroupOf (omegaGroup detForm_nondegenerate)).Normal) :
    ((K.map (TauCeti.QuadraticMap.orthogonalGroupCongr e).toMonoidHom).subgroupOf
      (omegaGroup hR)).Normal := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) Mat2 := by
    rw [finrank_mat2]
    norm_num
  have hΩ := mem_omegaGroup_orthogonalGroupCongr_iff detForm_nondegenerate hR h2 e
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨n₀, hn₀, hnφ⟩ := hn
  have hg₀ : (TauCeti.QuadraticMap.orthogonalGroupCongr e).symm (g : OGroup R) ∈
      omegaGroup detForm_nondegenerate := by
    rw [← hΩ, MulEquiv.apply_symm_apply]
    exact g.2
  have hc := hKn.conj_mem ⟨n₀, hKle hn₀⟩ (Subgroup.mem_subgroupOf.mpr hn₀)
    ⟨(TauCeti.QuadraticMap.orthogonalGroupCongr e).symm (g : OGroup R), hg₀⟩
  rw [Subgroup.mem_subgroupOf] at hc
  refine ⟨_, hc, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] at hnφ ⊢
  rw [hnφ]

theorem exists_plus4_block (hR : R.Nondegenerate) (hdim : Module.finrank (ZMod 3) U = 4)
    (hsign : quadSign R = 1) :
    ∃ κL κR : SL2F3 →* OGroup R,
      (∀ A, κL A ∈ omegaGroup hR) ∧ (∀ B, κR B ∈ omegaGroup hR) ∧
      Function.Injective κL ∧ Function.Injective κR ∧
      κL sl2f3NegOne = piOrth R ∧ κR sl2f3NegOne = piOrth R ∧
      ((κL.range).subgroupOf (omegaGroup hR)).Normal ∧
      ((κR.range).subgroupOf (omegaGroup hR)).Normal ∧
      (∀ A B, κL A * κR B = κR B * κL A) ∧
      (∀ c : ZMod 3, ∃ a : U, R a = c) ∧
      (∀ a : U, R a ≠ 0 → ∃ A B : SL2F3, A * A = sl2f3NegOne ∧ B * B = sl2f3NegOne ∧
        ((κL A * κR B : OGroup R) : U ≃ₗ[ZMod 3] U) a = a) ∧
      (∀ A B : SL2F3, A * A = sl2f3NegOne → B * B = sl2f3NegOne →
        κL A * κR B ≠ 1 ∧ κL A * κR B ≠ piOrth R) := by
  obtain ⟨e⟩ := equivalent_of_quadSign_eq detForm_nondegenerate hR
    (finrank_mat2.trans hdim.symm) (quadSign_detForm.trans hsign.symm)
  have h2 : 2 ≤ Module.finrank (ZMod 3) Mat2 := by
    rw [finrank_mat2]
    norm_num
  have hΩ := mem_omegaGroup_orthogonalGroupCongr_iff detForm_nondegenerate hR h2 e
  let Φ := TauCeti.QuadraticMap.orthogonalGroupCongr e
  have hleΩ : leftMulHom.range ≤ omegaGroup detForm_nondegenerate := by
    rintro _ ⟨A, rfl⟩
    exact leftMulHom_mem_omegaGroup A
  have hriΩ : rightMulHom.range ≤ omegaGroup detForm_nondegenerate := by
    rintro _ ⟨B, rfl⟩
    exact rightMulHom_mem_omegaGroup B
  refine ⟨Φ.toMonoidHom.comp leftMulHom, Φ.toMonoidHom.comp rightMulHom,
    fun A => (hΩ _).mpr (leftMulHom_mem_omegaGroup A),
    fun B => (hΩ _).mpr (rightMulHom_mem_omegaGroup B),
    Φ.injective.comp leftMulHom_injective, Φ.injective.comp rightMulHom_injective, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · show Φ (leftMulHom sl2f3NegOne) = piOrth R
    rw [leftMulHom_eq_piOrth coe_sl2f3NegOne]
    exact orthogonalGroupCongr_piOrth e
  · show Φ (rightMulHom sl2f3NegOne) = piOrth R
    rw [rightMulHom_sl2f3NegOne]
    exact orthogonalGroupCongr_piOrth e
  · rw [← MonoidHom.map_range]
    exact normal_map_orthogonalGroupCongr hR e hleΩ leftMulHom_range_normal
  · rw [← MonoidHom.map_range]
    exact normal_map_orthogonalGroupCongr hR e hriΩ rightMulHom_range_normal
  · intro A B
    show Φ (leftMulHom A) * Φ (rightMulHom B) = Φ (rightMulHom B) * Φ (leftMulHom A)
    rw [← map_mul, ← map_mul, leftMulHom_mul_rightMulHom_comm]
  · intro c
    obtain ⟨X, hX⟩ := exists_det_eq c
    refine ⟨e.toLinearEquiv X, ?_⟩
    exact (e.map_app X).trans hX
  · intro a ha
    have hdetX : detForm (e.toLinearEquiv.symm a) = R a := by
      have h : R (e.toLinearEquiv (e.toLinearEquiv.symm a)) =
          detForm (e.toLinearEquiv.symm a) := e.map_app (e.toLinearEquiv.symm a)
      rw [e.toLinearEquiv.apply_symm_apply] at h
      exact h.symm
    have hX : (e.toLinearEquiv.symm a).det ≠ 0 := by
      rw [← detForm_apply, hdetX]
      exact ha
    obtain ⟨A, B, hA, hB, hfix⟩ := exists_fixing_pair _ hX
    refine ⟨A, B, hA, hB, ?_⟩
    show ((Φ (leftMulHom A) * Φ (rightMulHom B) : OGroup R) : U ≃ₗ[ZMod 3] U) a = a
    rw [← map_mul, TauCeti.QuadraticMap.coe_orthogonalGroupCongr_apply, leftRight_apply, hfix]
    exact LinearEquiv.apply_symm_apply _ _
  · intro A B hA hB
    refine ⟨fun h => leftRight_ne_one hA hB (Φ.injective ?_),
      fun h => leftRight_ne_piOrth hA hB (Φ.injective ?_)⟩
    · rw [map_mul, map_one]
      exact h
    · rw [map_mul, orthogonalGroupCongr_piOrth e]
      exact h

end CFSG.OddStandard.SmallF3.Omega
