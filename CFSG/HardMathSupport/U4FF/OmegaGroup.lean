module

public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap CFSG.Open

section

variable {F : Type} [Field F] [Finite F] {b c : F}

theorem commutator_orthogonalGroup_quadMinus_three (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) = 0) (hperf : Group.IsPerfect ↥(elementaryGroup (quadMinus 3 F b c))) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 3 F b c)⁆ =
        elementaryGroup (quadMinus 3 F b c) := by
  have hn0 : 0 < 3 - 1 := by norm_num
  have hnd := nondegenerate_polarBilin_quadMinus_of_finite 3 F hirr
  have hgen := orthogonalGroup_le_closure_of_two_eq_zero (minusFamily_orth (K := F) (b := b)
    (c := c) hn0) hnd h2
    (fun x hx hQ => eq_zero_of_mem_tailSpace_minusFamily hirr hn0 hx hQ)
    (fun x hx hx0 y hy hxy => exists_eq_smul_of_mem_tailSpace_minusFamily h2 hirr hn0 hx hx0 hy
      hxy) (by norm_num : 1 ≤ 3 - 1)
  have hpair : (minusPair F b c (⟨0, by omega⟩ : Fin (3 - 1))).Orth
      (minusPair F b c (⟨1, by omega⟩ : Fin (3 - 1))) :=
    minusPair_orth (by simp [Fin.ext_iff])
  apply le_antisymm
  · refine commutator_le_of_le_closure (fun g hg x hx => conj_mem_elementaryGroup hg hx)
      (elementaryGroup_le_orthogonalGroup _) ?_ hgen ?_
    · rintro _ ⟨v, rfl⟩
      exact reflect_mem_orthogonalGroup _ v
    · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      exact commutatorElement_reflect_mem hnd hpair u v
  · calc elementaryGroup (quadMinus 3 F b c)
        = ⁅elementaryGroup (quadMinus 3 F b c), elementaryGroup (quadMinus 3 F b c)⁆ :=
          (Subgroup.commutator_eq_self).symm
      _ ≤ _ := Subgroup.commutator_mono (elementaryGroup_le_orthogonalGroup _)
        (elementaryGroup_le_orthogonalGroup _)

theorem spinMatrix_quadMinus_three_injective (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) = 0) : Function.Injective (spinMatrix (quadMinus 3 F b c)) := by
  have hcent := isCentral_cliffordAlgebra_quadMinus 3 b c hirr
  rw [← MonoidHom.ker_eq_bot_iff, ker_spinMatrix]
  exact ker_spinAction_eq_bot_of_isCentral _ h2

theorem range_spinMatrix_quadMinus_three (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) = 0) (hSpin : Group.IsPerfect (spinGroup (quadMinus 3 F b c))) :
    (spinMatrix (quadMinus 3 F b c)).range = StatedOmega (StatedQuadMinus 3 F b c) := by
  have hR := CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three (F := F) (b := b)
    (c := c) hirr
  have hperf : Group.IsPerfect ↥(elementaryGroup (quadMinus 3 F b c)) := by
    have := Group.IsPerfect.range (spinAction (quadMinus 3 F b c))
    rwa [hR] at this
  exact range_spinMatrix_eq_statedOmega (coe_quadMinus 3 F b c)
    (commutator_orthogonalGroup_quadMinus_three hirr h2 hperf) hR

@[expose] noncomputable def spinMinusThreeEquiv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (h2 : (2 : F) = 0) (hSpin : Group.IsPerfect (spinGroup (quadMinus 3 F b c))) :
    spinGroup (quadMinus 3 F b c) ≃* StatedOmega (StatedQuadMinus 3 F b c) :=
  (MonoidHom.ofInjective (spinMatrix_quadMinus_three_injective hirr h2)).trans
    (MulEquiv.subgroupCongr (range_spinMatrix_quadMinus_three hirr h2 hSpin))

theorem coe_spinMinusThreeEquiv (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : F) = 0)
    (hSpin : Group.IsPerfect (spinGroup (quadMinus 3 F b c))) (s : spinGroup (quadMinus 3 F b c)) :
    ((spinMinusThreeEquiv hirr h2 hSpin s : StatedOmega (StatedQuadMinus 3 F b c)) :
      GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) F) = spinMatrix (quadMinus 3 F b c) s :=
  rfl

end

end CFSG.HardMathSupport.U4FF
