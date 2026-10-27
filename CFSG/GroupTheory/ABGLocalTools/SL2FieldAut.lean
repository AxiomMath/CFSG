module

public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutPGammaL
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQFieldAutBorel
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ABGLocalTools

open Matrix CFSG.GorensteinWalter CFSG.QuasiDihedralFusion

theorem isOddPrimePower_card_of_odd {F : Type*} [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    IsOddPrimePower (Nat.card F) := by
  obtain ⟨f, hf, hq⟩ := card_eq_ringChar_pow (F := F)
  refine ⟨ringChar F, f, ringChar_prime, ?_, hf, hq⟩
  exact ringChar_prime.odd_of_ne_two (ringChar_ne_two_of_odd_card hodd)

theorem sl2FieldAutomorphism : SL2FieldAutomorphism := by
  intro F _ _ p _ hp hodd hpq α hαp hαinner
  have hpp : p.Prime := Fact.out
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_card hodd
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases (show Nat.card F = 3 ∨ 3 < Nat.card F by
      obtain ⟨k, hk⟩ := hodd
      omega) with h3 | h3
  · exfalso
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hpq ⟨1, by rw [h3]⟩
    exact hαinner 1 (by rw [mulAut_eq_one_of_card_three h3 hp hp3 α hαp, map_one])
  have hK := isOddPrimePower_card_of_odd hodd
  obtain ⟨f, -, hKcard⟩ := card_eq_ringChar_pow (F := F)
  have : Fact (ringChar F).Prime := ⟨ringChar_prime⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F hKcard hK h3 (psl2MulAutOf α)
  have hγp : γ ^ p = 1 := by
    apply pGammaL2ToMulAutPSL2_injective F hK h3
    rw [map_pow, hγ, psl2MulAutOf_pow_eq_one hαp, map_one]
  obtain ⟨G, hG⟩ := ProjGenLinGroup.mk_surjective γ.left
  have hσp : γ.right ^ p = 1 := by
    rw [← pGammaL2_pow_right, hγp, SemidirectProduct.one_right]
  by_cases hσ : γ.right = 1
  · exfalso
    have hpowl : ∀ k : ℕ, (γ ^ k).left = γ.left ^ k := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, SemidirectProduct.one_left]
      | succ k ih =>
        rw [pow_succ, SemidirectProduct.mul_left, ih, pGammaL2_pow_right, hσ, one_pow, map_one,
          MulAut.one_apply, pow_succ]
    have hgp : γ.left ^ p = 1 := by
      rw [← hpowl, hγp, SemidirectProduct.one_left]
    have hgsq : γ.left = (γ.left ^ ((p + 1) / 2)) ^ 2 := by
      obtain ⟨m, hm⟩ := hpp.odd_of_ne_two hp
      rw [← pow_mul, show (p + 1) / 2 * 2 = p + 1 by omega, pow_succ, hgp, one_mul]
    obtain ⟨j, hj⟩ : γ.left ∈ (Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin 2) F →* ProjGenLinGroup (Fin 2) F).range := by
      rw [hgsq]
      exact sq_mem_range_toPGL _
    have hG' : ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL j) = γ.left := hj
    have hαj := coe_mulAut_eq_smul_conj hK h3 α γ hγ _ hG'
    apply hαinner j
    apply eq_conj_of_inv_mul_conj_mem_center hF2 α j
    intro b
    obtain ⟨u, hu, hub⟩ := hαj b
    have hmap : (b : Matrix (Fin 2) (Fin 2) F).map γ.right = b := by
      rw [hσ]
      ext i k
      rfl
    have hinv : (((Matrix.SpecialLinearGroup.toGL j)⁻¹ : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = ((j⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := by
      rw [← map_inv]
      rfl
    rw [hmap, hinv] at hub
    change ((α b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      u • (((j * b * j⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F)
      at hub
    set A := α b
    set B := j * b * j⁻¹
    have hAA : ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hAB : ((A⁻¹ * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        u⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hub, Matrix.mul_smul] at hAA
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hAA, smul_smul, inv_mul_cancel₀ hu, one_smul]
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨u⁻¹, ?_, ?_⟩
    · have hdet := congrArg Matrix.det hAB
      rw [Matrix.SpecialLinearGroup.det_coe, Matrix.det_smul, Matrix.det_one, mul_one,
        Fintype.card_fin] at hdet
      exact hdet.symm
    · rw [hAB, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · have hσord : orderOf γ.right = p := orderOf_eq_prime hσp hσ
    have hN := pGammaL2_pow_left γ G hG p
    rw [hγp, SemidirectProduct.one_left] at hN
    have hNc : glNorm γ.right G p ∈ Subgroup.center (GL (Fin 2) F) :=
      ProjGenLinGroup.mk_eq_one.mp hN.symm
    obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hNc
    obtain ⟨v, hv, μ, hGv⟩ := exists_eigenvector_of_glNorm_scalar γ.right G
      (c := c) (by rw [hσord]; exact hc.symm)
    exact exists_borel_of_semilinear_eigenvector hodd hp hpq α γ.right hσ G
      (coe_mulAut_eq_smul_conj hK h3 α γ hγ G hG) hv hGv

end CFSG.ABGLocalTools
