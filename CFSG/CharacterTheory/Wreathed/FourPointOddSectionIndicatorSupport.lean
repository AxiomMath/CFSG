module

public import CFSG.CharacterTheory.Wreathed.FourPointOrderFourSupport
public import CFSG.CharacterTheory.Wreathed.ConditionalCompatibleModelData

public noncomputable section

namespace CFSG.Wreathed.FourPointOddSectionIndicator

open Equiv CFSG.Semidihedral.FourPointLifts
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.FourPointCompleteModel
open CFSG.Wreathed.FourPointOrderFour

open scoped Classical

theorem eq_of_sign_eq_one_of_sq_eq_one : ∀ σ : Perm (Fin 4), Perm.sign σ = 1 → σ ^ 2 = 1 →
    σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 0 3 * swap 1 2 := by
  decide

theorem mem_fourKlein_of_sign_eq_one_of_sq_eq_one {σ : Perm (Fin 4)} (hs : Perm.sign σ = 1)
    (hsq : σ ^ 2 = 1) : σ ∈ fourKlein :=
  (mem_fourKlein σ).mpr (eq_of_sign_eq_one_of_sq_eq_one σ hs hsq)

variable {G : Type} [Group G] [Finite G]

theorem centralInvolution_mem_fourPointQ (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (alpha : centralizerFullQuotient n hn S e ≃* Perm (Fin 4)) :
    centralizerOddCoreMap n S e (centralInvolution n S e) ∈
      fourKlein.comap (alpha.toMonoidHom.comp (centralizerFullQuotientMap n hn S e)) := by
  have hA : centralizerOddCoreMap n S e (centralInvolution n S e) ∈
      centralizerFullCenterImage n hn S e := by
    rw [← centralizerModelHom_a_pow n hn S e, map_pow]
    exact Subgroup.pow_mem _ (centralizerModelHom_a_mem_fullCenterImage n hn S e) _
  have h1 : centralizerFullQuotientMap n hn S e
      (centralizerOddCoreMap n S e (centralInvolution n S e)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hA
  rw [Subgroup.mem_comap, MonoidHom.comp_apply, h1, map_one]
  exact fourKlein.one_mem

theorem model_weyl_mem_fourPointQ (hn : 2 ≤ 2) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2))
    (alpha : centralizerFullQuotient 2 hn S e ≃* Perm (Fin 4))
    (Φ : CentralExtension (ZMod 3) twoUnit 4 (by norm_num) (by decide) ≃*
      centralizerOddCoreQuotient 2 S e)
    (hΦ : Φ (cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide) ^ 2) =
      centralizerOddCoreMap 2 S e (wreathModelHom (centralizerSylow 2 hn S e)
        (centralizerCoordinates 2 hn S e) (Original.a (2 ^ 2))))
    (h : centralizerOddCoreQuotient 2 S e)
    (hh : h = Φ (cyclicGenerator (ZMod 3) twoUnit 4 (by norm_num) (by decide) ^ 2 *
      specialInclusion (ZMod 3) twoUnit 4 (by norm_num) (by decide)
        (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3))))
    (hh2 : h ^ 2 = 1) :
    h ∈ fourKlein.comap (alpha.toMonoidHom.comp (centralizerFullQuotientMap 2 hn S e)) := by
  have hbot : ∀ σ ∈ (⊥ : Subgroup (ZMod 3 ≃+* ZMod 3)),
      σ ((twoUnit : (ZMod 3)ˣ) : ZMod 3) = twoUnit := by
    intro σ hσ
    rw [Subgroup.mem_bot] at hσ
    subst hσ
    rfl
  let Φ' : SemilinearExtension (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2)
      (wreathModulus_even hn) ⊥ hbot ≃* centralizerOddCoreQuotient 2 S e :=
    (semidirectBotEquiv _).symm.trans Φ
  have hΦ'inl : ∀ w, Φ' (SemidirectProduct.inl w) = Φ w := by
    intro w
    change Φ ((semidirectBotEquiv _).symm (SemidirectProduct.inl w)) = Φ w
    congr 1
    exact (semidirectBotEquiv _).symm_apply_eq.mpr rfl
  obtain ⟨-, hcomm, -⟩ :=
    CFSG.Wreathed.CentralSL2Abelianization.central_SL2_model_derived_subgroup_and_linear_characters
      (ZMod 3) 3 1 Nat.prime_three ⟨1, rfl⟩ le_rfl (by simp) twoUnit twoUnit_not_isSquare (2 ^ 2)
      (by norm_num) (wreathModulus_even hn) ⊥ hbot
  have hJ : (SemidirectProduct.inl (specialInclusion (ZMod 3) twoUnit (2 ^ 2)
      (wreathModulus_pos 2) (wreathModulus_even hn)
        (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3))) :
      SemilinearExtension (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2)
        (wreathModulus_even hn) ⊥ hbot) ∈ commutator _ := by
    rw [hcomm]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  set τ := centralizerFullQuotientMap 2 hn S e with hτ
  set f : SemilinearExtension (ZMod 3) twoUnit (2 ^ 2) (wreathModulus_pos 2)
      (wreathModulus_even hn) ⊥ hbot →* ℤˣ :=
    (Perm.sign.comp (alpha.toMonoidHom.comp τ)).comp Φ'.toMonoidHom with hf
  have hsignJ : Perm.sign (alpha (τ (Φ (specialInclusion (ZMod 3) twoUnit 4 _ _
      (CFSG.Wreathed.CentralSL2Abelianization.weyl (ZMod 3)))))) = 1 := by
    have h1 := Abelianization.commutator_subset_ker f hJ
    rw [MonoidHom.mem_ker] at h1
    rw [← hΦ'inl]
    exact h1
  have hu2 : τ (Φ (cyclicGenerator (ZMod 3) twoUnit 4 _ _ ^ 2)) = 1 := by
    rw [hΦ]
    exact (QuotientGroup.eq_one_iff _).mpr (centralizerModelHom_a_mem_fullCenterImage 2 hn S e)
  have hsign : Perm.sign (alpha (τ h)) = 1 := by
    rw [hh, map_mul, map_mul, hu2, one_mul]
    exact hsignJ
  have hsq : alpha (τ h) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, hh2, map_one, map_one]
  rw [Subgroup.mem_comap]
  exact mem_fourKlein_of_sign_eq_one_of_sq_eq_one hsign hsq

end CFSG.Wreathed.FourPointOddSectionIndicator
