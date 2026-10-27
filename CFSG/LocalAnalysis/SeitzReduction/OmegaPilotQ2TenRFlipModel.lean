module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRFlip

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (reflect reflect_apply elementaryGroup)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived
  matrixProjectiveProjection)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus minusIndexEquiv plusIndexEquiv)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)

section Reflect

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem IsAnisoCoord.reflect_eq_swapLin {a a' : Fin d} (h : IsAnisoCoord Q a a' 1 1) :
    reflect Q (Pi.single a 1 + Pi.single a' 1) = swapLin a a' := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ1 : Q (Pi.single a 1 + Pi.single a' 1) = 1 := by
    rw [QuadraticMap.map_add Q, h.map_left, h.map_right, h.polar_left, Pi.single_eq_same]
    linear_combination h2
  ext x i
  rw [reflect_apply (by rw [hQ1]; exact one_ne_zero), hQ1, div_one, polar_add_left, h.polar_left,
    h.polar_right, swapLin_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, one_mul]
  by_cases hia : i = a
  · subst hia
    rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne h.ne]
    linear_combination (-x a') * h2
  · by_cases hib : i = a'
    · subst hib
      rw [Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm h.ne)]
      linear_combination (-x a) * h2
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]
      ring

theorem IsHypCoord.reflect_eq_swapLin {e f : Fin d} (h : IsHypCoord Q e f) :
    reflect Q (Pi.single e 1 + Pi.single f 1) = swapLin e f := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ1 : Q (Pi.single e 1 + Pi.single f 1) = 1 := by
    rw [QuadraticMap.map_add Q, h.map_left, h.map_right, h.polar_left, Pi.single_eq_same]
    ring
  ext x i
  rw [reflect_apply (by rw [hQ1]; exact one_ne_zero), hQ1, div_one, polar_add_left, h.polar_left,
    h.polar_right, swapLin_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  by_cases hia : i = e
  · subst hia
    rw [Equiv.swap_apply_left, Pi.single_eq_same, Pi.single_eq_of_ne h.ne]
    linear_combination (-x f) * h2
  · by_cases hib : i = f
    · subst hib
      rw [Equiv.swap_apply_right, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm h.ne)]
      linear_combination (-x e) * h2
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib, Pi.single_eq_of_ne hia, Pi.single_eq_of_ne hib]
      ring

theorem doubleFlip_aniso_mem_orthDerived [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {a a' e f e' f' : Fin d} (h : IsAnisoCoord Q a a' 1 1) (hP : IsHypCoord Q e f)
    (hP' : IsHypCoord Q e' f') (hd : PairDisjoint e f e' f') :
    doubleFlip (K := K) a a' e f ∈ orthDerived Q := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQa : Q (Pi.single a 1 + Pi.single a' 1) = 1 := by
    rw [QuadraticMap.map_add Q, h.map_left, h.map_right, h.polar_left, Pi.single_eq_same]
    linear_combination h2
  have hQe : Q (Pi.single e 1 + Pi.single f 1) = 1 := by
    rw [QuadraticMap.map_add Q, hP.map_left, hP.map_right, hP.polar_left, Pi.single_eq_same]
    ring
  have hW : doubleFlip (K := K) a a' e f =
      reflect Q (Pi.single a 1 + Pi.single a' 1) * reflect Q (Pi.single e 1 + Pi.single f 1) := by
    rw [h.reflect_eq_swapLin, hP.reflect_eq_swapLin]
    rfl
  rw [hW]
  refine elementaryGroup_le_orthDerived hQ hT
    (CFSG.LieType.Universal.Spin.reflect_mul_reflect_mem_of_eq_sq_mul hQ (hP.orth hP' hd)
      (by rw [hQe]; exact one_ne_zero) one_ne_zero ?_)
  rw [hQa, hQe, one_pow, one_mul]

end Reflect

section Torus

variable {K : Type} [Field K] [CharP K 2] {d : ℕ}

theorem doubleFlip_anisoRotLin {a a' e f : Fin d} (hd : PairDisjoint a a' e f) (hne : a ≠ a')
    (p s : K) (v : Fin d → K) :
    doubleFlip a a' e f (anisoRotLin a a' 1 1 p s (doubleFlip a a' e f v)) =
      anisoRotLin a a' 1 1 (p + s) s v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hea := hd.left_ne_left
  have hea' := hd.left_ne_right
  have hfa := hd.right_ne_left
  have hfa' := hd.right_ne_right
  have hσa : Equiv.swap e f (Equiv.swap a a' a) = a' := by
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hea') (Ne.symm hfa')]
  have hσa' : Equiv.swap e f (Equiv.swap a a' a') = a := by
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm hea) (Ne.symm hfa)]
  funext i
  rw [doubleFlip_apply]
  by_cases hia : i = a
  · rw [hia, hσa, anisoRotLin_apply_right hne, doubleFlip_apply, doubleFlip_apply, hσa, hσa',
      anisoRotLin_apply_left]
    ring
  · by_cases hib : i = a'
    · rw [hib, hσa', anisoRotLin_apply_left, doubleFlip_apply, doubleFlip_apply, hσa, hσa',
        anisoRotLin_apply_right hne]
      linear_combination (-(s * v a')) * h2
    · have hσi : Equiv.swap e f (Equiv.swap a a' i) = Equiv.swap e f i := by
        rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      have hσia : Equiv.swap e f i ≠ a := by
        intro h'
        have := congrArg (Equiv.swap e f) h'
        rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne (Ne.symm hea) (Ne.symm hfa)]
          at this
        exact hia this
      have hσia' : Equiv.swap e f i ≠ a' := by
        intro h'
        have := congrArg (Equiv.swap e f) h'
        rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne (Ne.symm hea') (Ne.symm hfa')]
          at this
        exact hib this
      rw [hσi, anisoRotLin_apply_of_ne hσia hσia', doubleFlip_apply,
        Equiv.swap_apply_of_ne_of_ne hσia hσia', Equiv.swap_apply_self,
        anisoRotLin_apply_of_ne hia hib]

variable [Finite K] {Q : QuadraticForm K (Fin d → K)}

theorem projHom_doubleFlip_mem_normalizer_anisoTorusOf {a a' e f : Fin d}
    (hd : PairDisjoint a a' e f) (hne : a ≠ a')
    (hw : doubleFlip (K := K) a a' e f ∈ orthDerived Q) :
    projHom Q ⟨_, hw⟩ ∈ normalizer (anisoTorusOf Q hne 1 1 : Set (matrixProjectiveDerived Q)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine mem_normalizer_of_map_conj_le_of_mul_self (projHom_doubleFlip_mul_self hd hw) ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨p, s, hN, hg⟩ := mem_subgroupOf.1 hx
  refine ⟨⟨_, hw⟩ * x * ⟨_, hw⟩⁻¹, mem_subgroupOf.2 ⟨p + s, s, ?_, fun v => ?_⟩, ?_⟩
  · linear_combination hN + (p * s + s ^ 2) * h2
  · change ((doubleFlip (K := K) a a' e f * (x : (Fin d → K) ≃ₗ[K] (Fin d → K)) *
      (doubleFlip (K := K) a a' e f)⁻¹ : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) = _
    rw [doubleFlip_inv hd, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hg,
      doubleFlip_anisoRotLin hd hne]
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

end Torus

section Perp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem swap_swap_anisoPerpCoord (hn : 1 ≤ n) (ℓ : Fin (n - 1)) (x : Fin (2 * (n - 1))) :
    Equiv.swap (minusIndexEquiv n hn (.inl ℓ)) (minusIndexEquiv n hn (.inr (.inl ℓ)))
        (Equiv.swap (anisoCoordLeft hn) (anisoCoordRight hn) (anisoPerpCoord hn x)) =
      anisoPerpCoord hn (Equiv.swap (plusIndexEquiv (n - 1) (.inl ℓ))
        (plusIndexEquiv (n - 1) (.inr ℓ)) x) := by
  rw [Equiv.swap_apply_of_ne_of_ne (anisoPerpCoord_ne_left hn x) (anisoPerpCoord_ne_right hn x)]
  have he : anisoPerpCoord hn (plusIndexEquiv (n - 1) (.inl ℓ)) =
      minusIndexEquiv n hn (.inl ℓ) := by
    simp [anisoPerpCoord]
  have hf : anisoPerpCoord hn (plusIndexEquiv (n - 1) (.inr ℓ)) =
      minusIndexEquiv n hn (.inr (.inl ℓ)) := by
    simp [anisoPerpCoord]
  rw [← he, ← hf, (anisoPerpCoord_injective hn).swap_apply]

theorem doubleFlip_extend_aniso (hn : 1 ≤ n) (ℓ : Fin (n - 1)) (v : Fin (2 * (n - 1)) → K) :
    doubleFlip (anisoCoordLeft hn) (anisoCoordRight hn) (minusIndexEquiv n hn (.inl ℓ))
        (minusIndexEquiv n hn (.inr (.inl ℓ))) (Function.extend (anisoPerpCoord hn) v 0) =
      Function.extend (anisoPerpCoord hn)
        (swapLin (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) v) 0 := by
  have hd := pairDisjoint_aniso hn ℓ
  funext p
  rw [doubleFlip_apply]
  by_cases hp : ∃ x, anisoPerpCoord hn x = p
  · obtain ⟨x, rfl⟩ := hp
    rw [swap_swap_anisoPerpCoord, (anisoPerpCoord_injective hn).extend_apply,
      (anisoPerpCoord_injective hn).extend_apply, swapLin_apply]
  · rw [Function.extend_apply' _ _ _ hp, Function.extend_apply' _ _ _ ?_]
    · rfl
    rintro ⟨x, hx⟩
    apply hp
    refine ⟨Equiv.swap (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) x, ?_⟩
    rw [← swap_swap_anisoPerpCoord, hx, swap_comm_of_pairDisjoint hd, Equiv.swap_apply_self,
      Equiv.swap_apply_self]

theorem anisoPerpEquiv_conj_doubleFlip (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ℓ : Fin (n - 1))
    (w y : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hw : (w : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
      doubleFlip (anisoCoordLeft (by omega)) (anisoCoordRight (by omega))
        (minusIndexEquiv n (by omega) (.inl ℓ)) (minusIndexEquiv n (by omega) (.inr (.inl ℓ))))
    (x x' : anisoPerp (K := K) (by omega : 1 ≤ n) b c)
    (hy : (y : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (anisoCoordLeft (by omega : 1 ≤ n)) (anisoCoordRight (by omega : 1 ≤ n)))
    (hxy : (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ y)
    (hy' : ((w * y * w⁻¹ : orthDerived (coordinateQuadMinus n K (by omega) b c)) :
        (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (anisoCoordLeft (by omega : 1 ≤ n)) (anisoCoordRight (by omega : 1 ≤ n)))
    (hx'y : (x' : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) =
      projHom _ (w * y * w⁻¹)) :
    ((anisoPerpEquiv hn hirr x' : orthDerived (coordinateQuadPlus (n - 1) K)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) =
      swapLin (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) *
        ((anisoPerpEquiv hn hirr x : orthDerived (coordinateQuadPlus (n - 1) K)) :
          (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) *
        swapLin (plusIndexEquiv (n - 1) (.inl ℓ)) (plusIndexEquiv (n - 1) (.inr ℓ)) := by
  have hd := pairDisjoint_aniso (by omega : 1 ≤ n) ℓ
  have hcoe : ((w * y * w⁻¹ : orthDerived (coordinateQuadMinus n K (by omega) b c)) :
      (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
      doubleFlip (anisoCoordLeft (by omega)) (anisoCoordRight (by omega))
          (minusIndexEquiv n (by omega) (.inl ℓ)) (minusIndexEquiv n (by omega) (.inr (.inl ℓ))) *
        (y : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) *
      doubleFlip (anisoCoordLeft (by omega)) (anisoCoordRight (by omega))
        (minusIndexEquiv n (by omega) (.inl ℓ)) (minusIndexEquiv n (by omega) (.inr (.inl ℓ))) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw, doubleFlip_inv hd]
  ext v z
  rw [anisoPerpEquiv_apply hn hirr x' _ hy' hx'y v z, hcoe]
  simp only [LinearEquiv.mul_apply]
  rw [swapLin_apply, anisoPerpEquiv_apply hn hirr x y hy hxy, doubleFlip_extend_aniso,
    doubleFlip_apply, swap_swap_anisoPerpCoord]

theorem anisoPerpModelEquiv_conj_doubleFlip (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (w : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hw : (w : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) =
      doubleFlip (anisoCoordLeft (by omega)) (anisoCoordRight (by omega))
        (minusIndexEquiv n (by omega) (.inl ⟨n - 1 - 1, by omega⟩))
        (minusIndexEquiv n (by omega) (.inr (.inl ⟨n - 1 - 1, by omega⟩))))
    (x x' : anisoPerp (K := K) (by omega : 1 ≤ n) b c)
    (hxx' : (x' : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) =
      projHom _ w * x * (projHom _ w)⁻¹) :
    anisoPerpModelEquiv hn hirr x' =
      plusFlipAut (n - 1) K (by omega) (anisoPerpModelEquiv hn hirr x) := by
  have hd := pairDisjoint_aniso (by omega : 1 ≤ n) (⟨n - 1 - 1, by omega⟩ : Fin (n - 1))
  obtain ⟨y, hy, hyx⟩ := x.2
  have hy' : w * y * w⁻¹ ∈ (stabSub (K := K) (anisoCoordLeft (by omega : 1 ≤ n))
      (anisoCoordRight (by omega : 1 ≤ n))).subgroupOf
        (orthDerived (coordinateQuadMinus n K _ b c)) := by
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw]
    exact doubleFlip_conj_mem_stabSub hd (mem_subgroupOf.1 hy)
  have hx'y : (x' : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) =
      projHom _ (w * y * w⁻¹) := by
    rw [hxx', map_mul, map_mul, map_inv, hyx]
  have hconj := anisoPerpEquiv_conj_doubleFlip hn hirr ⟨n - 1 - 1, by omega⟩ w y hw x x'
    (mem_subgroupOf.1 hy) hyx.symm (mem_subgroupOf.1 hy') hx'y
  have hz : swapLin (K := K) (plusIndexEquiv (n - 1) (.inl ⟨n - 1 - 1, by omega⟩))
        (plusIndexEquiv (n - 1) (.inr ⟨n - 1 - 1, by omega⟩)) *
        ((anisoPerpEquiv hn hirr x : orthDerived (coordinateQuadPlus (n - 1) K)) :
          (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) *
        swapLin (plusIndexEquiv (n - 1) (.inl ⟨n - 1 - 1, by omega⟩))
          (plusIndexEquiv (n - 1) (.inr ⟨n - 1 - 1, by omega⟩)) ∈
      orthDerived (coordinateQuadPlus (n - 1) K) := by
    rw [← hconj]
    exact (anisoPerpEquiv hn hirr x').2
  change projHom _ (anisoPerpEquiv hn hirr x') =
    plusFlipAut (n - 1) K (by omega) (projHom _ (anisoPerpEquiv hn hirr x))
  rw [plusFlipAut_projHom (by omega) (anisoPerpEquiv hn hirr x) hz]
  congr 1
  exact Subtype.ext hconj

end Perp

section Congr

variable {K : Type} [Field K] [CharP K 2] {k₀ : Type} [Field k₀] [CharP k₀ 2]

theorem plusCongr_statedOmegaPlusEquiv (φ : K ≃+* k₀) {m : ℕ} (hm : 1 ≤ m)
    (A : StatedOmega (StatedQuadPlus m K)) :
    plusCongr φ m (statedOmegaPlusEquiv K m hm A) =
      statedOmegaPlusEquiv k₀ m hm (statedOmegaPlusCongr φ m A) := by
  change matrixProjectiveCongr φ _ (matrixProjectiveProjection _ (statedDerivedPlusEquiv K m A)) =
    matrixProjectiveProjection _ (statedDerivedPlusEquiv k₀ m (statedOmegaPlusCongr φ m A))
  apply matrixProjectiveCongr_mk
  apply Units.ext
  ext a b
  obtain ⟨i, rfl⟩ := (plusIndexEquiv m).surjective a
  obtain ⟨j, rfl⟩ := (plusIndexEquiv m).surjective b
  have h1 := statedDerivedPlusEquiv_symm_entry k₀ m
    (statedDerivedPlusEquiv k₀ m (statedOmegaPlusCongr φ m A)) i j
  have h2 := statedDerivedPlusEquiv_symm_entry K m (statedDerivedPlusEquiv K m A) i j
  rw [MulEquiv.symm_apply_apply] at h1 h2
  rw [← h1, glCongr_coe, Matrix.map_apply, ← h2, coe_statedOmegaPlusCongr, glCongr_coe,
    Matrix.map_apply]

theorem plusCongr_plusFlipAut (φ : K ≃+* k₀) {m : ℕ} (hm : 1 ≤ m)
    (u : matrixProjectiveDerived (coordinateQuadPlus m K)) :
    plusCongr φ m (plusFlipAut m K (by omega) u) =
      plusFlipAut m k₀ (by omega) (plusCongr φ m u) := by
  obtain ⟨A, rfl⟩ := (statedOmegaPlusEquiv K m hm).surjective u
  rw [plusFlipAut_statedOmegaPlusEquiv m K hm, plusCongr_statedOmegaPlusEquiv φ hm,
    plusCongr_statedOmegaPlusEquiv φ hm, plusFlipAut_statedOmegaPlusEquiv m k₀ hm,
    statedOmegaPlusCongr_plusSwapDerived]

end Congr

theorem omegaMinusTwoTenFlipModelInput_holds : OmegaMinusTwoTenFlipModelInput := by
  intro K _ _ _ b c hirr hK2 k₀ _ _ _ φ
  obtain rfl : b = 1 := eq_one_of_ne_zero_of_card_two hK2 (coeff_ne_zero_of_irreducible' hirr)
  obtain rfl : c = 1 := eq_one_of_ne_zero_of_card_two hK2 (by
    intro h
    apply hirr 0
    rw [h]
    ring)
  have hreg :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      5 K 1 1 (by norm_num) hirr
  have hA := isAnisoCoord_coordinateQuadMinus (K := K) (by norm_num : 1 ≤ 5) hirr
  have hP := isHypCoord_coordinateQuadMinus (K := K) (by norm_num : 1 ≤ 5) 1 1
    (⟨5 - 1 - 1, by norm_num⟩ : Fin (5 - 1))
  have hP' := isHypCoord_coordinateQuadMinus (K := K) (by norm_num : 1 ≤ 5) 1 1
    (⟨0, by norm_num⟩ : Fin (5 - 1))
  have hd := pairDisjoint_minus (by norm_num : 1 ≤ 5)
    (i := (⟨5 - 1 - 1, by norm_num⟩ : Fin (5 - 1))) (j := ⟨0, by norm_num⟩) (by decide)
  have hw := doubleFlip_aniso_mem_orthDerived hreg.1 hreg.2 hA hP hP' hd
  have hdA := pairDisjoint_aniso (by norm_num : 1 ≤ 5) (⟨5 - 1 - 1, by norm_num⟩ : Fin (5 - 1))
  refine ⟨projHom _ ⟨_, hw⟩,
    projHom_doubleFlip_mem_normalizer_anisoTorusOf hdA (anisoCoord_ne _) hw,
    projHom_doubleFlip_mem_normalizer_pairPerpOf hdA hw, fun x x' hxx' => ?_⟩
  rw [anisoPerpModelEquiv_conj_doubleFlip (by norm_num) hirr ⟨_, hw⟩ rfl x x' hxx',
    plusCongr_plusFlipAut φ (by norm_num)]

end CFSG.SeitzReduction.OmegaPilot
