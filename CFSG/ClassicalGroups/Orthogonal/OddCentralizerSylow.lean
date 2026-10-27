module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualMatrixCore
public import CFSG.RankThree.PartOne.KF.ClsOmega
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal

public section

namespace CFSG.ClassicalGroups.Orthogonal

open Subgroup QuadraticMap
open CFSG.Open
open CFSG.LieType.Universal.Spin (quadMinus quadMinus_apply coe_quadMinus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus plusIndexEquiv regular_coordinateQuadPlus
    coordinateQuadMinus minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.SeitzReduction.OmegaPilot

theorem odd_centralizer_sylow_le_center_orth_plus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2]
    (U : Sylow 2 (StatedProj (StatedOmega (StatedQuadPlus n F))))
    {x : StatedProj (StatedOmega (StatedQuadPlus n F))} (hxodd : Odd (orderOf x))
    (hxc : x ∈ Subgroup.centralizer
      ((U : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n F)))) :
        Set (StatedProj (StatedOmega (StatedQuadPlus n F))))) :
    x ∈ Subgroup.center (StatedProj (StatedOmega (StatedQuadPlus n F))) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hbot : (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf
      (StatedOmega (StatedQuadPlus n F)) = ⊥ :=
    CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadPlus_eq_bot
      (K := F) hn1
  let eΩ : StatedProj (StatedOmega (StatedQuadPlus n F)) ≃*
      StatedOmega (StatedQuadPlus n F) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eD : StatedOmega (StatedQuadPlus n F) ≃*
      matrixDerived (coordinateQuadPlus n F) :=
    statedDerivedPlusEquiv F n
  let eM : matrixDerived (coordinateQuadPlus n F) ≃*
      orthDerived (coordinateQuadPlus n F) :=
    derivedEquiv (coordinateQuadPlus n F)
  let e : StatedProj (StatedOmega (StatedQuadPlus n F)) ≃*
      orthDerived (coordinateQuadPlus n F) := eΩ.trans (eD.trans eM)
  let g : orthDerived (coordinateQuadPlus n F) := e x
  have hgodd : Odd (orderOf g) := by
    show Odd (orderOf (e x))
    rw [MulEquiv.orderOf_eq e x]
    exact hxodd
  let U' : Sylow 2 (orthDerived (coordinateQuadPlus n F)) :=
    U.comapOfInjective e.symm e.symm.injective (fun u _ => ⟨e u, by simp⟩)
  have hgcentral : g ∈ Subgroup.centralizer
      ((U' : Subgroup (orthDerived (coordinateQuadPlus n F))) :
        Set (orthDerived (coordinateQuadPlus n F))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzU : e.symm z ∈ (U : Subgroup _) := hz
    have hcomm : e.symm z * x = x * e.symm z :=
      (Subgroup.mem_centralizer_iff.mp hxc) (e.symm z) hzU
    calc z * g = e (e.symm z) * e x := by rw [e.apply_symm_apply]
      _ = e (e.symm z * x) := by rw [map_mul]
      _ = e (x * e.symm z) := by rw [hcomm]
      _ = e x * e (e.symm z) := by rw [map_mul]
      _ = g * z := by rw [e.apply_symm_apply]
  have hfr := isHypFrame_plus (K := F) n
  let i₁ : Fin n := ⟨0, by omega⟩
  let i₂ : Fin n := ⟨1, by omega⟩
  let i₃ : Fin n := ⟨2, by omega⟩
  let P₁ : HypPair (coordinateQuadPlus n F) := (hfr.hyp i₁).hypPair
  let P₂ : HypPair (coordinateQuadPlus n F) := (hfr.hyp i₂).hypPair
  let P₃ : HypPair (coordinateQuadPlus n F) := (hfr.hyp i₃).hypPair
  have hpd : ∀ i j : Fin n, i ≠ j →
      PairDisjoint (plusFrameLeft n i) (plusFrameRight n i)
        (plusFrameLeft n j) (plusFrameRight n j) := by
    intro i j hij
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hij (Sum.inl_injective ((plusIndexEquiv n).injective h)).symm
    · intro h
      exact Sum.inl_ne_inr ((plusIndexEquiv n).injective h)
    · intro h
      exact Sum.inr_ne_inl ((plusIndexEquiv n).injective h)
    · intro h
      exact hij (Sum.inr_injective ((plusIndexEquiv n).injective h)).symm
  have h₁₂ : P₁.Orth P₂ :=
    (hfr.hyp i₁).orth (hfr.hyp i₂) (hpd i₁ i₂ (by simp [i₁, i₂]))
  have h₁₃ : P₁.Orth P₃ :=
    (hfr.hyp i₁).orth (hfr.hyp i₃) (hpd i₁ i₃ (by simp [i₁, i₃]))
  have h₂₃ : P₂.Orth P₃ :=
    (hfr.hyp i₂).orth (hfr.hyp i₃) (hpd i₂ i₃ (by simp [i₂, i₃]))
  have hQ : (polarBilin (coordinateQuadPlus n F)).Nondegenerate :=
    (regular_coordinateQuadPlus (K := F) n hn3).1
  have hT : ∃ T : Submodule F (Fin (2 * n) → F), Module.finrank F T = 3 ∧
      ∀ x ∈ T, coordinateQuadPlus n F x = 0 :=
    (regular_coordinateQuadPlus (K := F) n hn3).2
  have hEΩ : ∀ u w, eichler (coordinateQuadPlus n F) u w ∈
      orthDerived (coordinateQuadPlus n F) :=
    fun u w => eichler_mem_orthDerived hQ hT u w
  by_cases hg1 : g = 1
  · have hx1 : x = 1 := by
      have h := congrArg e.symm hg1
      simpa [g] using h
    rw [hx1]
    exact Subgroup.one_mem _
  · exfalso
    obtain ⟨y, hyO, c, hc0, hgy⟩ :=
      exists_eq_eichler_of_commute_sylow (Q := coordinateQuadPlus n F) hQ h₁₂ h₁₃ h₂₃ hEΩ
        U' hg1 (fun u hu => (Subgroup.mem_centralizer_iff.mp hgcentral) u hu)
    have hyiso : (y : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)) ∈
        TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n F) :=
      Subgroup.commutator_le_self _ hyO
    have hpol : polar (coordinateQuadPlus n F) (y P₁.e) (c • y P₂.e) = 0 := by
      rw [polar_smul_right_eq, polar_map_of_mem hyiso, h₁₂.ee, mul_zero]
    have hsq : g * g = 1 := by
      apply Subtype.ext
      show (g : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)) *
        (g : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)) = 1
      rw [hgy, eichler_mul hpol hpol,
        show c • (y P₂.e) + c • (y P₂.e) = 0 by
          rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul],
        eichler_zero_right]
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hcop : Nat.Coprime (orderOf g) 2 := Nat.coprime_two_right.mpr hgodd
    exact hg1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd))

theorem odd_centralizer_sylow_le_center_orth_minus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F]
    [Finite F] [CharP F 2] (b c : F) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 (StatedProj (StatedOmega (StatedQuadMinus n F b c))))
    {x : StatedProj (StatedOmega (StatedQuadMinus n F b c))} (hxodd : Odd (orderOf x))
    (hxc : x ∈ Subgroup.centralizer
      ((U : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n F b c)))) :
        Set (StatedProj (StatedOmega (StatedQuadMinus n F b c))))) :
    x ∈ Subgroup.center (StatedProj (StatedOmega (StatedQuadMinus n F b c))) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hv0 : quadMinus n F b c
      (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1) ≠ 0 := by
    rw [quadMinus_apply]
    simp
  have hbot : (StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus n F b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus n F b c) (Q₀ := StatedQuadMinus n F b c)
      (coe_quadMinus n F b c) ⟨_, hv0⟩
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus n F b c)) ≃*
      StatedOmega (StatedQuadMinus n F b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eD : StatedOmega (StatedQuadMinus n F b c) ≃*
      matrixDerived (coordinateQuadMinus n F hn1 b c) :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedDerivedReindexEquiv
      (minusIndexEquiv n hn1) (quadMinus n F b c) (coe_quadMinus n F b c)
  let eM : matrixDerived (coordinateQuadMinus n F hn1 b c) ≃*
      orthDerived (coordinateQuadMinus n F hn1 b c) :=
    derivedEquiv (coordinateQuadMinus n F hn1 b c)
  let e : StatedProj (StatedOmega (StatedQuadMinus n F b c)) ≃*
      orthDerived (coordinateQuadMinus n F hn1 b c) := eΩ.trans (eD.trans eM)
  let g : orthDerived (coordinateQuadMinus n F hn1 b c) := e x
  have hgodd : Odd (orderOf g) := by
    show Odd (orderOf (e x))
    rw [MulEquiv.orderOf_eq e x]
    exact hxodd
  let U' : Sylow 2 (orthDerived (coordinateQuadMinus n F hn1 b c)) :=
    U.comapOfInjective e.symm e.symm.injective (fun u _ => ⟨e u, by simp⟩)
  have hgcentral : g ∈ Subgroup.centralizer
      ((U' : Subgroup (orthDerived (coordinateQuadMinus n F hn1 b c))) :
        Set (orthDerived (coordinateQuadMinus n F hn1 b c))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzU : e.symm z ∈ (U : Subgroup _) := hz
    have hcomm : e.symm z * x = x * e.symm z :=
      (Subgroup.mem_centralizer_iff.mp hxc) (e.symm z) hzU
    calc z * g = e (e.symm z) * e x := by rw [e.apply_symm_apply]
      _ = e (e.symm z * x) := by rw [map_mul]
      _ = e (x * e.symm z) := by rw [hcomm]
      _ = e x * e (e.symm z) := by rw [map_mul]
      _ = g * z := by rw [e.apply_symm_apply]
  have hfr : IsHypFrame (coordinateQuadMinus n F hn1 b c)
      (minusFrameLeft hn1) (minusFrameRight hn1) :=
    isHypFrame_minus (K := F) (n := n) hn1 b c
  let i₁ : Fin (n - 1) := ⟨0, by omega⟩
  let i₂ : Fin (n - 1) := ⟨1, by omega⟩
  let i₃ : Fin (n - 1) := ⟨2, by omega⟩
  let P₁ : HypPair (coordinateQuadMinus n F hn1 b c) := (hfr.hyp i₁).hypPair
  let P₂ : HypPair (coordinateQuadMinus n F hn1 b c) := (hfr.hyp i₂).hypPair
  let P₃ : HypPair (coordinateQuadMinus n F hn1 b c) := (hfr.hyp i₃).hypPair
  have hpd : ∀ i j : Fin (n - 1), i ≠ j →
      PairDisjoint (minusFrameLeft hn1 i) (minusFrameRight hn1 i)
        (minusFrameLeft hn1 j) (minusFrameRight hn1 j) := by
    intro i j hij
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hij (Sum.inl_injective ((minusIndexEquiv n hn1).injective h)).symm
    · intro h
      exact Sum.inl_ne_inr ((minusIndexEquiv n hn1).injective h)
    · intro h
      exact Sum.inr_ne_inl ((minusIndexEquiv n hn1).injective h)
    · intro h
      exact hij (Sum.inl_injective
        (Sum.inr_injective ((minusIndexEquiv n hn1).injective h))).symm
  have h₁₂ : P₁.Orth P₂ :=
    (hfr.hyp i₁).orth (hfr.hyp i₂) (hpd i₁ i₂ (by simp [i₁, i₂]))
  have h₁₃ : P₁.Orth P₃ :=
    (hfr.hyp i₁).orth (hfr.hyp i₃) (hpd i₁ i₃ (by simp [i₁, i₃]))
  have h₂₃ : P₂.Orth P₃ :=
    (hfr.hyp i₂).orth (hfr.hyp i₃) (hpd i₂ i₃ (by simp [i₂, i₃]))
  have hreg := regular_coordinateQuadMinus (n := n) F b c hn hirr
  have hQ : (polarBilin (coordinateQuadMinus n F hn1 b c)).Nondegenerate := hreg.1
  have hT : ∃ T : Submodule F (Fin (2 * n) → F), Module.finrank F T = 3 ∧
      ∀ x ∈ T, coordinateQuadMinus n F hn1 b c x = 0 := hreg.2
  have hEΩ : ∀ u w, eichler (coordinateQuadMinus n F hn1 b c) u w ∈
      orthDerived (coordinateQuadMinus n F hn1 b c) :=
    fun u w => eichler_mem_orthDerived hQ hT u w
  by_cases hg1 : g = 1
  · have hx1 : x = 1 := by
      have h := congrArg e.symm hg1
      simpa [g] using h
    rw [hx1]
    exact Subgroup.one_mem _
  · exfalso
    obtain ⟨y, hyO, d, hd0, hgy⟩ :=
      exists_eq_eichler_of_commute_sylow (Q := coordinateQuadMinus n F hn1 b c) hQ h₁₂ h₁₃ h₂₃ hEΩ
        U' hg1 (fun u hu => (Subgroup.mem_centralizer_iff.mp hgcentral) u hu)
    have hyiso : (y : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)) ∈
        TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadMinus n F hn1 b c) :=
      Subgroup.commutator_le_self _ hyO
    have hpol : polar (coordinateQuadMinus n F hn1 b c) (y P₁.e) (d • y P₂.e) = 0 := by
      rw [polar_smul_right_eq, polar_map_of_mem hyiso, h₁₂.ee, mul_zero]
    have hsq : g * g = 1 := by
      apply Subtype.ext
      show (g : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)) *
        (g : (Fin (2 * n) → F) ≃ₗ[F] (Fin (2 * n) → F)) = 1
      rw [hgy, eichler_mul hpol hpol,
        show d • (y P₂.e) + d • (y P₂.e) = 0 by
          rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul],
        eichler_zero_right]
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hcop : Nat.Coprime (orderOf g) 2 := Nat.coprime_two_right.mpr hgodd
    exact hg1 (orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd))

end CFSG.ClassicalGroups.Orthogonal

end
