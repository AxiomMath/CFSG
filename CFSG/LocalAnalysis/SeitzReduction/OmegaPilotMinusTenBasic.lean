module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotRootCentralizerMinus
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDisplayed

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup omegaGroup_le
  relIndex_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Six

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem omegaGroup_le_orthDerived_of_six (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 6) (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, R u ≠ 0) :
    omegaGroup R hR ≤ orthDerived R := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction R hR hdim hts
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hNΩ : orthDerived R ≤ omegaGroup R hR :=
    CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR
  have hΩO : omegaGroup R hR ≤ TauCeti.QuadraticMap.orthogonalGroup R := omegaGroup_le R hR
  have hmul := Subgroup.relIndex_mul_relIndex (orthDerived R) (omegaGroup R hR)
    (TauCeti.QuadraticMap.orthogonalGroup R) hNΩ hΩO
  rw [relIndex_omegaGroup R hR] at hmul
  have hNO : (orthDerived R).relIndex (TauCeti.QuadraticMap.orthogonalGroup R) = 2 := by
    rw [Subgroup.relIndex]
    have h : orthDerived R = ρ.range := hcomm
    rw [h]
    exact hidx
  have hne : (orthDerived R).relIndex (omegaGroup R hR) ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact Subgroup.relIndex_eq_one.mp (by omega)

theorem isQuasisimple_orthDerived_of_six (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 6) (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, R u ≠ 0) :
    CFSG.IsQuasisimple (orthDerived R) ∧ center (orthDerived R) = ⊥ := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, -, hnonab, -, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction R hR hdim hts
  have e : orthDerived R ≃* ρ.range := MulEquiv.subgroupCongr hcomm
  have := hsimple
  have hq : CFSG.IsQuasisimple ρ.range :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_of_simple_nonabelian hnonab
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_⟩
  have hc : center ρ.range = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ρ.range) with h | h
    · exact h
    · exfalso
      apply hnonab
      intro x y
      exact Subgroup.mem_center_iff.mp (h ▸ mem_top y) x
  have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm
  rw [← hmap, hc, Subgroup.map_bot]

end Six

section StabEquiv

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ι}
  {Q : QuadraticForm K (ι → K)}

theorem IsHypCoord.resHom_mem_orthDerived_of_le [CharP K 2] (h : IsHypCoord Q a b)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hΩ : omegaGroup (Q.comp (perpSub K a b).subtype) hR ≤
      orthDerived (Q.comp (perpSub K a b).subtype))
    (y : stabDerived Q a b) : h.resHom y ∈ orthDerived (Q.comp (perpSub K a b).subtype) := by
  have hev : Even (finrank K (commSpace ((y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)))) :=
    (mem_omegaGroup.mp
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hQ (y : orthDerived Q).2)).2
  apply hΩ
  exact mem_omegaGroup.mpr ⟨h.resHom_mem_orthogonalGroup y, by
    rw [h.finrank_commSpace_resHom]
    exact hev⟩

@[expose] noncomputable def IsHypCoord.stabDerivedEquivOfLe [CharP K 2] (h : IsHypCoord Q a b)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hΩ : omegaGroup (Q.comp (perpSub K a b).subtype) hR ≤
      orthDerived (Q.comp (perpSub K a b).subtype)) :
    stabDerived Q a b ≃* orthDerived (Q.comp (perpSub K a b).subtype) where
  toFun y := ⟨h.resHom y, h.resHom_mem_orthDerived_of_le hQ hR hΩ y⟩
  invFun g := ⟨⟨extendLin h.ne (g : perpSub K a b ≃ₗ[K] perpSub K a b),
      h.extendLin_mem_orthDerived g.2⟩,
    extendLin_mem_stabSub h.ne (g : perpSub K a b ≃ₗ[K] perpSub K a b)⟩
  left_inv y := Subtype.ext (Subtype.ext (h.extendLin_resHom y))
  right_inv g := Subtype.ext (h.resHom_extendLin (g : perpSub K a b ≃ₗ[K] perpSub K a b) _)
  map_mul' y y' := Subtype.ext (map_mul h.resHom y y')

end StabEquiv

section MinusPerp

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem minusPerp_regular_wittIndex {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (m - 1)) :
    (polarBilin ((coordinateQuadMinus m K (by omega) b c).comp
      (perpSub K (minusIndexEquiv m (by omega) (.inl k))
        (minusIndexEquiv m (by omega) (.inr (.inl k)))).subtype)).Nondegenerate ∧
    finrank K (perpSub K (minusIndexEquiv m (by omega) (.inl k))
      (minusIndexEquiv m (by omega) (.inr (.inl k)))) = 2 * (m - 1) ∧
    ∀ T : Submodule K (perpSub K (minusIndexEquiv m (by omega) (.inl k))
        (minusIndexEquiv m (by omega) (.inr (.inl k)))),
      (∀ x ∈ T, (coordinateQuadMinus m K (by omega) b c).comp
        (perpSub K (minusIndexEquiv m (by omega) (.inl k))
          (minusIndexEquiv m (by omega) (.inr (.inl k)))).subtype x = 0) →
      finrank K T ≤ m - 2 := by
  have e := minusPerpIsometry (K := K) hm b c k
  have hnd : (polarBilin (coordinateQuadMinus (m - 1) K (by omega) b c)).Nondegenerate :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry (m - 1) K
        (by omega) b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (m - 1) K hirr)
  refine ⟨nondegenerate_of_isometryEquiv e hnd, ?_, fun T hT => ?_⟩
  · rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
  · have hW := CFSG.Blueprint.EvenSource.le_sourceWittIndex
      (⇑(coordinateQuadMinus (m - 1) K (by omega) b c))
      (W := T.map e.toLinearEquiv.toLinearMap) (by
        rintro _ ⟨x, hx, rfl⟩
        change coordinateQuadMinus (m - 1) K (by omega) b c (e x) = 0
        rw [e.map_app]
        exact hT x hx)
    rw [LinearEquiv.finrank_map_eq,
      CFSG.RankThree.PartOne.KCOrthogonalDescent.sourceWittIndex_coordinateQuadMinus (m - 1) K
        (by omega) b c hirr hnd] at hW
    omega

theorem isQuasisimple_minusStabPairsBar_of_five_le [CharP K 2] (hn : 5 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) :
    CFSG.IsQuasisimple (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j)))) ∧
    center (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j))
      (minusIndexEquiv n (by omega) (.inr (.inl j)))) = ⊥ := by
  rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h6
  swap
  · exact isQuasisimple_minusStabPairsBar h6 hirr hij
  obtain ⟨j', hj'⟩ := exists_avoid_eq (M := 5 - 1 - 1) (by omega : 5 - 1 - 1 + 1 = 5 - 1) hij.symm
  have hk := isHypCoord_coordinateQuadMinus (K := K) (n := 5 - 1) (by omega) b c j'
  obtain ⟨hR, hdim, hW⟩ := minusPerp_regular_wittIndex (K := K) (m := 5 - 1) (by omega) hirr j'
  have hdim6 : finrank K (perpSub K (minusIndexEquiv (5 - 1) (by omega) (.inl j'))
      (minusIndexEquiv (5 - 1) (by omega) (.inr (.inl j')))) = 6 := by
    rw [hdim]
  have hts : ∀ U : Submodule K (perpSub K (minusIndexEquiv (5 - 1) (by omega) (.inl j'))
      (minusIndexEquiv (5 - 1) (by omega) (.inr (.inl j')))), finrank K U = 3 →
      ∃ u ∈ U, (coordinateQuadMinus (5 - 1) K (by omega) b c).comp
        (perpSub K (minusIndexEquiv (5 - 1) (by omega) (.inl j'))
          (minusIndexEquiv (5 - 1) (by omega) (.inr (.inl j')))).subtype u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    have := hW U hcon
    omega
  have hΩ := omegaGroup_le_orthDerived_of_six hR hdim6 hts
  obtain ⟨hqs, hcen⟩ := isQuasisimple_orthDerived_of_six hR hdim6 hts
  have hle : stabPairsBar (coordinateQuadMinus 5 K (by omega) b c)
      (minusIndexEquiv 5 (by omega) (.inl i)) (minusIndexEquiv 5 (by omega) (.inr (.inl i)))
      (minusIndexEquiv 5 (by omega) (.inl j)) (minusIndexEquiv 5 (by omega) (.inr (.inl j))) ≤
      minusPairPerp (by omega) b c i :=
    map_mono fun _ hx => (mem_subgroupOf.mp hx).1
  set φ := (((Subgroup.subgroupOfEquivOfLe hle).symm.trans
    (((stabPairsBar (coordinateQuadMinus 5 K _ b c)
      (minusIndexEquiv 5 _ (.inl i)) (minusIndexEquiv 5 _ (.inr (.inl i)))
      (minusIndexEquiv 5 _ (.inl j))
      (minusIndexEquiv 5 _ (.inr (.inl j)))).subgroupOf
        (minusPairPerp _ b c i)).equivMapOfInjective
      (minusPairPerpEquiv (K := K) (by omega) hirr i).toMonoidHom
      (minusPairPerpEquiv (K := K) (by omega) hirr i).injective)).trans
    (MulEquiv.subgroupCongr (map_minusStabPairsBar (by omega) hirr hj'))).trans
    (hk.stabDerivedEquivOfLe (regular_coordinateQuadMinus (5 - 1) K b c (by omega) hirr).1 hR hΩ)
    with hφ
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hqs, ?_⟩
  have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ.symm
  rw [← hmap, hcen, Subgroup.map_bot]

end MinusPerp

end CFSG.SeitzReduction.OmegaPilot
