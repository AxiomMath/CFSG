module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (commSpace omegaGroup mem_omegaGroup omegaGroup_le
  relIndex_omegaGroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem omegaGroup_le_orthDerived_of_four (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 4) (hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, R u ≠ 0) :
    omegaGroup R hR ≤ orthDerived R := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, -, -, -, -, hidx, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction R hR hdim hts
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

theorem isQuasisimple_orthDerived_of_four (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 4) (hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, R u ≠ 0) :
    CFSG.IsQuasisimple (orthDerived R) ∧ center (orthDerived R) = ⊥ ∧
      Nat.card (orthDerived R) = Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, -, hnonab, hcard, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction R hR hdim hts
  have e : orthDerived R ≃* ρ.range := MulEquiv.subgroupCongr hcomm
  have := hsimple
  have hq : CFSG.IsQuasisimple ρ.range :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_of_simple_nonabelian hnonab
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_, ?_⟩
  · have hc : center ρ.range = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ρ.range) with h | h
      · exact h
      · exfalso
        apply hnonab
        intro x y
        exact Subgroup.mem_center_iff.mp (h ▸ mem_top y) x
    have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm
    rw [← hmap, hc, Subgroup.map_bot]
  · rw [Nat.card_congr e.toEquiv, hcard]

end Four

section PerpEquiv

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem omegaGroup_le_orthDerived_minusPerp (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    omegaGroup ((coordinateQuadMinus n K (by omega) b c).comp
      (perpSub K (minusIndexEquiv n (by omega) (.inl k))
        (minusIndexEquiv n (by omega) (.inr (.inl k)))).subtype)
      (minusPerp_regular_wittIndex (K := K) (m := n) (by omega) hirr k).1 ≤
    orthDerived ((coordinateQuadMinus n K (by omega) b c).comp
      (perpSub K (minusIndexEquiv n (by omega) (.inl k))
        (minusIndexEquiv n (by omega) (.inr (.inl k)))).subtype) := by
  obtain ⟨hR, hdim, hW⟩ := minusPerp_regular_wittIndex (K := K) (m := n) (by omega) hirr k
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · refine omegaGroup_le_orthDerived_of_six hR (by rw [hdim]) fun U hU => ?_
    by_contra hcon
    push Not at hcon
    have := hW U hcon
    omega
  · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR
      (regular_minusPerp h5 hirr k).2

@[expose] noncomputable def IsHypCoord.pairPerpOfEquivOfLe {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {a b : Fin d} (h : IsHypCoord Q a b)
    (hQ : (polarBilin Q).Nondegenerate)
    (hR : (polarBilin (Q.comp (perpSub K a b).subtype)).Nondegenerate)
    (hΩ : omegaGroup (Q.comp (perpSub K a b).subtype) hR ≤
      orthDerived (Q.comp (perpSub K a b).subtype)) :
    pairPerpOf Q a b ≃* orthDerived (Q.comp (perpSub K a b).subtype) :=
  ((stabDerived Q a b).equivMapOfInjective (projHom Q)
    (projHom_injective h.exists_ne_zero)).symm.trans (h.stabDerivedEquivOfLe hQ hR hΩ)

@[expose] noncomputable def minusPairPerpEquivOfLe (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    minusPairPerp (K := K) (by omega) b c k ≃*
      orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c) :=
  ((isHypCoord_coordinateQuadMinus _ b c k).pairPerpOfEquivOfLe
    (regular_coordinateQuadMinus n K b c hn hirr).1
    (minusPerp_regular_wittIndex (K := K) (m := n) (by omega) hirr k).1
    (omegaGroup_le_orthDerived_minusPerp hn hirr k)).trans
    (orthDerivedCongr (minusPerpIsometry (by omega) b c k))

theorem minusPairPerpEquivOfLe_apply (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (x : minusPairPerp (K := K) (by omega) b c i)
    (G : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (minusIndexEquiv n (by omega) (.inl i))
        (minusIndexEquiv n (by omega) (.inr (.inl i))))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G)
    (w : Fin (2 * (n - 1)) → K) (y : Fin (2 * (n - 1))) :
    ((minusPairPerpEquivOfLe hn hirr i x :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) w y =
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Function.extend (minusPerpCoord (by omega) i) w 0) (minusPerpCoord (by omega) i y) := by
  have hsymm : ((stabDerived (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i))
      (minusIndexEquiv n (by omega) (.inr (.inl i)))).equivMapOfInjective
      (projHom _) (projHom_injective
        (isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).exists_ne_zero)).symm x =
      ⟨G, hG⟩ :=
    (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hxG)
  have e1 : minusPairPerpEquivOfLe hn hirr i x =
      orthDerivedCongr (minusPerpIsometry (by omega) b c i)
        ((isHypCoord_coordinateQuadMinus (K := K) (by omega) b c i).stabDerivedEquivOfLe
          (regular_coordinateQuadMinus n K b c hn hirr).1
          (minusPerp_regular_wittIndex (K := K) (m := n) (by omega) hirr i).1
          (omegaGroup_le_orthDerived_minusPerp hn hirr i) ⟨G, hG⟩) := by
    rw [← hsymm]
    rfl
  rw [e1, orthDerivedCongr_apply]
  rfl

end PerpEquiv

end CFSG.SeitzReduction.OmegaPilot
