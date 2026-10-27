module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoEightBasic
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTen

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (minusIndexEquiv coordinateQuadMinus regular_coordinateQuadMinus)

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem minusPairPerpEquivOfLe_fix_iff (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (i : Fin (n - 1)) (x : minusPairPerp (K := K) (by omega) b c i)
    (G : orthDerived (coordinateQuadMinus n K (by omega) b c))
    (hG : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      stabSub (minusIndexEquiv n (by omega) (.inl i))
        (minusIndexEquiv n (by omega) (.inr (.inl i))))
    (hxG : (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G)
    (c' : Fin (2 * (n - 1))) :
    ((minusPairPerpEquivOfLe hn hirr i x :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) (Pi.single c' 1) =
        Pi.single c' 1 ↔
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
        (Pi.single (minusPerpCoord (by omega) i c') 1) =
        Pi.single (minusPerpCoord (by omega) i c') 1 := by
  have hn2 : 2 ≤ n := by omega
  have hinj := minusPerpCoord_injective hn2 i
  have hext := extend_single (K := K) hinj c'
  have hcomp := single_comp (K := K) hinj c'
  have hi := isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ n) b c i
  have hGO : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadMinus n K (by omega) b c) :=
    Subgroup.commutator_le_self _ G.2
  have hU : (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K))
      (Pi.single (minusPerpCoord hn2 i c') 1) ∈
      perpSub K (minusIndexEquiv n (by omega) (.inl i))
        (minusIndexEquiv n (by omega) (.inr (.inl i))) :=
    hi.apply_mem_perpSub hGO hG (single_mem_perpSub (minusPerpCoord_ne_left hn2 i c')
      (minusPerpCoord_ne_right hn2 i c'))
  constructor
  · intro h
    funext v
    by_cases hva : v = minusIndexEquiv n (by omega) (.inl i)
    · subst hva
      rw [hU.1, Pi.single_eq_of_ne (minusPerpCoord_ne_left hn2 i c').symm]
    by_cases hvb : v = minusIndexEquiv n (by omega) (.inr (.inl i))
    · subst hvb
      rw [hU.2, Pi.single_eq_of_ne (minusPerpCoord_ne_right hn2 i c').symm]
    obtain ⟨y, rfl⟩ := exists_minusPerpCoord_eq hn2 i hva hvb
    have h1 := congrFun h y
    rw [minusPairPerpEquivOfLe_apply hn hirr i x G hG hxG, hext] at h1
    rw [h1, ← hcomp]
  · intro h
    funext y
    rw [minusPairPerpEquivOfLe_apply hn hirr i x G hG hxG, hext, h, ← hcomp]

theorem map_minusStabPairsBarOfLe (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (n - 1)} {j' : Fin (n - 1 - 1)} (hj' : avoid (by omega) i j' = j) :
    ((stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j))
      (minusIndexEquiv n (by omega) (.inr (.inl j)))).subgroupOf
        (minusPairPerp (by omega) b c i)).map (minusPairPerpEquivOfLe hn hirr i).toMonoidHom =
      stabDerived (coordinateQuadMinus (n - 1) K (by omega) b c)
        (minusIndexEquiv (n - 1) (by omega) (.inl j'))
        (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j'))) := by
  have hn2 : 2 ≤ n := by omega
  have hlift : ∀ x : minusPairPerp (K := K) (by omega) b c i,
      ∃ G : orthDerived (coordinateQuadMinus n K (by omega) b c),
      (G : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) ∈
        stabSub (minusIndexEquiv n (by omega) (.inl i))
          (minusIndexEquiv n (by omega) (.inr (.inl i))) ∧
      (x : matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) = projHom _ G := by
    rintro ⟨_, ⟨G, hG, rfl⟩⟩
    exact ⟨G, mem_subgroupOf.mp hG, rfl⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨G, hG, hxG⟩ := mem_map.mp (mem_subgroupOf.mp hx)
    have hG' := mem_subgroupOf.mp hG
    refine mem_subgroupOf.mpr ⟨?_, ?_⟩
    · refine (minusPairPerpEquivOfLe_fix_iff hn hirr i x G hG'.1 hxG.symm _).mpr ?_
      rw [minusPerpCoord_inl hn2 hj']
      exact hG'.2.1
    · refine (minusPairPerpEquivOfLe_fix_iff hn hirr i x G hG'.1 hxG.symm _).mpr ?_
      rw [minusPerpCoord_inr hn2 hj']
      exact hG'.2.2
  · intro hz
    refine ⟨(minusPairPerpEquivOfLe hn hirr i).symm z, ?_, by simp⟩
    obtain ⟨G, hG, hxG⟩ := hlift ((minusPairPerpEquivOfLe hn hirr i).symm z)
    have hz' : ((minusPairPerpEquivOfLe hn hirr i ((minusPairPerpEquivOfLe hn hirr i).symm z) :
        orthDerived (coordinateQuadMinus (n - 1) K (by omega) b c)) :
        (Fin (2 * (n - 1)) → K) ≃ₗ[K] (Fin (2 * (n - 1)) → K)) ∈
        stabSub (minusIndexEquiv (n - 1) (by omega) (.inl j'))
          (minusIndexEquiv (n - 1) (by omega) (.inr (.inl j'))) := by
      rw [MulEquiv.apply_symm_apply]
      exact mem_subgroupOf.mp hz
    have h1 := (minusPairPerpEquivOfLe_fix_iff hn hirr i _ G hG hxG _).mp hz'.1
    have h2 := (minusPairPerpEquivOfLe_fix_iff hn hirr i _ G hG hxG _).mp hz'.2
    rw [minusPerpCoord_inl hn2 hj'] at h1
    rw [minusPerpCoord_inr hn2 hj'] at h2
    refine mem_subgroupOf.mpr ?_
    rw [hxG]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr ⟨hG, h1, h2⟩)

omit [CharP K 2] in
theorem regular_wittIndex_coordinateQuadMinus {m : ℕ} (hm : 1 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin (coordinateQuadMinus m K hm b c)).Nondegenerate ∧
      ∀ T : Submodule K (Fin (2 * m) → K), (∀ x ∈ T, coordinateQuadMinus m K hm b c x = 0) →
        finrank K T ≤ m - 1 := by
  have hnd : (polarBilin (coordinateQuadMinus m K hm b c)).Nondegenerate :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinateMinusIsometry m K
        hm b c)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
  refine ⟨hnd, fun T hT => ?_⟩
  have hW := CFSG.Blueprint.EvenSource.le_sourceWittIndex
    (⇑(coordinateQuadMinus m K hm b c)) (W := T) hT
  rwa [CFSG.RankThree.PartOne.KCOrthogonalDescent.sourceWittIndex_coordinateQuadMinus m K hm b c
    hirr hnd] at hW

theorem isQuasisimple_minusPairPerp_of_four_le (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (n - 1)) :
    CFSG.IsQuasisimple (minusPairPerp (K := K) (by omega : 1 ≤ n) b c k) := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · obtain ⟨hR, hW⟩ := regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) (by omega) hirr
    have hts : ∀ U : Submodule K (Fin (2 * (4 - 1)) → K), finrank K U = 3 →
        ∃ u ∈ U, coordinateQuadMinus (4 - 1) K (by omega) b c u ≠ 0 := by
      intro U hU
      by_contra hcon
      push Not at hcon
      have := hW U hcon
      omega
    obtain ⟨hq, -⟩ := isQuasisimple_orthDerived_of_six hR (by rw [Module.finrank_fin_fun]) hts
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (minusPairPerpEquivOfLe le_rfl hirr k).symm hq
  · exact isQuasisimple_minusPairPerp h5 hirr k

theorem minusStabPairsBar_four {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {i j : Fin (4 - 1)} (hij : i ≠ j) :
    CFSG.IsQuasisimple (stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
      (minusIndexEquiv 4 (by omega) (.inl i)) (minusIndexEquiv 4 (by omega) (.inr (.inl i)))
      (minusIndexEquiv 4 (by omega) (.inl j)) (minusIndexEquiv 4 (by omega) (.inr (.inl j)))) ∧
    center (stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
      (minusIndexEquiv 4 (by omega) (.inl i)) (minusIndexEquiv 4 (by omega) (.inr (.inl i)))
      (minusIndexEquiv 4 (by omega) (.inl j))
      (minusIndexEquiv 4 (by omega) (.inr (.inl j)))) = ⊥ ∧
    Nat.card (stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
      (minusIndexEquiv 4 (by omega) (.inl i)) (minusIndexEquiv 4 (by omega) (.inr (.inl i)))
      (minusIndexEquiv 4 (by omega) (.inl j)) (minusIndexEquiv 4 (by omega) (.inr (.inl j)))) =
      Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := by
  obtain ⟨j', hj'⟩ := exists_avoid_eq (M := 4 - 1 - 1) (by omega : 4 - 1 - 1 + 1 = 4 - 1) hij.symm
  have hk := isHypCoord_coordinateQuadMinus (K := K) (n := 4 - 1) (by omega) b c j'
  obtain ⟨hR, hdim, hW⟩ := minusPerp_regular_wittIndex (K := K) (m := 4 - 1) (by omega) hirr j'
  have hdim4 : finrank K (perpSub K (minusIndexEquiv (4 - 1) (by omega) (.inl j'))
      (minusIndexEquiv (4 - 1) (by omega) (.inr (.inl j')))) = 4 := by
    rw [hdim]
  have hts : ∀ U : Submodule K (perpSub K (minusIndexEquiv (4 - 1) (by omega) (.inl j'))
      (minusIndexEquiv (4 - 1) (by omega) (.inr (.inl j')))), finrank K U = 2 →
      ∃ u ∈ U, (coordinateQuadMinus (4 - 1) K (by omega) b c).comp
        (perpSub K (minusIndexEquiv (4 - 1) (by omega) (.inl j'))
          (minusIndexEquiv (4 - 1) (by omega) (.inr (.inl j')))).subtype u ≠ 0 := by
    intro U hU
    by_contra hcon
    push Not at hcon
    have := hW U hcon
    omega
  have hΩ := omegaGroup_le_orthDerived_of_four hR hdim4 hts
  obtain ⟨hqs, hcen, hcard⟩ := isQuasisimple_orthDerived_of_four hR hdim4 hts
  have hle : stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
      (minusIndexEquiv 4 (by omega) (.inl i)) (minusIndexEquiv 4 (by omega) (.inr (.inl i)))
      (minusIndexEquiv 4 (by omega) (.inl j)) (minusIndexEquiv 4 (by omega) (.inr (.inl j))) ≤
      minusPairPerp (by omega) b c i :=
    map_mono fun _ hx => (mem_subgroupOf.mp hx).1
  set φ := (((Subgroup.subgroupOfEquivOfLe hle).symm.trans
    (((stabPairsBar (coordinateQuadMinus 4 K _ b c)
      (minusIndexEquiv 4 _ (.inl i)) (minusIndexEquiv 4 _ (.inr (.inl i)))
      (minusIndexEquiv 4 _ (.inl j))
      (minusIndexEquiv 4 _ (.inr (.inl j)))).subgroupOf
        (minusPairPerp _ b c i)).equivMapOfInjective
      (minusPairPerpEquivOfLe (K := K) (by omega) hirr i).toMonoidHom
      (minusPairPerpEquivOfLe (K := K) (by omega) hirr i).injective)).trans
    (MulEquiv.subgroupCongr (map_minusStabPairsBarOfLe (by omega) hirr hj'))).trans
    (hk.stabDerivedEquivOfLe
      (regular_wittIndex_coordinateQuadMinus (K := K) (m := 4 - 1) (by omega) hirr).1 hR hΩ)
    with hφ
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hqs, ?_, ?_⟩
  · have hmap := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv φ.symm
    rw [← hmap, hcen, Subgroup.map_bot]
  · rw [Nat.card_congr φ.toEquiv, hcard]

theorem isQuasisimple_minusStabPairsBar_of_four_le (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) :
    CFSG.IsQuasisimple (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j)))) ∧
    center (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j))
      (minusIndexEquiv n (by omega) (.inr (.inl j)))) = ⊥ := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · exact ⟨(minusStabPairsBar_four hirr hij).1, (minusStabPairsBar_four hirr hij).2.1⟩
  · exact isQuasisimple_minusStabPairsBar_of_five_le h5 hirr hij

theorem card_le_minusStabPairsBar_of_four_le (hn : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {i j : Fin (n - 1)} (hij : i ≠ j) :
    Nat.card K ^ 4 ≤ Nat.card (stabPairsBar (coordinateQuadMinus n K (by omega) b c)
      (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
      (minusIndexEquiv n (by omega) (.inl j)) (minusIndexEquiv n (by omega) (.inr (.inl j)))) := by
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · rw [(minusStabPairsBar_four hirr hij).2.2]
    have hq : 2 ≤ Nat.card K := Finite.one_lt_card
    have h1 : Nat.card K ^ 2 ≤ Nat.card K ^ 4 - 1 := by
      have : Nat.card K ^ 2 * 2 ≤ Nat.card K ^ 2 * Nat.card K ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith)
      have h4 : Nat.card K ^ 4 = Nat.card K ^ 2 * Nat.card K ^ 2 := by ring
      have : 4 ≤ Nat.card K ^ 2 := by nlinarith
      omega
    calc Nat.card K ^ 4 = Nat.card K ^ 2 * Nat.card K ^ 2 := by ring
      _ ≤ Nat.card K ^ 2 * (Nat.card K ^ 4 - 1) := Nat.mul_le_mul_left _ h1
  · obtain ⟨k, hik, hjk, -⟩ := exists_ne_three_fin (by omega : 4 ≤ n - 1) i j i
    exact card_le_minusStabPairsBar h5 hirr hik hjk

end Minus

end CFSG.SeitzReduction.OmegaPilot
