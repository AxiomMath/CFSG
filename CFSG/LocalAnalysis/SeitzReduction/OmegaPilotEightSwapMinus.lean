module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapCase
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommSwapParam
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Param

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_minusPairTorus_four_of_row (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (4 - 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hrow : OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by omega) b c k))
      (modelToG e (minusPairPerp (K := K) (by omega) b c k)) .swap) :
    ∃ P : SwapParam t (modelToG e (minusPairPerp (K := K) (by omega) b c k)),
      Function.Injective P.Ψ ∧
        P.Ψ.range = centralizerPerfectCore (modelToG e (minusPairTorus (K := K) (by omega) b c k)) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -⟩ := neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC
    (X := modelToG e (minusPairTorus (K := K) (by omega) b c k)) rfl
    (D := modelToG e (minusPairPerp (K := K) (by omega) b c k)) rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting_of_four_le hset hKc
    hq le_rfl hirr k e htC ht rfl htX rfl
  exact exists_swapParam_minusPairTorus_four hset hKc hq hirr k e htC ht rfl htX rfl
    (swapCase_of_omegaRowAt ht htX hcomp hsyl hrow 0 0)

end Param

section Overlap

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem minusOverlap_eq_stabPairsBar_four (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (4 - 1)} (h : a ≠ a') :
    minusOverlap (K := K) (n := 4) (by omega) b c a a' =
      stabPairsBar (coordinateQuadMinus 4 K (by omega) b c)
        (minusIndexEquiv 4 (by omega) (.inl a)) (minusIndexEquiv 4 (by omega) (.inr (.inl a)))
        (minusIndexEquiv 4 (by omega) (.inl a')) (minusIndexEquiv 4 (by omega) (.inr (.inl a'))) :=
  perfectCore_pairPerpOf_inf_centralizer_pairTorusOf hq
    (isHypCoord_coordinateQuadMinus _ b c a) (isHypCoord_coordinateQuadMinus _ b c a')
    (isPerfect_iff.mp (isQuasisimple_minusStabPairsBar_of_four_le (K := K) le_rfl hirr h).1.1)

theorem isSimpleGroup_minusOverlap_four (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (4 - 1)} (h : a ≠ a') :
    IsSimpleGroup (minusOverlap (K := K) (n := 4) (by omega) b c a a') := by
  rw [minusOverlap_eq_stabPairsBar_four hq hirr h]
  obtain ⟨hqs, hZ⟩ := isQuasisimple_minusStabPairsBar_of_four_le (K := K) le_rfl hirr h
  exact isSimpleGroup_of_isQuasisimple_of_center_eq_bot hqs hZ

theorem center_minusOverlap_eq_bot_four (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a a' : Fin (4 - 1)} (h : a ≠ a') :
    center (minusOverlap (K := K) (n := 4) (by omega) b c a a') = ⊥ := by
  rw [minusOverlap_eq_stabPairsBar_four hq hirr h]
  exact (isQuasisimple_minusStabPairsBar_of_four_le (K := K) le_rfl hirr h).2

theorem anisoTorus_le_stabPairsBar {n : ℕ} (hn : 1 ≤ n) (b c : K) (a a' : Fin (n - 1)) :
    anisoTorus (K := K) hn b c ≤
      stabPairsBar (coordinateQuadMinus n K hn b c)
        (minusIndexEquiv n hn (.inl a)) (minusIndexEquiv n hn (.inr (.inl a)))
        (minusIndexEquiv n hn (.inl a')) (minusIndexEquiv n hn (.inr (.inl a'))) := by
  have hd : ∀ k : Fin (n - 1), PairDisjoint (minusIndexEquiv n hn (.inl k))
      (minusIndexEquiv n hn (.inr (.inl k))) (anisoCoordLeft hn) (anisoCoordRight hn) := by
    intro k
    have P := pairDisjoint_aniso hn k
    exact ⟨P.left_ne_left.symm, P.right_ne_left.symm, P.left_ne_right.symm,
      P.right_ne_right.symm⟩
  exact anisoTorusOf_le_stabPairsBar (anisoCoord_ne hn) (hd a) (hd a')

theorem exists_ne_one_mem_minusOverlap_triple_four (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {o k l : Fin (4 - 1)} (hok : o ≠ k) (hol : o ≠ l)
    (hkl : k ≠ l) :
    ∃ x : matrixProjectiveDerived (coordinateQuadMinus 4 K (by omega) b c), x ≠ 1 ∧
      x ∈ minusOverlap (K := K) (n := 4) (by omega) b c o k ∧
        x ∈ minusOverlap (K := K) (n := 4) (by omega) b c o l ∧
          x ∈ minusOverlap (K := K) (n := 4) (by omega) b c k l := by
  have hne : anisoTorus (K := K) (n := 4) (by omega) b c ≠ ⊥ :=
    ne_bot_of_one_lt_card (by rw [card_anisoTorus le_rfl hirr]; omega)
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hmem : ∀ {a a' : Fin (4 - 1)}, a ≠ a' →
      x ∈ minusOverlap (K := K) (n := 4) (Nat.succ_le_succ (Nat.zero_le _)) b c a a' :=
    fun h => by
    rw [minusOverlap_eq_stabPairsBar_four hq hirr h]
    exact anisoTorus_le_stabPairsBar _ b c _ _ hx
  exact ⟨x, hx1', hmem hok, hmem hol, hmem hkl⟩

@[expose] def MinusFourSwapGenInput (K : Type) [Field K] (b c : K) : Prop :=
  ∀ a a' a'' : Fin (4 - 1), a ≠ a' → a ≠ a'' → a' ≠ a'' →
    minusPairPerp (K := K) (n := 4) (by omega) b c a ≤
      minusOverlap (n := 4) (by omega) b c a a' ⊔ minusOverlap (n := 4) (by omega) b c a a''

end Overlap

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_swapRow_omega_minus_four_of_gen (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hrow : ∀ k : Fin (4 - 1),
      OmegaRowAt t (modelToG e (minusPairTorus (K := K) (by norm_num) b c k))
        (modelToG e (minusPairPerp (K := K) (by norm_num) b c k)) .swap)
    (hgen : MinusFourSwapGenInput K b c)
    (hP : SwapPairExclusion
      (matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c))) : False := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set X : Fin (4 - 1) → Subgroup G :=
    fun k => modelToG e (minusPairTorus (K := K) (by norm_num) b c k) with hXdef
  set D : Fin (4 - 1) → Subgroup G :=
    fun k => modelToG e (minusPairPerp (K := K) (by norm_num) b c k) with hDdef
  have hdata : ∀ k : Fin (4 - 1), X k ≤ L ∧ t ∈ centralizer (X k : Set G) ∧
      D k ≤ centralizer (X k : Set G) ∧ ⁅D k, D k⁆ = D k ∧ center (D k) = ⊥ := by
    intro k
    obtain ⟨hXL, htX, -, -, -, -, hDXt, hDq, hZ, -⟩ :=
      neighbour_data_minusPairTorus_of_four_le hKc hq le_rfl hirr k e htC (X := X k) rfl
        (D := D k) rfl
    exact ⟨hXL, htX, hDXt.trans inf_le_left, isPerfect_iff.mp hDq.1, hZ⟩
  have hpar : ∀ k : Fin (4 - 1), ∃ P : SwapParam t (D k), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (X k) := fun k =>
    exists_swapParam_minusPairTorus_four_of_row hset hKc hq hirr k e htC ht (hrow k)
  choose Ψ hinj hrange using hpar
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_minus le_rfl (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc
      hirr e
  have hO' : ∀ a a', perfectCore (D a ⊓ centralizer (X a' : Set G)) =
      modelToG e (minusOverlap (K := K) (n := 4) (by norm_num) b c a a') := fun a a' =>
    perfectCore_modelToG_inf_centralizer e _ _
  have hgenL : ⨆ a, D a = L :=
    (UnitaryPilot.modelToG_iSup e _).symm.trans
      (by rw [iSup_minusPairPerp_eq_top le_rfl _ hirr, UnitaryPilot.modelToG_top])
  exact false_of_swapParam_family hset hOut e hP ht hKt Ψ hinj hrange (fun k => (hdata k).1)
    (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2.1) (fun k => (hdata k).2.2.2.2) hgenL
    (fun a a' h => UnitaryPilot.modelToG_mono e (minusPairTorus_le_minusPairPerp _ b c h))
    (fun a a' h => by
      rw [hO']
      exact isSimpleGroup_modelToG e (isSimpleGroup_minusOverlap_four hq hirr h))
    (fun a a' h => by
      rw [hO']
      exact center_modelToG_eq_bot e (center_minusOverlap_eq_bot_four hq hirr h))
    (exists_ne_ne_fin (by norm_num))
    (fun a a' a'' h1 h2 h3 => by
      rw [hO', hO', ← UnitaryPilot.modelToG_sup]
      exact UnitaryPilot.modelToG_mono e (hgen a a' a'' h1 h2 h3))
    ⟨0, by norm_num⟩
    (fun k l hk hl hkl => by
      rw [hO', hO', hO']
      exact exists_ne_one_mem_modelToG e
        (exists_ne_one_mem_minusOverlap_triple_four hq hirr (Ne.symm hk) (Ne.symm hl) hkl))

end Main

end CFSG.SeitzReduction.OmegaPilot
