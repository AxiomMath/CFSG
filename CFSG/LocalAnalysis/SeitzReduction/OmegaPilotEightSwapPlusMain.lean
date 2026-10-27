module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapPlus
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Model

structure PlusFourSwapGenInput (K : Type) [Field K] : Prop where
  le_sup : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
    pairPerp (K := K) a ≤ plusOverlap a b ⊔ plusOverlap a c
  triple : ∀ o k l : Fin 4, o ≠ k → o ≠ l → k ≠ l → ∃ x, x ≠ 1 ∧
    x ∈ plusOverlap (K := K) o k ∧ x ∈ plusOverlap (K := K) o l ∧ x ∈ plusOverlap (K := K) k l
  iSup_eq_top : ⨆ a : Fin 4, pairPerp (K := K) a = ⊤

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem plusFourSwapTriple_of_levi (hlevi : PlusFourLeviInput) (hq : 4 ≤ Nat.card K)
    {o k l : Fin 4} (hok : o ≠ k) (hol : o ≠ l) (hkl : k ≠ l) : ∃ x, x ≠ 1 ∧
      x ∈ plusOverlap (K := K) o k ∧ x ∈ plusOverlap (K := K) o l ∧
        x ∈ plusOverlap (K := K) k l := by
  obtain ⟨j, hjo, hjk, hjl⟩ := exists_ne_ne_ne_fin (by norm_num) o k l
  have hne : pairTorus (K := K) j ≠ ⊥ :=
    ne_bot_of_one_lt_card (by rw [card_pairTorus]; omega)
  obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hmem : ∀ {a b : Fin 4}, a ≠ b → j ≠ a → j ≠ b → x ∈ plusOverlap (K := K) a b := by
    intro a b hab hja hjb
    have hperf := (hlevi K hq a b hab).1
    have hle : stabTwoBar K a b ≤ plusOverlap (K := K) a b :=
      stabPairsBar_le_perfectCore_inf_centralizer (isHypCoord_coordinateQuadPlus b) hperf
    refine hle ?_
    rw [← pairPerp_inf_pairPerp]
    exact ⟨pairTorus_le_pairPerp (Ne.symm hja) hx, pairTorus_le_pairPerp (Ne.symm hjb) hx⟩
  exact ⟨x, hx1', hmem hok hjo hjk, hmem hol hjo hjl, hmem hkl hjk hjl⟩

end Model

@[expose] def PlusFourSwapDichotomyInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ f → 2 ≤ f →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 1) K)) (t : G),
      orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
        (∃ hz : z ∈ L, IsLongRoot _ (e ⟨z, hz⟩)) ∧
        (∃ hz : z ∈ CFSG.conjugate L x,
          IsLongRoot _ (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)) ∧
        ∀ l ∈ CFSG.conjugate L x, t * l * t⁻¹ = z * l * z⁻¹) →
      (∀ k : Fin (3 + 1), OmegaRowAt t (modelToG e (pairTorus (K := K) k))
        (modelToG e (pairPerp (K := K) k)) .swap) →
      ∀ Ψ : ∀ k : Fin (3 + 1), SwapParam t (modelToG e (pairPerp (K := K) k)),
        (∀ k, Function.Injective (Ψ k).Ψ) →
        (∀ k, (Ψ k).Ψ.range = centralizerPerfectCore (modelToG e (pairTorus (K := K) k))) →
        ∀ a b : Fin (3 + 1), a ≠ b →
          AgreeOn (Ψ a) (Ψ b) (perfectCore (modelToG e (pairPerp (K := K) a) ⊓
            centralizer (modelToG e (pairTorus (K := K) b) : Set G))) ∨
          FlipOn (Ψ a) (Ψ b) (perfectCore (modelToG e (pairPerp (K := K) a) ⊓
            centralizer (modelToG e (pairTorus (K := K) b) : Set G)))

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_swapRow_omega_plus_four (hset : SeitzSetting G L) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hrow : ∀ k : Fin 4, OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .swap)
    (hgen : PlusFourSwapGenInput K)
    (hdich : ∀ Ψ : ∀ k : Fin 4, SwapParam t (modelToG e (pairPerp (K := K) k)),
        (∀ k, Function.Injective (Ψ k).Ψ) →
        (∀ k, (Ψ k).Ψ.range = centralizerPerfectCore (modelToG e (pairTorus (K := K) k))) →
        ∀ a b : Fin 4, a ≠ b →
          AgreeOn (Ψ a) (Ψ b) (perfectCore (modelToG e (pairPerp (K := K) a) ⊓
            centralizer (modelToG e (pairTorus (K := K) b) : Set G))) ∨
          FlipOn (Ψ a) (Ψ b) (perfectCore (modelToG e (pairPerp (K := K) a) ⊓
            centralizer (modelToG e (pairTorus (K := K) b) : Set G))))
    (hP : SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 4 K))) : False := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  set X : Fin 4 → Subgroup G := fun k => modelToG e (pairTorus (K := K) k) with hXdef
  set D : Fin 4 → Subgroup G := fun k => modelToG e (pairPerp (K := K) k) with hDdef
  have hdata : ∀ k : Fin 4, X k ≤ L ∧ t ∈ centralizer (X k : Set G) ∧
      D k ≤ centralizer (X k : Set G) ∧ ⁅D k, D k⁆ = D k ∧ center (D k) = ⊥ := by
    intro k
    obtain ⟨hXL, htX, -, -, -, -, hDXt, hDq, hZ, -, -⟩ :=
      neighbour_data_pairTorus_four hKc hq k e htC (X := X k) rfl (D := D k) rfl
    exact ⟨hXL, htX, hDXt.trans inf_le_left, isPerfect_iff.mp hDq.1, hZ⟩
  have hpar : ∀ k : Fin 4, ∃ P : SwapParam t (D k), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (X k) := fun k =>
    exists_swapParam_pairTorus_four_of_row hset hKc hq k e htC ht (hrow k)
  choose Ψ hinj hrange using hpar
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_mulEquiv_plus le_rfl (LinearPilot.one_le_of_card_eq_two_pow hKc) hKc e
  have hO' : ∀ a b, perfectCore (D a ⊓ centralizer (X b : Set G)) =
      modelToG e (plusOverlap (K := K) a b) := fun a b =>
    perfectCore_modelToG_inf_centralizer e _ _
  have hgenL : ⨆ a, D a = L :=
    (UnitaryPilot.modelToG_iSup e _).symm.trans
      (by rw [hgen.iSup_eq_top, UnitaryPilot.modelToG_top])
  exact false_of_swapParam_family_of_dichotomy hset hOut e hP ht hKt Ψ hinj hrange
    (fun k => (hdata k).1) (fun k => (hdata k).2.2.1) (fun k => (hdata k).2.2.2.1)
    (fun k => (hdata k).2.2.2.2) hgenL
    (fun a b hab => UnitaryPilot.modelToG_mono e (pairTorus_le_pairPerp hab))
    (hdich Ψ hinj hrange) (exists_ne_ne_fin (by norm_num))
    (fun a b c hab hac hbc => by
      rw [hO', hO', ← UnitaryPilot.modelToG_sup]
      exact UnitaryPilot.modelToG_mono e (hgen.le_sup a b c hab hac hbc))
    ⟨0, by norm_num⟩
    (fun k l hk hl hkl => by
      rw [hO', hO', hO']
      exact exists_ne_one_mem_modelToG e (hgen.triple _ k l (Ne.symm hk) (Ne.symm hl) hkl))

end Main


theorem omegaPlusFourSwapInput_of_inputs
    (hgen : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K → PlusFourSwapGenInput K)
    (hdich : PlusFourSwapDichotomyInput)
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      SwapPairExclusion (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
    OmegaPlusFourSwapInput := by
  intro G _ _ L hset f K _ _ _ hKc hf e t ht hKt hR5 _ hrow
  have hq : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  exact false_of_swapRow_omega_plus_four hset hKc hq e ht hKt hrow (hgen K hq)
    (hdich G L hset f K hKc hf e t ht hKt hR5 hrow) (hP K hq)

end CFSG.SeitzReduction.OmegaPilot
