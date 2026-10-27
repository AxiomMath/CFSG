module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightSwapCase
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusFourHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapFamily
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSwapParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Open
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore OddSchurTrivial)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn SwapPairExclusion)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Param

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_swapParam_pairTorus_four_of_row (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) (k : Fin 4)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hrow : OmegaRowAt t (modelToG e (pairTorus (K := K) k)) (modelToG e (pairPerp (K := K) k))
      .swap) :
    ∃ P : SwapParam t (modelToG e (pairPerp (K := K) k)), Function.Injective P.Ψ ∧
      P.Ψ.range = centralizerPerfectCore (modelToG e (pairTorus (K := K) k)) := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -, -, -, hD, hDXt, hDq, hZD, ⟨φ⟩, hOutD⟩ := neighbour_data_pairTorus_four hKc hq k
    e htC (X := modelToG e (pairTorus (K := K) k)) rfl (D := modelToG e (pairPerp (K := K) k)) rfl
  obtain ⟨hcomp, hsyl, -⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting_four hset hKc hq k e htC ht rfl htX rfl
  have hKt := inf_centralizer_eq_zpowers_plus hset (by norm_num) hKc e htC ht
  have hLt : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht
  have hXo := mem_of_odd_of_commute_pairTorus_four htC ht hLt hKt (by omega) k e
    (X := modelToG e (pairTorus (K := K) k)) rfl (D := modelToG e (pairPerp (K := K) k)) rfl
  have hDL : modelToG e (pairPerp (K := K) k) ≤ L := UnitaryPilot.modelToG_le e _
  have hSchur : OddSchurTrivial (modelToG e (pairPerp (K := K) k)) :=
    (SeitzQ2.oddSchurTrivial_specialLinearGroup 3 K).of_mulEquiv φ.symm
  exact exists_swapParam_of_swapCase htC ht hLt htX hD hDq hXo (hDXt.trans inf_le_left) hDL hZD
    hOutD hSchur hsyl (swapCase_of_omegaRowAt ht htX hcomp hsyl hrow 0 0)

end Param

section Family

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_swapParam_family_of_dichotomy (hset : SeitzSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {P : Type} [Group P] [Finite P] (e : L ≃* P)
    (hP : SwapPairExclusion P) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {ι : Type*} {X D : ι → Subgroup G} (Ψ : ∀ a, SwapParam t (D a))
    (hinj : ∀ a, Function.Injective (Ψ a).Ψ)
    (hrange : ∀ a, (Ψ a).Ψ.range = centralizerPerfectCore (X a))
    (hXL : ∀ a, X a ≤ L) (hDX : ∀ a, D a ≤ centralizer (X a : Set G))
    (hDperf : ∀ a, ⁅D a, D a⁆ = D a) (hZD : ∀ a, center (D a) = ⊥) (hgen : ⨆ a, D a = L)
    (hXD : ∀ a b, a ≠ b → X b ≤ D a)
    (hdich : ∀ a b, a ≠ b →
      AgreeOn (Ψ a) (Ψ b) (perfectCore (D a ⊓ centralizer (X b : Set G))) ∨
        FlipOn (Ψ a) (Ψ b) (perfectCore (D a ⊓ centralizer (X b : Set G))))
    (h3 : ∀ a b : ι, ∃ c, c ≠ a ∧ c ≠ b)
    (hgen2 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      D a ≤ perfectCore (D a ⊓ centralizer (X b : Set G)) ⊔
        perfectCore (D a ⊓ centralizer (X c : Set G)))
    (o : ι)
    (hdet : ∀ k l, k ≠ o → l ≠ o → k ≠ l → ∃ x : G, x ≠ 1 ∧
      x ∈ perfectCore (D o ⊓ centralizer (X k : Set G)) ∧
      x ∈ perfectCore (D o ⊓ centralizer (X l : Set G)) ∧
      x ∈ perfectCore (D k ⊓ centralizer (X l : Set G))) : False := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hL := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  set O : ι → ι → Subgroup G := fun a b => perfectCore (D a ⊓ centralizer (X b : Set G)) with hOdef
  have hOD : ∀ a b, O a b ≤ D a := fun a b => (perfectCore_le _).trans inf_le_left
  have hO : ∀ a b, O b a = O a b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · change perfectCore (D b ⊓ centralizer (X a : Set G)) =
        perfectCore (D a ⊓ centralizer (X b : Set G))
      rw [(Ψ b).perfectCore_inf_centralizer_eq (hinj b) (hrange b) (hXD b a (Ne.symm hab)),
        (Ψ a).perfectCore_inf_centralizer_eq (hinj a) (hrange a) (hXD a b hab), sup_comm]
  obtain ⟨σ, hσ⟩ := exists_coherent_star ht2 Ψ O hO hdich o
    (fun k l hk hl hkl => by
      obtain ⟨x, hx1, hok, hol, hkl'⟩ := hdet k l hk hl hkl
      refine ⟨x, hok, hol, hkl', hOD k l hkl', fun hxZ => hx1 ?_⟩
      rw [hZD k, mem_bot] at hxZ
      exact congrArg Subtype.val hxZ)
  set Ψ' : ∀ a, SwapParam t (D a) := fun a => (Ψ a).twist (σ a) with hΨ'
  have hrange' : ∀ a, (Ψ' a).Ψ.range = centralizerPerfectCore (X a) := fun a =>
    (range_twist_Ψ (σ a) (Ψ a)).trans (hrange a)
  obtain ⟨hq, h₁₂, hδ, hsurj, hrng⟩ := swapFactors_of_coherent Ψ' hL O hO
    (fun a b _ => hOD a b) hσ h3 hgen2 hDperf hgen
  exact SeitzQ2.false_of_swapFactors_of_neighbours hset hOut htC ht hq h₁₂ hδ hsurj X D hXL hDX
    hDperf hgen (fun a => (hrange' a) ▸ hrng a)
    (SeitzQ2.nonSwap_of_factorNormal hset ht hKt
      (SeitzQ2.factorNormal_of_swapPairExclusion hset hOut e hP ht hKt) hq h₁₂ hδ hsurj)

end Family

end CFSG.SeitzReduction.OmegaPilot
