module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommGen
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommFour

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal Matrix
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam)
open CFSG.SeitzReduction.LinearPilot (upperUnit)
open scoped MatrixGroups

section RootElt

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem minusRootElt_mul_ne (hn : 4 ≤ n) {β γ : K} (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    {i j : Fin (n - 1)} (hij : i ≠ j) :
    minusRootElt hn hirr i j 1 * minusRootElt hn hirr j i 1 ≠
      minusRootElt hn hirr j i 1 * minusRootElt hn hirr i j 1 := by
  have hn1 : 1 ≤ n := by omega
  have hfr := isHypFrame_minus K hn1 β γ
  intro h
  rw [minusRootElt, minusRootElt, ← map_mul, ← map_mul] at h
  have h2 := congrArg Subtype.val
    (projHom_injective (isHypCoord_coordinateQuadMinus hn1 β γ i).exists_ne_zero h)
  have h3 := LinearEquiv.congr_fun h2 (Pi.single (minusFrameLeft hn1 i) 1)
  have hai : ∀ x : Fin (n - 1), (Pi.single (minusFrameLeft hn1 i) (1 : K) : Fin (2 * n) → K)
      (minusFrameRight hn1 x) = 0 := fun x =>
    Pi.single_eq_of_ne (hfr.left_ne_right i x).symm _
  have haj : (Pi.single (minusFrameLeft hn1 i) (1 : K) : Fin (2 * n) → K)
      (minusFrameLeft hn1 j) = 0 :=
    Pi.single_eq_of_ne (fun e => hij (hfr.left_injective e).symm) _
  have hai' : (Pi.single (minusFrameLeft hn1 i) (1 : K) : Fin (2 * n) → K)
      (minusFrameLeft hn1 i) = 1 := Pi.single_eq_same _ _
  have hji : (Pi.single (minusFrameLeft hn1 j) (1 : K) : Fin (2 * n) → K)
      (minusFrameLeft hn1 i) = 0 :=
    Pi.single_eq_of_ne (fun e => hij (hfr.left_injective e)) _
  have hjj : (Pi.single (minusFrameLeft hn1 j) (1 : K) : Fin (2 * n) → K)
      (minusFrameLeft hn1 j) = 1 := Pi.single_eq_same _ _
  have hbj : ∀ x : Fin (n - 1), (Pi.single (minusFrameLeft hn1 j) (1 : K) : Fin (2 * n) → K)
      (minusFrameRight hn1 x) = 0 := fun x =>
    Pi.single_eq_of_ne (hfr.left_ne_right j x).symm _
  have e1 : frameRootElt (coordinateQuadMinus n K hn1 β γ) (minusFrameLeft hn1)
      (minusFrameRight hn1) j i 1 (Pi.single (minusFrameLeft hn1 i) 1) =
      Pi.single (minusFrameLeft hn1 i) 1 - Pi.single (minusFrameLeft hn1 j) 1 := by
    rw [hfr.frameRootElt_apply hij.symm, hai, hai']
    simp
  have e2 : frameRootElt (coordinateQuadMinus n K hn1 β γ) (minusFrameLeft hn1)
      (minusFrameRight hn1) i j 1 (Pi.single (minusFrameLeft hn1 i) 1) =
      Pi.single (minusFrameLeft hn1 i) 1 := by
    rw [hfr.frameRootElt_apply hij, hai, haj]
    simp
  have e3 : frameRootElt (coordinateQuadMinus n K hn1 β γ) (minusFrameLeft hn1)
      (minusFrameRight hn1) i j 1
      (Pi.single (minusFrameLeft hn1 i) 1 - Pi.single (minusFrameLeft hn1 j) 1) =
      Pi.single (minusFrameLeft hn1 i) 1 - Pi.single (minusFrameLeft hn1 j) 1 +
        Pi.single (minusFrameLeft hn1 i) 1 := by
    rw [hfr.frameRootElt_apply hij]
    simp only [Pi.sub_apply, hai, hbj, haj, hjj, sub_zero, zero_sub, mul_zero, zero_smul,
      add_zero, mul_neg, mul_one, neg_smul, one_smul, sub_neg_eq_add]
  change frameRootElt _ _ _ i j 1 (frameRootElt _ _ _ j i 1 (Pi.single (minusFrameLeft hn1 i) 1)) =
    frameRootElt _ _ _ j i 1 (frameRootElt _ _ _ i j 1 (Pi.single (minusFrameLeft hn1 i) 1)) at h3
  rw [e1, e3, e2, e1] at h3
  have h4 := congrFun h3 (minusFrameLeft hn1 i)
  simp only [Pi.sub_apply, Pi.add_apply, hai', hji, sub_zero] at h4
  have h22 : (1 : K) + 1 = 0 := by
    rw [← two_mul, mul_one]
    exact CharTwo.two_eq_zero
  rw [h22] at h4
  exact one_ne_zero h4.symm

end RootElt

section StepA

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {n : ℕ}

structure MinusRootFieldParam (hn : 4 ≤ n) {β γ : K} (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)) (t : G)
    {F : Type} [Field F] (ι : K →+* F) (σ : F ≃+* F) (i j : Fin (n - 1)) where
  φ : SL(2, F) →* G
  range_eq : φ.range = minusLevelCore e ({i, j} : Finset (Fin (n - 1)))
  N1 : ∀ A : SL(2, K), φ (SpecialLinearGroup.map ι A) ∈
    modelToG e (frameLeviProj (coordinateQuadMinus n K (by omega) β γ) (minusFrameLeft (by omega))
      (minusFrameRight (by omega)) i j)
  upper : φ (upperUnit 1) = (e.symm (minusRootElt hn hirr i j 1) : G)
  N3 : ∀ A : SL(2, F), t * φ A * t⁻¹ = φ (SpecialLinearGroup.map σ.toRingHom A)

omit [Finite G] [Finite K] [CharP K 2] in
theorem modelToG_frameLeviProj_le_centralizer (hn : 1 ≤ n) {β γ : K}
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K hn β γ)) {i j : Fin (n - 1)}
    (hij : i ≠ j) :
    modelToG e (frameLeviProj (coordinateQuadMinus n K hn β γ) (minusFrameLeft hn)
        (minusFrameRight hn) i j) ≤
      centralizer (modelToG e (stabPairsBar (coordinateQuadMinus n K hn β γ)
        (minusIndexEquiv n hn (.inl i)) (minusIndexEquiv n hn (.inr (.inl i)))
        (minusIndexEquiv n hn (.inl j)) (minusIndexEquiv n hn (.inr (.inl j)))) : Set G) := by
  have h := (isHypFrame_minus K hn β γ).frameLeviProj_le_centralizer_stabPairsBar hij
  rw [stabPairsBar_swap_right] at h
  exact UnitaryPilot.modelToG_le_centralizer e h

theorem forall_le_centralizer_minusPlanes (hset : SeitzSetting G L) {f : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {i j : Fin (n - 1)} (hij : i ≠ j) :
    ∀ S : Subgroup G, ⁅S, S⁆ = S → (∀ N : Subgroup S, N.Normal → N = ⊥ ∨ N = ⊤) →
      S ≤ centralizer ({t * (e.symm (minusRootElt hn hirr i j 1) : G)} : Set G) →
      S ≤ centralizer (modelToG e (minusLevelTorus (by omega) β γ
        ({i, j} : Finset (Fin (n - 1)))) : Set G) →
      (e.symm (minusRootElt hn hirr i j 1) : G) ∈ S →
      S ≤ centralizer (modelToG e (stabPairsBar (coordinateQuadMinus n K (by omega) β γ)
        (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
        (minusIndexEquiv n (by omega) (.inl j))
        (minusIndexEquiv n (by omega) (.inr (.inl j)))) : Set G) := by
  obtain ⟨l, hl⟩ := exists_units_ne_one (K := K) (by omega : 3 ≤ Nat.card K)
  obtain ⟨g, hg, hS⟩ := exists_conj_eq_mul_forall_le_centralizer_minusPlanes hset hn hK hq hirr e
    ht hKt hij hl
  intro S hSp hSs hSt hST hzS
  refine hS S hSp hSs (by rw [hg]; exact hSt) (hST.trans (centralizer_le ?_)) hzS
  rw [Set.singleton_subset_iff]
  exact UnitaryPilot.symm_mem_modelToG e (orthTorusElt_mem_minusLevelTorus (by omega) hij l)

theorem minusLevelCore_le_centralizer_field (hset : SeitzSetting G L) {f : ℕ} (hn : 4 ≤ n)
    (hK : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K) {β γ : K}
    (hirr : ∀ s : K, s ^ 2 + β * s + γ ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) β γ)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {i j : Fin (n - 1)} (hij : i ≠ j) {F : Type} [Field F] [Finite F] {ι : K →+* F}
    {σ : F ≃+* F} (hσ1 : σ ≠ 1) (hσσ : σ * σ = 1) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (P : MinusRootFieldParam hn hirr e t ι σ i j) :
    minusLevelCore e ({i, j} : Finset (Fin (n - 1))) ≤
      centralizer (modelToG e (stabPairsBar (coordinateQuadMinus n K (by omega) β γ)
        (minusIndexEquiv n (by omega) (.inl i)) (minusIndexEquiv n (by omega) (.inr (.inl i)))
        (minusIndexEquiv n (by omega) (.inl j))
        (minusIndexEquiv n (by omega) (.inr (.inl j)))) : Set G) := by
  have hORTH := forall_le_centralizer_minusPlanes hset hn hK hq hirr e ht hKt hij
  have hUT : minusLevelCore e ({i, j} : Finset (Fin (n - 1))) ≤
      centralizer (modelToG e (minusLevelTorus (by omega) β γ
        ({i, j} : Finset (Fin (n - 1)))) : Set G) :=
    centralizerPerfectCore_le_centralizer _
  rw [← P.range_eq]
  refine range_le_centralizer_of_fieldTwist hq ι hσ1 hσσ hfix P.φ P.N3 (P.range_eq ▸ hUT)
    (fun A => modelToG_frameLeviProj_le_centralizer (by omega) e hij (P.N1 A)) ?_
  intro S hSp hSs hSt hST hzS
  rw [P.upper] at hSt hzS
  exact hORTH S hSp hSs hSt hST hzS

end StepA

end CFSG.SeitzReduction.OmegaPilot
