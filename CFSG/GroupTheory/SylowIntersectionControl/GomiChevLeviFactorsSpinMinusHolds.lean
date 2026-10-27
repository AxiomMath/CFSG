module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviFactorInputs
public import Certificates.Certificate43
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusDBlock
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusModel
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SLChev
import CFSG.RankThree.PartOne.CTP.SpinCenterEven
import CFSG.RankThree.PartOne.CTP.SU4EvenBridge
import CFSG.LocalAnalysis.SectionRank.EvenCover.Unitary
import CFSG.ClassicalInvolution.ModelFacts.LinearAutLift
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.StandardType.GGLatDefs
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.ClassicalInvolution.WeakCT.SpinMinus
import CFSG.GH74.GLS.Classes
import CFSG.GH74.Statements
import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SpinMinusBlocks
import CFSG.LieType.Universal.Spin
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

private theorem cartanB_ne_zero_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    cartanB m i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  simp only [cartanB, Matrix.of_apply, if_neg hij]
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => by split_ifs <;> norm_num⟩
  · rw [if_neg h]
    exact ⟨fun h0 => absurd rfl h0, fun h0 => absurd h0 h⟩

private theorem nodeAdj_val_minus {n : ℕ} {F : Type} [Field F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {C : Set (Fin (n - 1))} {i j : Fin (n - 1)}
    (h : NodeAdj (minusDatum n hirr) C i j) :
    i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have h1 := (TauCeti.IsFiniteType.diagramGraph_adj_iff
    (isFiniteType_cartanB (n - 1))).mp h.2.2
  exact (cartanB_ne_zero_iff h1.1).mp h1.2

private theorem odd_card_center_of_center_eq_bot {X : Type} [Group X]
    (h : Subgroup.center X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  rw [h, Subgroup.card_eq_one.mpr rfl]
  exact ⟨0, rfl⟩

private theorem gomiLeviFactor_of_isQuasisimple_classical {X : Type} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) (hZ : Odd (Nat.card (Subgroup.center X)))
    (hcl : IsClassicalTwoOrG2 (X ⧸ Subgroup.center X)) : GomiLeviFactor X :=
  Or.inl (IsGomiChevTwo.of_isQuasisimple hq hZ (isChevTwo_of_classicalTwoOrG2 hcl))

private theorem center_spinMinus_three_eq_bot {F K : Type} [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    {b c : F} (e : spinGroup (quadMinus 3 F b c) ≃* SU (unitaryInvolution K 2 f) 4) :
    Subgroup.center (spinGroup (quadMinus 3 F b c)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h; exact absurd (congrArg Prod.fst h) (by norm_num)
  obtain ⟨-, hZ⟩ := isQuasisimple_statedSU_of_card (p := 2) (f := f) hK
    (by norm_num : 3 ≤ 4) hnq
  have hZbot : Subgroup.center (StatedSU 4 (2 ^ f) K) = ⊥ := by
    rw [hZ, CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSU_four_eq_bot
      (q := 2 ^ f)]
  let e' : SU (unitaryInvolution K 2 f) 4 ≃* StatedSU 4 (2 ^ f) K := equivStatedSU hK 4
  have hcSU : Subgroup.center (SU (unitaryInvolution K 2 f) 4) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (SU (unitaryInvolution K 2 f) 4))
      (f := e'.toMonoidHom) e'.injective).mp (by
        rw [map_center_mulEquiv e', hZbot])
  exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (spinGroup (quadMinus 3 F b c)))
    (f := e.toMonoidHom) e.injective).mp (by rw [map_center_mulEquiv e, hcSU])

private theorem gomiLeviFactor_runBlock {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {C : Set (Fin (n - 1))} {lo hi : ℕ}
    (hlh : lo ≤ hi) (hhi : hi + 2 < n) (hn : 4 ≤ n) (hCeq : C = runNodes n lo hi)
    (hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F))
    (hZ : Odd (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F))))
    (hcl : IsClassicalTwoOrG2 (Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (hi - lo + 2)) F))) :
    GomiLeviFactor ↥(leviM (minusDatum n hirr) C) := by
  rw [hCeq]
  exact GomiLeviFactor.of_mulEquiv (chEquivMinus hirr hlh hhi hn)
    (gomiLeviFactor_of_isQuasisimple_classical hq hZ hcl)

private theorem gomiLeviFactor_lastRun {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {C : Set (Fin (n - 1))}
    {a : Fin (n - 1)} {k : ℕ} (hk : 3 ≤ k) (h : a.val + k = n)
    (hCeq : C = blkNodes (n - 1) a.val)
    (hq : CFSG.IsQuasisimple (spinGroup (quadMinus k F b c)))
    (hZ : Odd (Nat.card (Subgroup.center (spinGroup (quadMinus k F b c)))))
    (hcl : IsClassicalTwoOrG2 (spinGroup (quadMinus k F b c) ⧸
      Subgroup.center (spinGroup (quadMinus k F b c)))) :
    GomiLeviFactor ↥(leviM (minusDatum n hirr) C) := by
  have : Finite ↥(spinGroup (quadMinus k F b c)) :=
    Finite.of_injective (matM (b := b) (c := c) (by omega : 1 ≤ k))
      (matM_injective hirr (by omega : 1 ≤ k))
  rw [hCeq]
  exact GomiLeviFactor.of_mulEquiv (blkEquivMinus h hirr hk)
    (gomiLeviFactor_of_isQuasisimple_classical hq hZ hcl)

private theorem le_of_interval {n : ℕ} {a b' : Fin (n - 1)} {C : Set (Fin (n - 1))}
    (hCab : C = Set.Icc a b') (ha : a ∈ C) : a.val ≤ b'.val := by
  have h := ha; rw [hCab] at h; exact Fin.le_def.mp h.2

private theorem interval_eq_runNodes {n : ℕ} {a b' : Fin (n - 1)} {C : Set (Fin (n - 1))}
    (hCab : C = Set.Icc a b') : C = runNodes n a.val b'.val := by
  rw [hCab]; ext j
  simp only [Set.mem_Icc, runNodes, Set.mem_setOf_eq, Fin.le_def]

private theorem interval_eq_blkNodes {n : ℕ} {a b' : Fin (n - 1)} {C : Set (Fin (n - 1))}
    (hCab : C = Set.Icc a b') (hb' : b'.val + 1 = n - 1) : C = blkNodes (n - 1) a.val := by
  rw [hCab]; ext j
  simp only [Set.mem_Icc, blkNodes, Set.mem_setOf_eq, Fin.le_def]
  exact ⟨fun h => h.1, fun h => ⟨h, by have := j.isLt; omega⟩⟩

private theorem lt_of_card_two_interval {n : ℕ} {a b' : Fin (n - 1)} {C : Set (Fin (n - 1))}
    (hCab : C = Set.Icc a b') (h2 : 2 ≤ C.ncard) : a.val < b'.val := by
  have h2' : 2 ≤ (Set.Icc a b').ncard := by rw [hCab] at h2; exact h2
  rw [Set.ncard_Icc] at h2'
  simp only [Fin.card_Icc] at h2'
  omega

theorem gomiLeviFactorsSpinMinus_holds :
    GomiLeviFactorsSpinMinus := by
  intro n F _ _ _ b c hirr hn C hC h2C hne
  let C' : Set (Fin (n - 1)) := C
  have hC' : IsNodeConnected (minusDatum n hirr) C' := hC
  obtain ⟨a, b', ha, hb', hCab⟩ :
      ∃ a b' : Fin (n - 1), a ∈ C ∧ b' ∈ C ∧ C = Set.Icc a b' :=
    hC'.exists_eq_Icc (fun _ _ h => nodeAdj_val_minus hirr h)
  have hle : a.val ≤ b'.val := le_of_interval hCab ha
  have hlt' : a.val < b'.val := lt_of_card_two_interval hCab h2C
  rcases lt_or_eq_of_le (show b'.val + 1 ≤ n - 1 by omega) with hlt | heq
  · have hhi : b'.val + 2 < n := by omega
    have hCeq := interval_eq_runNodes (n := n) hCab
    have hk : 3 ≤ b'.val - a.val + 2 := by omega
    have hsl := isChevComponent_sl (F := F) (k := b'.val - a.val + 2) (Or.inl hk)
    change GomiLeviFactor ↥(leviM (minusDatum n hirr) C')
    exact gomiLeviFactor_runBlock hirr hle hhi hn hCeq hsl.1
      (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
        CFSG.ClassicalInvolution.ModelFacts.LinearAut.not_dvd_card_center_specialLinearGroup))
      hsl.2
  · have hCeq := interval_eq_blkNodes (n := n) hCab heq
    have hk : 3 ≤ n - a.val := by omega
    rcases lt_or_eq_of_le hk with hk4 | hk3
    · have hs := isChevComponent_spinMinus hirr hk4
      change GomiLeviFactor ↥(leviM (minusDatum n hirr) C')
      exact gomiLeviFactor_lastRun hirr hk (by omega) hCeq hs.1
        (odd_card_center_of_center_eq_bot
          (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hk4 hirr)) hs.2
    · obtain ⟨f, hf1, hfcard⟩ := CFSG.AGLEmbedding.ParabHub.exists_card_eq_two_pow F
      let K := GaloisField 2 (2 * f)
      have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
        rw [GaloisField.card _ _ (by omega), ← pow_mul, mul_comm]
      have : CharP K 2 := inferInstance
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨_, e, -⟩ := CFSG.RankThree.PartOne.CTP.SU4Even.exists_equiv_su_four_even
        (F := F) (K := K) hfcard hKcard hirr
      have hs := chev_spinMinus_three (F := F) (b := b) (c := c) hirr
      change GomiLeviFactor ↥(leviM (minusDatum n hirr) C')
      exact gomiLeviFactor_lastRun (k := 3) hirr (by norm_num) (by omega) hCeq hs.1
        (odd_card_center_of_center_eq_bot (center_spinMinus_three_eq_bot hKcard e)) hs.2

end CFSG.GroupTheory
