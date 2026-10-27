module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympComp

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem quotCenter_cases_of_glaPComponent_conj {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (hm : 1 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (x : StatedSp m K) (hx : x ^ p = 1) {J : Subgroup (StatedProj (StatedSp m K))}
    (hJ : GLAPComponent p (fixSubgroup (MulAut.conj (proj m K x))) J) :
    (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
        n ∣ k ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL a E))) ∨
      (∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
          Nat.card E = (2 ^ k) ^ 2 ∧ n ∣ k ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            ↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ))) ∨
      (∃ s : ℕ, 2 ≤ s ∧ ¬(s = 2 ∧ Nat.card K = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K))) ∨
      Nat.card K = 2 := by
  classical
  obtain ⟨hPIL, hcomp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
      (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
      hp hp2 Nat.prime_two hn hK hm hp2 (fun h => h.elim) x hx
  have hperfJ := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj (proj m K x))) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJ hJle).1
  obtain ⟨X, inst, hXfin, ⟨hXLie, hA6⟩, hfac, f, hf, hker⟩ := hcomp J hJcomp
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect f hf hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hSp42
  ·
    rw [hK] at hSL
    exact Or.inl (Y10GCenterQuot.linCase_of_factor eJ hSL)
  ·
    rw [hK] at hSU
    exact Or.inr (Or.inl (Y10GCenterQuot.uniCase_of_factor eJ hSU))
  ·
    obtain ⟨-, -, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hne' : ¬(s = 2 ∧ Nat.card K = 2) := fun h => hne (by rw [h.1, h.2])
    have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
    obtain ⟨eXZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sp (s := s) hs2 hne' hchar eX
    exact Or.inr (Or.inr (Or.inl ⟨s, hs2, hne', ⟨eJ.trans eXZ⟩⟩))
  ·
    obtain ⟨-, -, hK2, -⟩ := hSp42
    exact Or.inr (Or.inr (Or.inr hK2))

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympComp

end
