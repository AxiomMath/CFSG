module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthInnerExport
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorOmega
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthComp

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem quotCenter_cases_of_glaPComponent_conj_omega {G : Type} [Group G] [Finite G]
    {t : StatedLieTag} (ht : t = .POmegaPlus ∨ t = .POmegaMinus) {m f p : ℕ}
    (hG : StatedClassicalModel G t m 2 f) (hp : p.Prime) (hp2 : p ≠ 2) (a : G) (ha : a ^ p = 1)
    {J : Subgroup G} (hJ : GLAPComponent p (fixSubgroup (MulAut.conj a)) J) :
    (∃ (b k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ b ∧ Nat.card E = 2 ^ k ∧
        f ∣ k ∧ Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSL b E))) ∨
      (∃ (b k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
          (hτ : ∀ y, τ (τ y) = y), 2 ≤ b ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
          Nat.card E = (2 ^ k) ^ 2 ∧ f ∣ k ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            ↥(heldSU b E τ hτ) ⧸ Subgroup.center ↥(heldSU b E τ hτ))) ∨
      (∃ (s : ℕ) (K' : Type) (_ : Field K') (_ : Finite K'), 2 ≤ s ∧ Nat.card K' = 2 ^ f ∧
        ¬(s = 2 ∧ Nat.card K' = 2) ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃* StatedProj (StatedSp s K'))) ∨
      (∃ s : ℕ, StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaPlus s 2 f ∨
        StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .POmegaMinus s 2 f) := by
  classical
  have hPIL : CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer
      (MulAut.conj a) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_omega
      (Or.inr ht) hG hp hp2 hp2 a ha
  have hperfJ : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ
  have hJle := hPIL J hJ.1 hperfJ
  have hJcomp : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj a)) :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
      hJ hJle).1
  obtain ⟨X, inst, -, hXLie, hfac, -, g, hg, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_lieFactor_of_component_conj_omega_card
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.omegaFactorField_holds
      hp hp2 (Or.inr ht) hG hp2 a ha J hJcomp
  letI := inst
  obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
    hXLie.perfect g hg hker
  unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.OrthFactorOver at hfac
  rcases hfac with hSL | hSU | hSp | hOm
  ·
    exact Or.inl (Y10GCenterQuot.linCase_of_factor eJ hSL)
  ·
    exact Or.inr (Or.inl (Y10GCenterQuot.uniCase_of_factor eJ hSU))
  ·
    obtain ⟨K', _, _, hK'card, hK'ring, s, hs2, hne, ⟨eX⟩⟩ := hSp
    have hchar : CharP K' 2 := ringChar.of_eq hK'ring
    have hne' : ¬(s = 2 ∧ Nat.card K' = 2) := fun h => hne (by rw [h.1, h.2])
    obtain ⟨eXZ⟩ := Y10GCenterQuot.nonempty_centerQuot_sp (s := s) hs2 hne' hchar eX
    exact Or.inr (Or.inr (Or.inl
      ⟨s, K', _, Finite.of_fintype K', hs2, hK'card, hne', ⟨eJ.trans eXZ⟩⟩))
  ·
    obtain ⟨K', _, _, V, _, _, _, Q, hK'card, _, hQ, hd, hT, ⟨eX⟩⟩ := hOm
    obtain ⟨s, hs⟩ :=
      Y10GInnOrthModel.exists_statedClassicalModel_quotCenter_orthDerived
        hK'card hQ hd hT eX
    rcases hs with hplus | hminus
    · exact Or.inr (Or.inr (Or.inr
        ⟨s, Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hplus)⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨s, Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eJ.symm hminus)⟩))

end CFSG.LocalAnalysis.GLTheoremA.Y10GInnOrthComp

end
