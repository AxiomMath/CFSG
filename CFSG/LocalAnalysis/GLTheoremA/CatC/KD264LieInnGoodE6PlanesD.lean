module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangAlg
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE6ThreeLines

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.RankThree.Classical2 CFSG.RankThree.Lattice
open scoped Matrix MatrixGroups

section Three


theorem perfectCentralizerPlanes_adjointGroup_E6_three (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E6 K) := by
  classical
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_E6_three frobeniusOnRoots_proved K hp hp7 hpK he
  set L := AlgebraicClosure K with hL
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := e6ThreeLine_dvd_of_orderOf hp he
  have hp3 : p ≠ 3 := by omega
  have hq : S.D.q = Nat.card K := by rw [hSD]; rfl
  have hfrob : FrobRootMap (LangDatum.ofFrobenius Fr (Nat.card K) hFr e6PhiThreeWeyl hg0C hg0)
      S.ρ := hSD ▸ S.frob
  have hρM : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = toMat Tag.E6.rank e6ThreeMat *ᵥ γ := by
    intro γ hγ
    rw [frobRootMap_ofFrobenius_apply Nat.card_pos hFr hg0C hg0 hfrob hγ,
      wordProd_smul_eq_wordMat_mulVec, e6Three_wordMat]
  have hlines : ∀ k : Fin 12, ∃ Y : Subgroup (ModGL Tag.E6 L), Y ≤ S.Γ ∧ ⁅Y, Y⁆ = Y ∧
      (∃ x ∈ Y, orderOf x = p) ∧ Y ≤ rootSpan Tag.E6 L
        {γ | ∃ j : ℕ, γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (e6ThreeLineX k) ∨
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (-e6ThreeLineX k)} ∧
      IsRoot Tag.E6 (e6ThreeLineX k) := by
    intro k
    obtain ⟨ρk, σk, hfr, hinj, h01, h12⟩ := e6ThreeLine_frame (L := L) k
    obtain ⟨h02, h10, h21, h20⟩ := e6ThreeLine_sigma hfr h01 h12
    obtain ⟨hMx, hMy⟩ := e6ThreeLine_M k
    have hxr : IsRoot Tag.E6 (e6ThreeLineX k) := by
      rw [← h01]
      exact hfr.isRoot 0 1 (by decide)
    have hyr : IsRoot Tag.E6 (e6ThreeLineY k) := by
      rw [← h12]
      exact hfr.isRoot 1 2 (by decide)
    have hxyr : IsRoot Tag.E6 (e6ThreeLineX k + e6ThreeLineY k) := by
      rw [← h02]
      exact hfr.isRoot 0 2 (by decide)
    have hρx : S.ρ (e6ThreeLineX k) = e6ThreeLineY k := by rw [hρM _ hxr, hMx]
    have hρy : S.ρ (e6ThreeLineY k) = -(e6ThreeLineX k + e6ThreeLineY k) := by
      rw [hρM _ hyr, hMy]
    have hρnx : S.ρ (-e6ThreeLineX k) = -e6ThreeLineY k := by
      rw [S.frob.neg_eq, hρx]
    have hρny : S.ρ (-e6ThreeLineY k) = e6ThreeLineX k + e6ThreeLineY k := by
      rw [S.frob.neg_eq, hρy, neg_neg]
    have hρxy : S.ρ (e6ThreeLineX k + e6ThreeLineY k) = -e6ThreeLineX k := by
      rw [hρM _ hxyr, Matrix.mulVec_add, hMx, hMy]
      abel
    have hρnxy : S.ρ (-(e6ThreeLineX k + e6ThreeLineY k)) = e6ThreeLineX k := by
      rw [S.frob.neg_eq, hρxy, neg_neg]
    have r0 : finRotate 3 0 = 1 := rfl
    have r1 : finRotate 3 1 = 2 := rfl
    have r2 : finRotate 3 2 = 0 := rfl
    have hπ : ∀ i j, i ≠ j → S.ρ (σk i j) = σk (finRotate 3 i) (finRotate 3 j) := by
      intro i j hij
      fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | skip
      · show S.ρ (σk 0 1) = σk (finRotate 3 0) (finRotate 3 1)
        rw [r0, r1, h01, h12, hρx]
      · show S.ρ (σk 0 2) = σk (finRotate 3 0) (finRotate 3 2)
        rw [r0, r2, h02, h10, hρxy]
      · show S.ρ (σk 1 0) = σk (finRotate 3 1) (finRotate 3 0)
        rw [r1, r0, h10, h21, hρnx]
      · show S.ρ (σk 1 2) = σk (finRotate 3 1) (finRotate 3 2)
        rw [r1, r2, h12, h20, hρy]
      · show S.ρ (σk 2 0) = σk (finRotate 3 2) (finRotate 3 0)
        rw [r2, r0, h20, h01, hρnxy]
      · show S.ρ (σk 2 1) = σk (finRotate 3 2) (finRotate 3 1)
        rw [r2, r1, h21, h02, hρny]
    obtain ⟨⟨H, hH⟩, hYΓ, hYp⟩ := splitLine_spec S (k := K) hq.symm hfr hinj (finRotate 3) hπ
    have hord := splitLine_exists_orderOf S hinj hH hp3 hpq
    have hframe : frameRoots σk ⊆ {γ | ∃ j : ℕ,
        γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (e6ThreeLineX k) ∨
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[j] (-e6ThreeLineX k)} := by
      rintro _ ⟨i, j, hij, rfl⟩
      fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | skip
      · exact ⟨0, Or.inl (by simpa using h01)⟩
      · refine ⟨2, Or.inr ?_⟩
        show σk 0 2 = S.ρ (S.ρ (-e6ThreeLineX k))
        rw [hρnx, hρny, h02]
      · exact ⟨0, Or.inr (by simpa using h10)⟩
      · refine ⟨1, Or.inl ?_⟩
        show σk 1 2 = S.ρ (e6ThreeLineX k)
        rw [hρx, h12]
      · refine ⟨2, Or.inl ?_⟩
        show σk 2 0 = S.ρ (S.ρ (e6ThreeLineX k))
        rw [hρx, hρy, h20]
      · refine ⟨1, Or.inr ?_⟩
        show σk 2 1 = S.ρ (-e6ThreeLineX k)
        rw [hρnx, h21]
    exact ⟨_, hYΓ, hYp, hord, inf_le_left.trans (hfr.range ▸ rootSpan_mono hframe), hxr⟩
  obtain ⟨Y, hYΓ, hYp, ⟨x, hxY, hxp⟩, hYspan, hxr⟩ := hlines 0
  have hbig : ∀ D₁ : Subgroup (ModGL Tag.E6 L), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
      (bigComponentSet S D₁).Nonempty := fun D₁ hD₁ hc =>
    ⟨x, subset_bigComponentSet_of_perfect S hD₁ hc hxr hYΓ hYp hYspan hxY hxp hxY⟩
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_of_sylow_le_torus S hsyl hbig)

end Three

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
