module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.Char3
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.OutTriD4

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo.KFacts
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem noL2OuterAt_mono {Fam Fam' : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hle : ∀ t n p f, Fam' t n p f → Fam t n p f) (h : NoL2OuterAt Fam) : NoL2OuterAt Fam' :=
  fun P _ _ t n p f hadm ht hF hm => h P t n p f hadm ht (hle t n p f hF) hm

theorem hOK_of_noL2OuterAt {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop} (h : NoL2OuterAt Fam) :
    ∀ (P : Type) [Group P] [Finite P] (t : StatedLieTag) (n p f : ℕ),
      StatedLieAdmissible t n p f → t ≠ .Tits → Fam t n p f → CFSG.Blueprint.LieModel P t n p f →
        FamOK P :=
  fun P _ _ t n p f hadm ht hF hm ψ hψ3 hninn =>
    ⟨1, ψ, by simp, h P t n p f hadm ht hF hm ψ hψ3 hninn⟩

theorem y1431NoCfgAt_char3_of_outDerived (hKD : KDCharP 3)
    {Fam : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hB : (∀ t n p f, Fam t n p f → t ∈ classicalTags) ∨ CFSG.TauCetiBridge.TypewiseBridges)
    (hp3 : ∀ t n p f, Fam t n p f → p = 3) (hOut : OutDerived3At Fam) : Y1431NoCfgAt Fam := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain rfl := hp3 t n p f hF
  have hin := c.mem_innerAut_of_outDerived (MulEquiv.refl _)
    (fun _ => hOut (Y ⧸ Subgroup.center Y) t n 3 f hadm ht hF hm)
  exact y1431_false_of_char3_of_bridges hKD c hq0 hqq (MulEquiv.refl _)
    (isInnerAut_congr_centerDescend (MulEquiv.refl _) (hin ξ c.mem))
    (hB.imp (fun h => h t n 3 f hF) id) hm

theorem y1431_noCfg_reeG2 (hKD : KDCharP 3) (hB : CFSG.TauCetiBridge.TypewiseBridges)
    (hN : NoL2OuterAt FamReeG2) : Y1431NoCfgAt FamReeG2 := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  have hp3 : p = 3 := by
    subst hF
    exact hadm.2.2.2.1
  exact y1431NoCfgAt_char3_of_bridges (Fam := fun t n p f => FamReeG2 t n p f ∧ p = 3) hKD
    (.inr hB) (fun t n p f hF => hF.2)
    (hOK_of_noL2OuterAt (noL2OuterAt_mono (fun t n p f hF => hF.1) hN))
    Y Â ξ J q c t n p f hadm ht ⟨hF, hp3⟩ hm q0 hq0 hqq

theorem y1431_noCfg_g2High (hKD : KDCharP 3) (hB : CFSG.TauCetiBridge.TypewiseBridges)
    (hN : NoL2OuterAt FamG2) : Y1431NoCfgAt FamG2High :=
  y1431NoCfgAt_char3_of_bridges hKD (.inr hB) (fun t n p f hF => hF.2)
    (hOK_of_noL2OuterAt (noL2OuterAt_mono (fun t n p f hF => hF.1) hN))

theorem y1431_noCfg_triD4High (hKD : KDCharP 3) (hB : CFSG.TauCetiBridge.TypewiseBridges)
    (hOut : OutDerived3At FamTriD4High) : Y1431NoCfgAt FamTriD4High :=
  y1431NoCfgAt_char3_of_outDerived hKD (.inr hB) (fun t n p f hF => hF.2) hOut

section Certified

set_option linter.unusedSectionVars false


theorem outDerived3_triD4High : OutDerived3At FamTriD4High := by
  intro P _ _ t n p f hadm ht hF hm τ hτ _
  obtain ⟨rfl, -⟩ := hF
  exact t6outtrid4_isInnerAut_of_mem_innAutDerived hm hτ

end Certified

end CFSG.HardMathSupport.Dickson.Sec6.I1431
