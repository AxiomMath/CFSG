module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAsmAlpha
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.OuterThree.LieTwo
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeAsmBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HStdList

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)
open scoped commutatorElement


private theorem false_of_noSmallModel
    (hM : ModelRed) {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hK : CFSG.Open.IsKGroup Ω)
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hLn : L.Normal) (hMax : CFSG.LocalAnalysis.GLTheoremA.S171.MaxG 3 B)
    (hstd : ∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K)
    (hsmall : ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K)
    (hT : ∃ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) ∧
      T ≤ Subgroup.centralizer ({x} : Set Ω) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (G₀ : Type) [Group G₀] [Finite G₀] (hAut : AutThreePowInner G₀)
    (hIso : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* G₀))
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) (hNo : NoSmallModel G₀) : False := by
  obtain ⟨Bb, hBb⟩ := hM Ω B x L hK hcfg hLn hMax hstd hsmall hT G₀ hAut hIso hZ
  exact hNo Bb hBb


private theorem false_of_excNoSmall
    (hA : AlphaRed) {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hK : CFSG.Open.IsKGroup Ω)
    (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hLn : L.Normal) (hMax : CFSG.LocalAnalysis.GLTheoremA.S171.MaxG 3 B)
    (hstd : ∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K)
    (hsmall : ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K)
    (d : TauCeti.ValidLieTypeIndex)
    (hIso : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* d.Group))
    (hNo : HStdExcl.NoSmall d.Group) : False := by
  obtain ⟨α, hα3, hα1, -, J, -, hJcomp, -, hJsmall⟩ :=
    hA Ω B x L hK hcfg hLn hMax hstd hsmall d hIso
  exact hNo α hα3 hα1 J hJcomp hJsmall

theorem t171SmallTypeFact_of_lie
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hU42 : CFSG.LocalAnalysis.GLTheoremA.I1431C2.U42InnField)
    (hM : ModelRed) (hA : AlphaRed) (hA6 : A6InnField) (hE : ExcNoSmall)
    (hU : UniHighWit) (hLin : FamLin) (hU4 : FamU4) (hSp : FamSp) (hOmP : FamOmP)
    (hOmM : FamOmM) (hCard : BCardLe) (hW : Wit5False)
    {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω} {L : Subgroup Ω}
    (hK : CFSG.Open.IsKGroup Ω) (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hLn : L.Normal) (hMax : CFSG.LocalAnalysis.GLTheoremA.S171.MaxG 3 B)
    (hstd : ∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K)
    (hsmall : ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K)
    (hT : ∃ T : Subgroup Ω, T ≤ Subgroup.normalizer (L : Set Ω) ∧
      T ≤ Subgroup.centralizer ({x} : Set Ω) ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set Ω) ∧ (⁅T, B⁆ : Subgroup Ω) ≠ ⊥)
    (hLie : catalogIs (PSimple 3 L) (onLie fun d => d.characteristic = 2)) :
    catalogIs (↥L ⧸ Subgroup.center ↥L)
      (fun i => S9.isU5two i ∨ S9.isU6two i ∨ S9.isD4two i) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := hLie
  cases i with
  | lie dd =>
    obtain ⟨d0, hv⟩ := dd
    change d0.characteristic = 2 at hi
    haveI : Finite (TauCeti.CFSGIndex.lie ⟨d0, hv⟩).Group :=
      (CFSG.Assembly.lie_finite_simple ⟨d0, hv⟩).1
    haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨d0, hv⟩).Group :=
      (CFSG.Assembly.lie_finite_simple ⟨d0, hv⟩).2
    haveI : Nontrivial (TauCeti.CFSGIndex.lie ⟨d0, hv⟩).Group := IsSimpleGroup.toNontrivial
    have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
        (TauCeti.CFSGIndex.lie ⟨d0, hv⟩).Group) :=
      HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
    obtain ⟨eL⟩ := hIso0
    by_cases htits : d0 = .tits
    · have hExc : ExcTwo d0 := by rw [htits]; trivial
      obtain ⟨α, hα3, hα1, -, J, -, hJcomp, -, hJsmall⟩ :=
        hA Ω B x L hK hcfg hLn hMax hstd hsmall ⟨d0, hv⟩ ⟨eL⟩
      exact (hE ⟨d0, hv⟩ hExc α hα3 hα1 J hJcomp hJsmall).elim
    · have hfs : KD264Lie.fieldSize d0 = 2 :=
        fieldSize_two_of_alphaRed hGA hA hU42 hA6 hK hcfg hLn hMax hstd hsmall
          ⟨d0, hv⟩ ⟨eL⟩ hi htits
      have hdne : d0 ≠ .tits := htits

      cases d0 with
      | A r q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hq : q.card = 2 := hfs
        have hr : 4 ≤ r := four_le_of_typeA_two hv hfs
        have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
          CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_not_three_dvd_center hGA hcfg.qs
            (by
              intro h
              rw [CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex] at h
              obtain ⟨-, h3⟩ := h
              rw [hq] at h3
              norm_num at h3) eL
        have hAut : AutThreePowInner (TauCeti.CFSGIndex.lie
            ⟨.A r q, hv⟩).Group :=
          CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeA_two
            hv hq (MulEquiv.refl _)
        exact (false_of_noSmallModel hM hK hcfg hLn hMax hstd hsmall hT
          (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group hAut hIso0 hZ
          (hLin r q hv hq hr)).elim
      | twistedA r q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hq : q.card = 2 := hfs
        have hr : 3 ≤ r := three_le_of_twistedA_two hv hfs
        rcases (show r = 3 ∨ r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with rfl | rfl | rfl | hr6
        · have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
            CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_not_three_dvd_center hGA hcfg.qs
              (by
              intro h
              rw [CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex] at h
              rcases h with ⟨h4, -⟩ | ⟨-, h3⟩
              · norm_num at h4
              · rw [hq] at h3
                norm_num at h3) eL
          have hAut : AutThreePowInner (TauCeti.CFSGIndex.lie
              ⟨.twistedA 3 q, hv⟩).Group :=
            CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeTwistedA_two
              hv hq (by norm_num) (MulEquiv.refl _)
          exact (false_of_noSmallModel hM hK hcfg hLn hMax hstd hsmall hT
            (TauCeti.CFSGIndex.lie ⟨.twistedA 3 q, hv⟩).Group hAut hIso0 hZ
            (hU4 q hv hq)).elim
        · exact ⟨.lie ⟨.twistedA 4 q, hv⟩, Or.inl hq, hIso0⟩
        · exact ⟨.lie ⟨.twistedA 5 q, hv⟩, Or.inr (Or.inl hq), hIso0⟩
        · have hWit : Wit5 ↥L :=
            hU r q hv hq hr6 L hcfg.qs hIso0
          exact (hW Ω B x L hcfg hMax
            (hCard Ω B x L hcfg hstd hsmall) hWit).elim
      | B r q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hq : q.card = 2 := hfs
        have hr : 3 ≤ r := three_le_of_typeB_two hv hfs
        have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
          CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_not_three_dvd_center hGA hcfg.qs
            (by
            intro h
            rw [CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex] at h
            obtain ⟨-, h3⟩ := h
            rw [hq] at h3
            norm_num at h3) eL
        have hAut : AutThreePowInner (TauCeti.CFSGIndex.lie
            ⟨.B r q, hv⟩).Group :=
          CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeB_two
            hv hq (MulEquiv.refl _)
        exact (false_of_noSmallModel hM hK hcfg hLn hMax hstd hsmall hT
          (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group hAut hIso0 hZ
          (hSp r q hv hq hr)).elim
      | C r q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.C r q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hq2 : q.card = 2 := hfs
        obtain ⟨hp2, -⟩ := CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_primePower_card_two hq2
        have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hvalid
        omega
      | D r q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hq : q.card = 2 := hfs
        have hr : 4 ≤ r := four_le_of_typeD_two hv hfs
        rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
        · exact ⟨.lie ⟨.D 4 q, hv⟩, Or.inr (Or.inr hq), hIso0⟩
        · have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
            CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_not_three_dvd_center hGA hcfg.qs
              (by simp [CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex]) eL
          have hAut : AutThreePowInner (TauCeti.CFSGIndex.lie
              ⟨.D r q, hv⟩).Group :=
            CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeD_two
              hv hq hr5 (MulEquiv.refl _)
          exact (false_of_noSmallModel hM hK hcfg hLn hMax hstd hsmall hT
            (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group hAut hIso0 hZ
            (hOmP r q hv hq hr5)).elim
      | twistedD r q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hq : q.card = 2 := hfs
        have hr : 4 ≤ r := four_le_of_twistedD_two hv hfs
        have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) :=
          CFSG.LocalAnalysis.GLTheoremA.I1431C2.cl_not_three_dvd_center hGA hcfg.qs
            (by simp [CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex]) eL
        have hAut : AutThreePowInner (TauCeti.CFSGIndex.lie
            ⟨.twistedD r q, hv⟩).Group :=
          CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree.autThreePowInner_typeTwistedD_two
            hv hq (MulEquiv.refl _)
        exact (false_of_noSmallModel hM hK hcfg hLn hMax hstd hsmall hT
          (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group hAut hIso0 hZ
          (hOmM r q hv hq hr)).elim
      | E6 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hExc : ExcTwo (.E6 q) := by simpa [ExcTwo] using hfs
        exact (false_of_excNoSmall hA hK hcfg hLn hMax hstd hsmall ⟨.E6 q, hv⟩
          hIso0 (hE ⟨.E6 q, hv⟩ hExc)).elim
      | E7 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hExc : ExcTwo (.E7 q) := by simpa [ExcTwo] using hfs
        exact (false_of_excNoSmall hA hK hcfg hLn hMax hstd hsmall ⟨.E7 q, hv⟩
          hIso0 (hE ⟨.E7 q, hv⟩ hExc)).elim
      | E8 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hExc : ExcTwo (.E8 q) := by simpa [ExcTwo] using hfs
        exact (false_of_excNoSmall hA hK hcfg hLn hMax hstd hsmall ⟨.E8 q, hv⟩
          hIso0 (hE ⟨.E8 q, hv⟩ hExc)).elim
      | F4 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.F4 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hExc : ExcTwo (.F4 q) := by simpa [ExcTwo] using hfs
        exact (false_of_excNoSmall hA hK hcfg hLn hMax hstd hsmall ⟨.F4 q, hv⟩
          hIso0 (hE ⟨.F4 q, hv⟩ hExc)).elim
      | twistedE6 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hExc : ExcTwo (.twistedE6 q) := by simpa [ExcTwo] using hfs
        exact (false_of_excNoSmall hA hK hcfg hLn hMax hstd hsmall ⟨.twistedE6 q, hv⟩
          hIso0 (hE ⟨.twistedE6 q, hv⟩ hExc)).elim
      | trialityD4 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hExc : ExcTwo (.trialityD4 q) := by simpa [ExcTwo] using hfs
        exact (false_of_excNoSmall hA hK hcfg hLn hMax hstd hsmall ⟨.trialityD4 q, hv⟩
          hIso0 (hE ⟨.trialityD4 q, hv⟩ hExc)).elim
      | G2 q =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hvalid
        omega
      | suzuki m =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hvalid
        have hm : 2 ^ (2 * m + 1) = 2 := hfs
        have h1 : 2 * m + 1 = 1 :=
          Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using hm)
        omega
      | reeG2 m =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        have hdiv : 3 ∣ 2 := by
          rw [← hfs]
          exact dvd_pow_self 3 (by omega)
        norm_num at hdiv
      | reeF4 m =>
        have hIso0 : Nonempty (↥L ⧸ Subgroup.center ↥L ≃*
            (TauCeti.CFSGIndex.lie ⟨.reeF4 m, hv⟩).Group) :=
          HStdList.centerQuot_equiv_of_pSimple hcfg.qs f
        simp only [KD264Lie.fieldSize] at hfs
        have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hvalid
        have hm : 2 ^ (2 * m + 1) = 2 := hfs
        have h1 : 2 * m + 1 = 1 :=
          Nat.pow_right_injective (by norm_num : 2 ≤ 2) (by simpa using hm)
        omega
      | tits => exact absurd rfl hdne
  | cyclic _ _ => exact absurd hi (by simp [onLie])
  | alternating _ _ => exact absurd hi (by simp [onLie])
  | sporadic _ => exact absurd hi (by simp [onLie])

end CFSG.LocalAnalysis.GLTheoremA.T171S
