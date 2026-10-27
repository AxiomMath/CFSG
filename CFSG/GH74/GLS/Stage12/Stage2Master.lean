module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.Main
public import CFSG.GH74.GLS.Stage2.Final.Thm4.SixA
public import CFSG.GH74.GLS.Stage2.Final.Thm4.L192Final
public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193
public import CFSG.GH74.GLS.Stage2.Final.Thm4.EvenOverCGlue
public import CFSG.GH74.GLS.Stage2.Final.L26.M12Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Assembly
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyAllInnerThm
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyCoreThreeBFinal
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultFive
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.L64Odd87
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Closed
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Main
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Main
public import CFSG.GH74.GLS.Stage2.Signalizer.L52One
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoFinal
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.T3Main
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Lie
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2FinTop
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.MainW

public section

namespace CFSG.GH74.GLS.Stage12

open CFSG.GH74.GLS.Stage2 CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Bender
  CFSG.GH74.GLS.Stage12

structure Stage2Leaves : Prop where
  thm1 : Thm1.Thm1Leaves
  sig55 : Signalizer.Ivk8.Lemma5_5m
  oddThree : Thm2.Gap56.OddCoreThreeLy
  thm2 : Thm2.Thm2Leaves
  thm6 : Thm6.Thm6Leaves

namespace Stage2Leaves

variable (L : Stage2Leaves)

include L

omit L in
theorem p34
    : Leaf_Prop34 :=
  P34.leaf_prop34_proved

theorem thm1_primePower
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    :
    Thm1.Thm1PrimePower :=
  Thm1.thm1_primePower p34 ivk33 Thm1.bender12_thm Thm1.bender13_thm Thm1.bender14_thm
    (Thm1.L64.lemma6_4_of_odd87 hGA)
    (Thm1.cf67NonAltJ1_thm hGA Thm1.LyOut.lyAllInner_thm Thm1.LyCore.lyCentralizerCore_thm Thm1.LyMult.lyMultTrivial_thm) L.thm1

theorem thm2False
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : Thm2.Thm2False :=
  have hSch : P34.GHSchreier := fun J _ _ _ hn hG => GHSch.ghSchreier_thm J hn hG
  have hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Stage12.Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S := fun _ _ _ _ _ _ c => c.detail.l4_two
  have hND : Signalizer.Odd87.NonCentralDihedral := Signalizer.Odd87.nonCentralDihedral_of_ctx hfld hSch
  have h29 : Signalizer.Odd87.Lemma29First := Signalizer.Odd87.lemma29First_proved hND
  have h31 : Signalizer.Odd87.Lemma31Narrow :=
    Signalizer.Odd87.leaf_lemma31Narrow_of h29 (Signalizer.Odd87.lemma29NonSolv_of h29)
      (Signalizer.Odd87.invSec_of_secX (Signalizer.Odd87.secX_proved hfld hSch)) hfld hSch
  Thm2.thm2_false_w Thm1.qp_exists_thm
    (Signalizer.prop_4_7S_of Signalizer.sdWr_rank2
      (Signalizer.Odd87.prop4_7S_proved (Signalizer.Odd87.prop4_2_of_odd87 hGA) h31 hND h29))
    (Signalizer.Ivk8.prop_5_1w'_of_m Signalizer.sdWr_rank2 (Signalizer.lemma5_2_of_halves Signalizer.lemma5_2One_thm
      (Signalizer.lemma5_2Two_thm (fun _ _ _ _ _ _ h => h.detail.l4_two)
        (fun J _ _ _ hn hG => GHSch.ghSchreier_thm J hn hG))) Signalizer.L53.lemma5_3_thm L.sig55) Signalizer.L48.lemma4_8w_thm p34
    (Thm2.lemma9_15_of_tail3_proved
      (Signalizer.Odd87.prop_4_3E (Signalizer.Odd87.prop4_2_of_odd87 hGA) h31) p34
      (Thm2.P911.prop9_11core_final (Signalizer.Odd87.prop_4_3E (Signalizer.Odd87.prop4_2_of_odd87 hGA) h31)
        Thm1.LyOut.lyAllInner_thm))
    L.oddThree

theorem exEven
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : ExistsEvenFStar := by
  intro G _ _ z k S hctx
  by_contra hno
  have hodd : ∀ M ∈ maximalOverCentralizer z, Odd (Nat.card ↥(generalizedFitting ↥M)) :=
    fun M hM => Nat.not_even_iff_odd.mp (fun he => hno ⟨M, hM, he⟩)
  exact L.thm2False hGA G z k S hctx hodd (L.thm1_primePower hGA G z k S hctx hodd)

theorem thm4 (hcov : Thm4.PSp4_oddCover)
    : Thm4.Ch4Thm4 :=
  Thm4.thm4_of_19_2_to_19_4 p34 (L26.leaf_lemma26_of_g2_m12 L26.lemma26K_g2 L26.lemma26K_m12) (Thm4.L192.lemma19_2_thm (Thm4.prop17_1 p34 hcov))
    (Thm4.lemma19_3_thm (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.prop18_13_thm hcov) (Thm4.prop17_1 p34 hcov)) (Thm4.lemma19_4_thm (CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.prop18_13_thm hcov) (Thm4.prop17_1 p34 hcov)) hcov

theorem oddCoreOverC
    (hcov : Thm4.PSp4_oddCover)
    : Thm4.OddCoreOverC :=
  Thm6.oddCoreOverC_of_prop201 (L.thm4 hcov) (Thm6.prop201_of_leaves L.thm6)

theorem evenOverC
    (hcov : Thm4.PSp4_oddCover)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : Thm4.EvenOverC :=
  have hSch : P34.GHSchreier := fun J _ _ _ hn hG => GHSch.ghSchreier_thm J hn hG
  have hfld : ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Stage12.Kind) (S : Subgroup G),
      Stage2Ctx G z k S → Stage1.Main.L4TwoFieldStmt G z k S := fun _ _ _ _ _ _ c => c.detail.l4_two
  have hND : Signalizer.Odd87.NonCentralDihedral := Signalizer.Odd87.nonCentralDihedral_of_ctx hfld hSch
  have h29 : Signalizer.Odd87.Lemma29First := Signalizer.Odd87.lemma29First_proved hND
  have h31 : Signalizer.Odd87.Lemma31Narrow :=
    Signalizer.Odd87.leaf_lemma31Narrow_of h29 (Signalizer.Odd87.lemma29NonSolv_of h29)
      (Signalizer.Odd87.invSec_of_secX (Signalizer.Odd87.secX_proved hfld hSch)) hfld hSch
  Thm4.EvenOver.evenOverC_proved p34 (L.oddCoreOverC hcov) (L.exEven hGA)
    (Signalizer.Odd87.prop_4_3E (Signalizer.Odd87.prop4_2_of_odd87 hGA) h31)

theorem main
    (hcov : Thm4.PSp4_oddCover)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    : Stage2Main := by
  have h6 := Thm6.thm6 (L.exEven hGA) (L.thm4 hcov) p34 L.thm6
  have hsix := Thm4.stage2_sixA p34 (L.oddCoreOverC hcov) (L.evenOverC hcov hGA)
  intro G _ _ z k S hctx
  refine ⟨fun h => h6.1 G z k S hctx h, ?_, ?_⟩
  · intro ε q L₁ L₂ hk h1
    subst hk
    exact h6.2 G z S ε q L₁ L₂ hctx h1
  · intro ε q L₁ L₂ hk h1 p f hp hpf M hM hlt
    exact hsix G z k S hctx ε q L₁ L₂ hk h1 p f hp hpf M hM hlt

end Stage2Leaves

end CFSG.GH74.GLS.Stage12
