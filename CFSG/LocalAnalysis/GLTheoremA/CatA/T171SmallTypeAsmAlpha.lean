module

public import CFSG.Assembly.InCatalogConverse
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeDefs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult


public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (AutThreePowInner)


theorem fieldSize_two_of_alphaRed {Ω : Type} [Group Ω] [Finite Ω] {B : Subgroup Ω} {x : Ω}
    {L : Subgroup Ω} (hGA : CFSG.Open.GriessAllModelsStatement)
    (hA : AlphaRed) (hU42res : CFSG.LocalAnalysis.GLTheoremA.I1431C2.U42InnField)
    (hA6res : A6InnField)
    (hK : CFSG.Open.IsKGroup Ω) (hcfg : CFSG.LocalAnalysis.GLTheoremA.S171.Cfg Ω 3 B x L)
    (hLn : L.Normal) (hMax : CFSG.LocalAnalysis.GLTheoremA.S171.MaxG 3 B)
    (hstd : ∃ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K)
    (hsmall : ∀ D K : Subgroup Ω, GLAStdSubPre 3 B x L D K → GLASmall K)
    (d : TauCeti.ValidLieTypeIndex) (hIso : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* d.Group))
    (hdchar : d.1.characteristic = 2) (hdne : d.1 ≠ .tits) :
    KD264Lie.fieldSize d.1 = 2 := by
  haveI : Finite d.Group := (CFSG.Assembly.lie_finite_simple d).1
  haveI : IsSimpleGroup d.Group := (CFSG.Assembly.lie_finite_simple d).2
  haveI : Nontrivial d.Group := IsSimpleGroup.toNontrivial
  obtain ⟨α, hα3, hα1, hαin, J, hJcomp, hJisComp, hJtype, hJsmall⟩ :=
    hA Ω B x L hK hcfg hLn hMax hstd hsmall d hIso
  have hJqs : CFSG.Open.IsQuasisimple ↥J := hJisComp.2.2
  have hJnt : Nontrivial ↥J := by
    rcases hJsmall with hsmall | hsmall
    · have hqnt : Nontrivial (↥J ⧸ Subgroup.center ↥J) := by
        refine Finite.one_lt_card_iff_nontrivial.mp ?_
        rw [hsmall]; norm_num
      exact (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
    · have hqnt : Nontrivial (↥J ⧸ Subgroup.center ↥J) := by
        refine Finite.one_lt_card_iff_nontrivial.mp ?_
        rw [hsmall]; norm_num
      exact (QuotientGroup.mk_surjective (s := Subgroup.center ↥J)).nontrivial
  have hJnab : ∃ a b : d.Group, a * b ≠ b * a := by
    by_contra h
    push Not at h
    haveI : IsMulCommutative ↥J := isMulCommutative_iff.2 (fun a b => Subtype.ext (h a b))
    have hbot : commutator ↥J = ⊥ := commutator_eq_bot_iff (G := ↥J).2 inferInstance
    have hsub : Subsingleton ↥J := by
      have htop : (⊤ : Subgroup ↥J) = ⊥ := by
        rw [← hJqs.1]
        exact hbot
      refine ⟨fun a b => ?_⟩
      have ha : a ∈ (⊥ : Subgroup ↥J) := by rw [← htop]; trivial
      have hb : b ∈ (⊥ : Subgroup ↥J) := by rw [← htop]; trivial
      rw [Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    exact not_subsingleton ↥J hsub
  have hαin' : α ∈ innAutDerived d.Group := hαin hdne
  rcases hJtype with hU4 | hA6type
  · exact hU42res d.Group ‹IsSimpleGroup d.Group› hJnab d hdchar ⟨MulEquiv.refl _⟩ α hαin'
      ⟨hα3, hα1, J, hJcomp, hU4⟩
  · exact hA6res d.Group ‹IsSimpleGroup d.Group› hJnab d hdchar ⟨MulEquiv.refl _⟩ α hαin'
      ⟨hα3, hα1, J, hJcomp, hA6type⟩

end CFSG.LocalAnalysis.GLTheoremA.T171S
