module

public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Lang.TwE6Step3.TwoA2Split
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8SylowSeven
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngine2
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LieType.SeitzGeneration
  CFSG.ComponentClassification CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.HardMathSupport.Lang.AnisoE8 CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine
open scoped MatrixGroups

variable {K : Type} [Field K]

section FamilyGroup


theorem familyGroup_le_normalizer_rootSpan {ι : Type} (a : ι → Fin Tag.E8.rank → Kˣ) :
    familyGroup (K := K) a ≤
      Subgroup.normalizer (rootSpan Tag.E8 K (familyKernel a) : Set (ModGL Tag.E8 K)) := by
  rw [familyGroup]
  exact sup_le (torusGroup_le_normalizer_rootSpan fun α hα => hα.1) Subgroup.le_normalizer

end FamilyGroup

section CanonicalRep


theorem canonicalRep_mem_normalizer_rootSpan_of_mem_familyStabilizer
    {ι : Type} {a : ι → Fin Tag.E8.rank → Kˣ} {w : WeylGroup Tag.E8}
    (hw : w ∈ familyStabilizer a) :
    canonicalRep (coxeterSystem Tag.E8) K w ∈
      Subgroup.normalizer (rootSpan Tag.E8 K (familyKernel a) : Set (ModGL Tag.E8 K)) := by
  have hS : ∀ α ∈ familyKernel a, IsRoot Tag.E8 α := fun α hα => hα.1
  have himg : (fun α => w • α) '' familyKernel a = familyKernel a := image_familyKernel hw
  have himg' : (fun α => w⁻¹ • α) '' familyKernel a = familyKernel a :=
    image_familyKernel (familyStabilizer_inv hw)
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨?_, ?_⟩
  · intro hh
    exact canonicalRep_conj_mem_rootSpan (K := K) w
      (S := familyKernel a) (S' := familyKernel a)
      (fun γ hγ => ⟨hγ.1, by rw [← himg]; exact ⟨γ, hγ, rfl⟩⟩) hh
  · intro hh
    have hconj := canonicalRep_inv_conj_mem_rootSpan (K := K) w
      (S := familyKernel a) (S' := familyKernel a)
      (fun γ hγ => ⟨hγ.1, by rw [← himg']; exact ⟨γ, hγ, rfl⟩⟩) hh
    have heq : (canonicalRep (coxeterSystem Tag.E8) K w)⁻¹ *
        (canonicalRep (coxeterSystem Tag.E8) K w * h *
          (canonicalRep (coxeterSystem Tag.E8) K w)⁻¹) *
          canonicalRep (coxeterSystem Tag.E8) K w = h := by group
    rwa [heq] at hconj

end CanonicalRep

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Spin
