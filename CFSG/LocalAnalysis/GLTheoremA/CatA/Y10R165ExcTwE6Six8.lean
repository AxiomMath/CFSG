module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcTwE6Six
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.E6 CFSG.RankThree.Lattice CFSG.HardMathSupport.Lang.TwE6Step3
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise commutatorElement

def tw6SixFrameWeyl : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (e6Word [3, 2, 0])

theorem tw6SixFrameWeyl_supportA2 :
    ((tw6SixFrameWeyl • ·) '' parabolicRoots Tag.E6 tw6SixSupportA2) =
      parabolicRoots Tag.E6 support13 := by
  refine CFSG.RankThree.E6.image_wordProd_parabolicRoots_eq
    (P := fun i => i = 2 ∨ i = 3) (P' := fun i => i = 0 ∨ i = 2) ?_ ?_ ?_ ?_
  · intro i; rw [tw6SixSupportA2]; decide +revert
  · intro i; rw [CFSG.RankThree.E6.mem_support13]; decide +revert
  · decide +kernel
  · decide +kernel

private theorem mem_supportA2A2_compl {i : Fin Tag.E6.rank} :
    i ∉ supportA2A2 ↔ i = e6Index 1 ∨ i = e6Index 3 := by
  rw [mem_supportA2A2]
  constructor
  · intro h
    have h0 : i.val ≠ 0 := fun hv => h (Or.inl (Fin.ext (by simpa [e6Index] using hv)))
    have h2 : i.val ≠ 2 := fun hv => h (Or.inr (Or.inl (Fin.ext (by simpa [e6Index] using hv))))
    have h4 : i.val ≠ 4 := fun hv =>
      h (Or.inr (Or.inr (Or.inl (Fin.ext (by simpa [e6Index] using hv)))))
    have h5 : i.val ≠ 5 := fun hv =>
      h (Or.inr (Or.inr (Or.inr (Fin.ext (by simpa [e6Index] using hv)))))
    have hlt : i.val < 6 := i.isLt
    rcases (by omega : i.val = 1 ∨ i.val = 3) with hv | hv
    · left; exact Fin.ext (by simpa [e6Index] using hv)
    · right; exact Fin.ext (by simpa [e6Index] using hv)
  · rintro (rfl | rfl)
    · push_neg
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
    · push_neg
      exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem tw6SixFrameWeyl_supportA2A2 {p q : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (hq : (q : ZMod p) ^ 2 - (q : ZMod p) + 1 = 0) :
    ((tw6SixFrameWeyl • ·) '' CFSG.RankThree.E6.rootKernel (tw6SixZx p q)) =
      parabolicRoots Tag.E6 supportA2A2 := by
  have hSx : CFSG.RankThree.E6.rootKernel (tw6SixZx p q) =
      e6RootVec '' ↑(Finset.univ.filter fun m : Fin 72 =>
        e6RootVec m (e6Index 1) = 0 ∧ e6RootVec m (e6Index 0) = e6RootVec m (e6Index 4)) := by
    ext α
    constructor
    · intro hα
      obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
      refine ⟨m, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (tw6SixZx_charVal_eq_zero_iff hp5 hq (isRoot_e6RootVec m)).1 hα.2⟩
    · rintro ⟨m, hm, rfl⟩
      rw [Finset.mem_coe, Finset.mem_filter] at hm
      exact ⟨isRoot_e6RootVec m,
        (tw6SixZx_charVal_eq_zero_iff hp5 hq (isRoot_e6RootVec m)).2 hm.2⟩
  have hsupp : ∀ m : Fin 72, (e6RootVec m (e6Index 1) = 0 ∧
      e6RootVec m (e6Index 0) = e6RootVec m (e6Index 4)) →
      (tw6SixFrameWeyl • e6RootVec m) (e6Index 1) = 0 ∧
        (tw6SixFrameWeyl • e6RootVec m) (e6Index 3) = 0 := by
    rw [tw6SixFrameWeyl]
    decide +kernel
  have hpre : ∀ m : Fin 72, (e6RootVec m (e6Index 1) = 0 ∧ e6RootVec m (e6Index 3) = 0) →
      ∃ m' : Fin 72, (e6RootVec m' (e6Index 1) = 0 ∧
        e6RootVec m' (e6Index 0) = e6RootVec m' (e6Index 4)) ∧
        tw6SixFrameWeyl • e6RootVec m' = e6RootVec m := by
    rw [tw6SixFrameWeyl]
    decide +kernel
  rw [hSx, Set.image_image]
  ext α
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [Finset.mem_coe, Finset.mem_filter] at hm
    have hs := hsupp m hm.2
    refine mem_parabolicRoots_iff.mpr ⟨IsRoot.smul (isRoot_e6RootVec m) tw6SixFrameWeyl,
      fun i hi => ?_⟩
    rw [mem_supportA2A2_compl] at hi
    rcases hi with rfl | rfl
    · exact hs.1
    · exact hs.2
  · intro hα
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
    have h1 : e6RootVec m (e6Index 1) = 0 := hα.2 (e6Index 1) (by
      rw [mem_supportA2A2_compl]; exact Or.inl rfl)
    have h3 : e6RootVec m (e6Index 3) = 0 := hα.2 (e6Index 3) (by
      rw [mem_supportA2A2_compl]; exact Or.inr rfl)
    obtain ⟨m', hm', he⟩ := hpre m ⟨h1, h3⟩
    exact ⟨m', by rw [Finset.mem_coe, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hm'⟩, he⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
