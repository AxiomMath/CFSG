module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdSmallDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4Perfect
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4PSimple
public import CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4Label
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Rank23
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.CatalogToCover
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.GLTheoremA.S8.Common
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.CatB.StdD4

section Main


theorem stdSubInnerD4At_holds (G : Type) [Group G] [Finite G] : StdSubInnerD4At G := by
  intro B L hL hcat _ hM b hb
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hM
  have hZ : catalogIs (↥L ⧸ Subgroup.center ↥L) CFSG.LocalAnalysis.GLTheoremA.S9.isD4two :=
    psimple_equiv_center_quot 3 L hL hcat
  have hmk := CFSG.StandardType.Canonical.largeEvenRawDatum_markedModel hlab
    (fun R _ I F hq => hq.2.1) hraw
  obtain ⟨R, _, I, F, ⟨-, -, θ, -⟩, hMR⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hmk
  have hlabD := d4Label_of_marked hZ (CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hMR)
  obtain ⟨tg, rk, nn⟩ := lab
  obtain ⟨h1, h2⟩ := hlabD
  change tg = .D at h1
  change rk = 4 at h2
  subst h1 h2
  simp only [CFSG.Assembly.LargeEvenRawDatum, ↓reduceIte] at hraw
  obtain ⟨K, _, _, _, hQK⟩ := hraw
  obtain ⟨-, -, θ', hP⟩ := hQK
  obtain ⟨hBN, hind⟩ := hP
  have hbmem : ∀ l ∈ L, b⁻¹ * l * b ∈ L := by
    intro l hl
    refine (Subgroup.mem_normalizer_iff.1 (hBN hb) (b⁻¹ * l * b)).2 ?_
    rw [show b * (b⁻¹ * l * b) * b⁻¹ = l by group]
    exact hl
  obtain ⟨φ, hφ, hgi⟩ := hind b hb
  obtain ⟨r, rfl⟩ := hφ
  refine inducesInnerMod_of_perfect L hcomm 3 b hbmem θ' r (fun l => ?_)
  have h := hgi l ⟨b⁻¹ * (l : G) * b, hbmem l l.2⟩ rfl
  rw [MulAut.conj_apply] at h
  exact h.symm

end Main

end CFSG.LocalAnalysis.GLTheoremA
