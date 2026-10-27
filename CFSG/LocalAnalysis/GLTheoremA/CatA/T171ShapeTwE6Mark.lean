module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GF2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerBridge
public import CFSG.Goldschmidt.Steps.G310Comp
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial

theorem twE6Marking_holds :
    TwE6Marking := by
  intro G _ _ L J A d b hS hcat
  obtain ⟨-, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_markedModel hS.idiag
  obtain ⟨R, _, I, F, -, -, θ, -, hM⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨i, hi, ⟨e0⟩⟩ := hcat
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating k hk => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie idx =>
    obtain ⟨q, hshape, hidx⟩ := hi
    rw [hidx] at hshape
    obtain ⟨-, hq2, h3q⟩ := hshape
    have hvalid : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by
      rw [← hidx]
      exact idx.2
    haveI hsimpleCat : IsSimpleGroup (TauCeti.CFSGIndex.lie idx).Group := by
      rw [show idx = ⟨.twistedE6 q, hvalid⟩ from Subtype.ext hidx]
      exact (CFSG.HardMathSupport.Timmesfeld.CrossChar.finite_isSimpleGroup_cat_twistedE6
        hvalid).2
    haveI : IsSimpleGroup (PSimple 3 L) := e0.isSimpleGroup
    have hn : 1 ≤ q.exponent := q.exponent_pos
    have h3dvd : 3 ∣ 2 ^ q.exponent + 1 := by
      have h := h3q
      rwa [TauCeti.PrimePower.card_def, hq2] at h
    have hcatTE6 : catalogIs (PSimple 3 L) (S10.isTE6n q.exponent) := by
      refine ⟨.lie idx, ?_, ⟨e0⟩⟩
      rw [show idx = ⟨.twistedE6 q, hvalid⟩ from Subtype.ext hidx]
      exact ⟨hq2, rfl⟩
    obtain ⟨eP⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter 3 L hS.qs
        inferInstance
    have hcatZ : catalogIs (↥L ⧸ Subgroup.center ↥L) (S10.isTE6n q.exponent) :=
      (CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr eP).mp hcatTE6
    have hMZ : MarkedModel lab (↥L ⧸ Subgroup.center ↥L) :=
      MarkedModel.of_mulEquiv θ.symm hM
    have hLieZ : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .twistedE6 0 2
        q.exponent :=
      CFSG.LocalAnalysis.GLTheoremA.T263.lieModel_twE6_of_catalogIs hcatZ
    have hdeterm : lab.tag = .twE6 ∧ lab.n = q.exponent := by
      by_cases h2 : markChar lab = 2
      · exact CFSG.StandardType.NbrInnerMore.eq_of_markedModel_twE6 hn hLieZ hlab h2 hMZ
      · exfalso
        have hodd : CFSG.Blueprint.OddLieType (↥L ⧸ Subgroup.center ↥L) := by
          obtain ⟨tag, rank, m⟩ := lab
          cases tag <;> simp [markChar] at h2
          all_goals first
            | exact ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num,
                CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel
                  (show CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2 from
                    hMZ),
                (show CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 3 2 from
                  hMZ)⟩
            | exact ⟨.PSU, 3, 3, 1, Nat.prime_three, by norm_num,
                CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel
                  (show CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 3 1 from
                    hMZ),
                (show CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 3 1 from
                  hMZ)⟩
        exact CFSG.SeitzReduction.CrossChar.not_oddLieType_of_lieModel_two_of_ne_Tits hLieZ
          (by decide) (by simp) (by simp) (by simp) hodd
    obtain ⟨tag_l, rank_l, n_l⟩ := lab
    obtain ⟨htag, hnlab⟩ := hdeterm
    subst htag
    subst hnlab
    have hrecipe := hraw
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at hrecipe
    dsimp only [CFSG.Assembly.LargeEvenRecipeTwisted] at hrecipe
    obtain ⟨K, hKfield, hKfinite, hKcard, hQ⟩ := hrecipe
    obtain ⟨hsR, -, ⟨θ', hP', -⟩⟩ := hQ
    obtain ⟨-, hBI⟩ := hP'
    exact ⟨q.exponent, K, hKfield, hKfinite, hn, h3dvd, hKcard, hsR, θ', hBI⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
