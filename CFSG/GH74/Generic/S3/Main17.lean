module

public import CFSG.GH74.Generic.S3.NbrR
public import CFSG.GH74.Generic.S3.LeavesR
public import CFSG.GH74.Generic.S3.PumpLift
public import CFSG.GH74.Generic.S3.PumpDiag
public import CFSG.GH74.Generic.Lifting
public import CFSG.GH74.GLS.TwoThin.Pumpup
public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.Generic.JMaxDefs
public import CFSG.GH74.Generic.S3.TerminalR
public import CFSG.GH74.Generic.JMax
public import CFSG.GH74.Generic.JMaxShapes
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.Generic.S3.Reflection
public import CFSG.GH74.Generic.S45.LUniLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieDefs
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.Sporadic.Th.Max3.Packet
public import CFSG.Sporadic.Th.Max3.Quotient
public import Certificates.Certificate10091Base

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

theorem false_of_onlyInvX_at (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S3Setup G x K)
    (hN : ∀ (t : StatedLieTag) (p f : ℕ), (t = .PSL ∨ t = .PSU) → p.Prime → p ≠ 2 → 5 ≤ p ^ f →
      LieModel ↥K t 3 p f →
      ∃ (t' : StatedLieTag) (y : G) (Iw Iv Ivw T : Subgroup G),
        Nbhd3 G t t' p f x y Iw Iv Ivw T ∧ imgBar x Iw = K) : False := by
  obtain ⟨hL, hU⟩ := b_S3_prop21_of_griess hGA
  have hR : B_S3_L4Reflection := b_S3_L4Reflection
  obtain ⟨⟨p, f, hp, hp2, hq5, hmodel⟩, -⟩ := hset.shape
  rcases hmodel with hlin | huni
  · obtain ⟨t', v, Iw, Iv, Ivw, P, hnb, himg⟩ := hN .PSL p f (Or.inl rfl) hp hp2 hq5 hlin
    have hconf := hnb.conf2A b_L3_class b_L3_sylow b_L3_noNormalMinus
    obtain ⟨F, hF1, hF2, z, u, Y, hFc, hmod4, hA3, -, -, hY01, hRefl⟩ :=
      hL G hset.global p f v x Iv Iw Ivw P hconf
    have hR1 : B_S3_L4Reflection_lin := hR.1
    exact hR1 G hset.gen4 F hF1 hF2 p f hp hp2 hFc hq5 hmod4 x z u Y hset.inv hA3 hRefl
  · obtain ⟨t', v, Iw, Iv, Ivw, P, hnb, himg⟩ := hN .PSU p f (Or.inr rfl) hp hp2 hq5 huni
    have hconf := hnb.conf2A b_L3_class b_L3_sylow b_L3_noNormalMinus
    obtain ⟨F₂, F, hF₂f, hF₂fin, hFf, hFfin, z, u, Y, hF₂, hF, hmod4, hA3, -, -, hY01, hRefl⟩ :=
      hU G hset.global p f v x Iv Iw Ivw P hconf
    have hR2 : B_S3_L4Reflection_uni := hR.2
    exact hR2 G hset.gen4 F₂ F hF₂f hF₂fin hFf hFfin p f hp hp2 hF₂ hF hq5 hmod4 x z u Y hset.inv hA3
      hRefl

end CFSG.GH74.Generic.S3
