module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Over
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.Assembly.OrderReductions.CharacterInflation
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate8026Base

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Open

theorem a312For_of_bender {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (hB : fusionIsBenderGroup X) : A312For X :=
  fun T hT B hB' hne =>
    (CFSG.QuasithinUnique.Unc25G2.A312Sub.over_bender hq hB T hT B hB' hne).elim

theorem u3even : FamU3even := by
  intro X _ _ f hq hf hX
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hcard : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ f)) := e
  exact a312For_of_bender hq
    (Or.inr (Or.inl ⟨f, hf, ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative f hf hcard)⟩⟩))

theorem sz : FamSz := by
  intro X _ _ f hq _ _ hX
  obtain ⟨a, ha, ⟨e⟩⟩ := CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hX
  exact a312For_of_bender hq
    (Or.inr (Or.inr ⟨a, ha, ⟨e.trans (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a).symm⟩⟩))

end CFSG.QuasithinUnique.Vol2Native.A312L
