module

public import CFSG.LieType.BorelTits.StronglyEmbedded
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.Assembly.GL83SuzukiModel
public import CFSG.Blueprint.Catalog
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LieType.BorelTits

open CFSG.Open

theorem holds_sz (a : ℕ) (ha : 1 ≤ a) : Holds (Sz a) 2 :=
  holds_two_of_stronglyEmbedded fun Q => (bender_suzuki_borel_full a ha Q).1

theorem suzukiGroup_eq_glaSzGroup (a : ℕ) (K : Type) [Field K] :
    CFSG.Blueprint.suzukiGroup a K = GLASzGroup a K :=
  (CFSG.Assembly.largeEvenSzGroup_eq_suzukiGroup a K).symm

theorem holds_of_suzukiModel {G : Type} [Group G] {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel G p f) : Holds G p := by
  obtain ⟨rfl, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := h
  let e' : G ≃* Sz a := e.trans ((MulEquiv.subgroupCongr (suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
  exact (holds_sz a ha).of_mulEquiv e'.symm

end CFSG.LieType.BorelTits
