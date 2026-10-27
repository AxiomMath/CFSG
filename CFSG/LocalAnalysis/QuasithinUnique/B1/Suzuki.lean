module

public import CFSG.Assembly.GL83SuzukiModel
public import CFSG.LocalAnalysis.QuasithinUnique.B1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalSuzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Models.BenderSuzuki
public import CFSG.Foundations
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.QuasithinUnique.B1

open TauCeti

theorem suzukiGroup_eq_glaSzGroup (a : ℕ) (K : Type) [Field K] :
    CFSG.Blueprint.suzukiGroup a K = CFSG.Open.GLASzGroup a K :=
  (CFSG.Assembly.largeEvenSzGroup_eq_suzukiGroup a K).symm

theorem catalogBridgeFor_suzuki (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid) :
    CatalogBridgeFor (.lie ⟨.suzuki m, hv⟩) := by
  intro G _ _ _ ⟨e⟩
  have hm : 1 ≤ m := by
    have h := ((LieTypeIndex.valid_iff _).1 hv).1
    simpa only [LieTypeIndex.inStandardRange_iff] using h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : CFSG.Theory.Comparator.SzModel m = CFSG.Open.Sz m := CFSG.Models.benderSzModel_eq_sz m
  let toSz : G ≃* CFSG.Open.Sz m :=
    (e.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).trans
      ((MulEquiv.subgroupCongr (hmodel.symm.trans
        (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup m))).symm)
  have hcard : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
    GaloisField.card 2 (2 * m + 1) (by omega)
  let toBP : G ≃* CFSG.Blueprint.suzukiGroup m (GaloisField 2 (2 * m + 1)) :=
    (toSz.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative m hm hcard).symm).trans
      (MulEquiv.subgroupCongr (suzukiGroup_eq_glaSzGroup m (GaloisField 2 (2 * m + 1))).symm)
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨2, 2 * m + 1, rfl, m, hm,
    GaloisField 2 (2 * m + 1), inferInstance, inferInstance, rfl, hcard, ⟨toBP⟩⟩)))))

end CFSG.QuasithinUnique.B1
