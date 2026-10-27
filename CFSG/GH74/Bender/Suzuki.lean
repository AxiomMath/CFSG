module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.LieType.BorelTits.Suzuki
import CFSG.Models.BenderSuzuki
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.Models
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

public section

namespace CFSG.GH74.Bender

theorem szModel_eq_sz (n : ℕ) : CFSG.Theory.Comparator.SzModel n = CFSG.Open.Sz n :=
  CFSG.Models.benderSzModel_eq_sz n

theorem le_twoRank_sz {a : ℕ} (ha : 1 ≤ a) [Finite (CFSG.Open.Sz a)] :
    2 * a + 1 ≤ CFSG.Open.twoRank (CFSG.Open.Sz a) := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 (CFSG.Open.Sz a)))
  obtain ⟨-, -, hpow, hcard, -⟩ := CFSG.Open.bender_suzuki_borel_full a ha Q
  exact CFSG.SectionRank.le_pRank_of_injective (p := 2) Nat.one_lt_two
    (A := Subgroup.center (Q : Subgroup (CFSG.Open.Sz a)))
    (fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x))
    (fun x => Subtype.ext (hpow x x.2)) hcard
    ((Q : Subgroup (CFSG.Open.Sz a)).subtype.comp
      (Subgroup.center (Q : Subgroup (CFSG.Open.Sz a))).subtype)
    (Subtype.val_injective.comp Subtype.val_injective) le_top

theorem suzukiModel_of_mulEquiv_sz {G : Type} [Group G] {a : ℕ} (ha : 1 ≤ a)
    (e : G ≃* CFSG.Open.Sz a) : CFSG.Blueprint.SuzukiModel G 2 (2 * a + 1) := by
  have hcard : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  refine ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl, hcard, ⟨?_⟩⟩
  exact (e.trans (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard).symm).trans
    (MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a (GaloisField 2 (2 * a + 1))).symm)

theorem lieModel_twistedB2_of_mulEquiv_sz_one {G : Type} [Group G] (e : G ≃* CFSG.Open.Sz 1) :
    CFSG.Blueprint.LieModel G .twistedB2 0 2 3 :=
  Or.inr (Or.inr (Or.inr ⟨rfl, rfl, suzukiModel_of_mulEquiv_sz le_rfl e⟩))

end CFSG.GH74.Bender
