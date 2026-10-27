module

import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.KlingenSylowThree
import CFSG.RankThree.PartTwo.Sec4.Item417Res4ProofSp62
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.TwoReduced

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.AGLEmbedding CFSG.RankThree.PartTwo.Sec4.Item434Kit CFSG.Quasithin
open CFSG.RankThree.PartTwo.Sec4.Res417Four
  (card_W6 factorization_card_H6' t6' wreathFacts_sp6 z6)
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two (H6)

namespace KlingenSylowCentre

theorem card_centerOf_eq_card_center {G : Type*} [Group G] (R : Subgroup G) :
    Nat.card (centerOf R) = Nat.card (Subgroup.center R) := by
  have h : (Subgroup.center R).map R.subtype = centerOf R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)⟩
    · intro hx
      obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.mp hx
      refine ⟨⟨x, hxR⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxc y y.2
  rw [← h]
  exact (Nat.card_congr
    ((Subgroup.center R).equivMapOfInjective _ R.subtype_injective).toEquiv).symm

theorem card_center_map {K H : Type*} [Group K] [Group H] (φ : K ≃* H) (T : Subgroup K) :
    Nat.card (Subgroup.center (T.map φ.toMonoidHom)) = Nat.card (Subgroup.center T) :=
  Nat.card_congr
    (Subgroup.centerCongr (T.equivMapOfInjective φ.toMonoidHom φ.injective)).symm.toEquiv

theorem card_center_eq_of_equiv {p : ℕ} [Fact p.Prime] {K H : Type*} [Group K] [Group H]
    [Finite K] [Finite H] (e : K ≃* H) (T : Sylow p K) (W : Sylow p H) :
    Nat.card (Subgroup.center (T : Subgroup K)) = Nat.card (Subgroup.center (W : Subgroup H)) := by
  obtain ⟨φ, hφ⟩ := KlingenSylowThree.exists_mulEquiv_map_eq e T W
  rw [← card_center_map φ, hφ]

end KlingenSylowCentre

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
