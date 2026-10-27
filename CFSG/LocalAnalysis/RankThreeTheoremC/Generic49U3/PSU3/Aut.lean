module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutPCard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

theorem u3_aut_pgroup_card {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hK : IsU3Pred p K) (S : Subgroup (MulAut K)) (hS : IsPGroup p S) : Nat.card S ∣ p ^ 3 := by
  obtain ⟨q, hqp, hq1, hv, ⟨e⟩⟩ := hK
  have hd : CFSG.AGLEmbedding.IsUnitaryIndex p (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) :=
    ⟨q, hqp, rfl⟩
  have hfe : (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hq1
  have h := CFSG.AGLEmbedding.kFactUnitaryAutPCard K p
    (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex) (by omega) hd ⟨e⟩ S hS
  rwa [hfe, mul_one, mul_one] at h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
